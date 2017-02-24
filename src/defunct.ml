open Atom
open Types
open Terms
open Symbols


(* util function : compute free type variables of a term *)
(* TODO: put in a different file?                        *)
let rec ftv_term (term : fterm) : AtomSet.t = match term with
  | TeVar _ -> AtomSet.empty
  | TeAbs (_, t, term, _)
  | TeTyAnnot (term, t)
  | TeTyApp (term, t)
  | TeFix (_, t, term) -> AtomSet.union (ftv t) (ftv_term term)
  | TeApp (term1, term2, _)
  | TeLet (_, term1, term2) -> AtomSet.union (ftv_term term1) (ftv_term term2)
  | TeTyAbs (a, term) -> AtomSet.remove a (ftv_term term)
  | TeLoc (_, term) -> ftv_term term
  | TeData (_, types, fields) ->
    let ftv_fields = List.fold_left AtomSet.union AtomSet.empty (List.map ftv_term fields) in
    List.fold_left AtomSet.union ftv_fields (List.map ftv types)
  | TeMatch (term, t, clauses) ->
    List.fold_left AtomSet.union (AtomSet.union (ftv t) (ftv_term term))
      (List.map ftv_clause clauses)
and ftv_clause (Clause (PatData (_, _, tyvars, _), term) : clause) : AtomSet.t =
  List.fold_left (fun res a -> AtomSet.remove a res) (ftv_term term) tyvars




(* the new arrow type constructor *)
let arrow_tk : atom = fresh (Identifier.mk "arrow" (4, "type constructor"))
let arrow_type (a1 : ftype) (a2 : ftype) =
  TyCon (arrow_tk, [a1 ; a2])

(* type translation, pretty straightforward *)
let rec translate_type (ty : ftype) : ftype = match ty with
  | TyBoundVar _ -> assert false
  | TyFreeVar a -> TyFreeVar a
  | TyArrow (t1, t2) -> arrow_type (translate_type t1) (translate_type t2)
  | TyForall tc -> let a = fresh (Identifier.mk "dummy" (1, "type")) in
    TyForall (abstract a (translate_type (fill tc (TyFreeVar a))))
  | TyCon (a, l) -> TyCon (a, List.map translate_type l)
  | TyTuple l -> TyTuple (List.map translate_type l)
  | TyWhere (t, l, r) -> TyWhere (translate_type t, translate_type l, translate_type r)


(* type scheme translation, needed for the dc table *)
(* the only tricky thing is that you have to preserve the main arrow *)
let rec translate_typescheme (ty : ftype) : ftype = match ty with
  | TyForall tc -> let a = fresh (Identifier.mk "dummy" (1, "type")) in
    TyForall (abstract a (translate_typescheme (fill tc (TyFreeVar a))))
  | TyWhere (t, l, r) -> TyWhere (translate_typescheme t, translate_type l, translate_type r)
  | TyArrow (TyTuple args, TyCon (tk, results)) ->
    TyArrow (TyTuple (List.map translate_type args), TyCon (tk, List.map translate_type results))
  | _ -> failwith "This is not a type scheme"

(* a type for the apply function *)
let apply_type : ftype =
  let a1 = fresh (Identifier.mk "dummy" (1, "type")) in
  let a2 = fresh (Identifier.mk "dummy" (1, "type")) in
  TyForall (abstract a1 (
      TyForall (abstract a2 (
          TyArrow (arrow_type (TyFreeVar a1) (TyFreeVar a2),
                   TyArrow (TyFreeVar a1, TyFreeVar a2))))))

(* the identifier for calling the apply function *)
let apply_id : atom = fresh (Identifier.mk "apply" (0, "term"))
(* and for using the argument inside clauses *)
let arg_id : atom = fresh (Identifier.mk "arg"   (0, "term"))

(* the apply function's body           *)
(* take the clause list as an argument *)
let build_apply (clauses : clause list) : fterm =
  let a1 = fresh (Identifier.mk "a1" (1, "type")) in
  let a2 = fresh (Identifier.mk "a2" (1, "type")) in
  let f   : atom = fresh (Identifier.mk "f"     (0, "term")) in
  TeFix (apply_id, apply_type,
         TeTyAbs (a1,
                  TeTyAbs (a2,
                           TeAbs (f,
                                  arrow_type (TyFreeVar a1) (TyFreeVar a2),
                                  TeAbs (arg_id,
                                         TyFreeVar a1,
                                         TeMatch (TeVar f, TyFreeVar a2, clauses),
                                         ref None),
                                  ref None))))


(* the translation itself *)
let translate (Prog (t_table, dc_table, term) : program) =
  (* use stack to store new type schemes and clauses *)
  let schemes = Stack.create () in
  let clauses = Stack.create () in
  (* the main term translation *)
  let rec traverse t = match t with
    (* lambda abstraction *)
    | TeAbs (x, _, e, fun_info) ->
      (* get the function information from the typechecker *)
      let (hyps, tenv, t1, t2) = match !fun_info with
        | None -> failwith "You need to call the typechecker before defunctionalization"
        | Some r -> begin match r.fty with
            | TyArrow (t1, t2) ->
              (r.hyps, r.tenv, t1, t2)
            | _ -> assert false
            end
      in
      (* create a fresh id for the lambda *)
      let m : atom = fresh (Identifier.mk "M" (3, "data constructor")) in
      (* compute free term variables and their types *)
      let free_vars = AtomSet.elements (fv t) in
      let free_vars_types = List.map (fun a -> lookup a tenv) free_vars in
      (* compute all free type variables *)
      let free_type_vars =
        let ftv_tenv = List.map ftv free_vars_types in
        let ftv_hyps = List.map (fun (l, r) -> AtomSet.union (ftv l) (ftv r)) hyps in
        let full_set = List.fold_left AtomSet.union AtomSet.empty
            (ftv_term t :: ftv t1 :: ftv t2 :: (List.rev_append ftv_tenv ftv_hyps)) in
        AtomSet.elements full_set

      in
      (* build its type scheme and store it *)
      let sch = (foralls free_type_vars
                   (wheres (TyArrow (TyTuple (List.map translate_type free_vars_types),
                                     arrow_type (translate_type t1) (translate_type t2)))
                      (List.map (fun (l,r) -> (translate_type l, translate_type r)) hyps))) in
      let () = Stack.push (m, sch) schemes in
      (* build the corresponding clause and store it *)
      let c = Clause (PatData (Error.dummy, m, free_type_vars, free_vars),
                      TeLet (x, TeTyAnnot (TeVar arg_id, translate_type t1), traverse e)) in
      let () = Stack.push c clauses in
      (* return the data constructor *)
      TeData (m,
              List.map (fun a -> TyFreeVar a) free_type_vars,
              List.map (fun x -> TeVar x) free_vars)
    (* function application *)
    | TeApp (e1, e2, app_info) ->
      (* get the application information from the typechecker *)
      let (t1, t2) = match !app_info with
        | None -> failwith "You need to call the typechecker before defunctionalization"
        | Some r -> (r.domain, r.codomain)
      in
      (* replace with a call to apply *)
      TeApp (TeApp (TeTyApp (TeTyApp (TeVar apply_id, (translate_type t1)), (translate_type t2)),
                    traverse e1, ref None),
             traverse e2, ref None)
    (* the rest is straightforward *)
    | TeVar x -> TeVar x
    | TeLet (x, e1, e2) -> TeLet (x, traverse e1, traverse e2)
    | TeFix (x, t, e) -> TeFix (x, translate_type t, traverse e)
    | TeTyAbs (alpha, e) -> TeTyAbs (alpha, traverse e)
    | TeTyApp (e, t) -> TeTyApp (traverse e, translate_type t)
    | TeData (k, tys, terms) -> TeData (k, List.map translate_type tys, List.map traverse terms)
    | TeTyAnnot (e, t) -> TeTyAnnot (traverse e, translate_type t)
    | TeMatch (e, t2, clauses) ->
      TeMatch (traverse e, translate_type t2,
               List.map (fun (Clause (p, e)) -> Clause (p, traverse e)) clauses)
    | TeLoc (loc, e) -> TeLoc (loc, traverse e)
  in
  (* translate the body of the program *)
  let traversed = traverse term in
  (* add the arrow type constructor *)
  let t_table' = AtomMap.add arrow_tk 2 t_table in
  (* translate type schemes and add the new ones *)
  let dc_table' = Stack.fold (fun res (m, sch) -> AtomMap.add m sch res)
      (AtomMap.map translate_typescheme dc_table) schemes in
  (* build the new program *)
  let term' = TeLet (apply_id,
                     build_apply (Stack.fold (fun res x -> x :: res) [] clauses),
                     traversed) in
  Prog (t_table', dc_table', term')
