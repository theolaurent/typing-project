open Atom
open Types
open Terms
open Symbols

(* the new arrow type constructor *)
let arrow_tk : atom = fresh (Identifier.mk "arrow" (4, "type constructor"))
let arrow_type (a1 : ftype) (a2 : ftype) =
  TyCon (arrow_tk, [a1 ; a2])

(* type translation, pretty straightforward *)
let rec translate_type (ty : ftype) : ftype = match ty with
  | TyBoundVar _ -> assert false
  | TyFreeVar a -> TyFreeVar a
  | TyArrow (t1, t2) -> arrow_type t1 t2
  | TyForall tc -> let a = fresh (Identifier.mk "dummy" (1, "type")) in
    TyForall (abstract a (translate_type (fill tc (TyFreeVar a))))
  | TyCon (a, l) -> TyCon (a, List.map translate_type l)
  | TyTuple l -> TyTuple (List.map translate_type l)
  | TyWhere (tl, tr, t) -> TyWhere (translate_type tl, translate_type tr, translate_type t)


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
  let schemes = Stack.create () in
  let clauses = Stack.create () in
  let rec traverse t = match t with
    (* lambda abstraction *)
    | TeAbs (x, _, e, fun_info) ->
      (* get the function information from the typechecker *)
      let (hyps, tenv, t1, t2) = match !fun_info with
        | None -> failwith "You need to call the typechecker before defunctionalization"
        | Some r -> begin match r.fty with
            | TyArrow (t1, t2) -> (r.hyps, r.tenv, t1, t2)
            | _ -> assert false
            end
      in
      (* create a fresh id for the lambda *)
      let m : atom = fresh (Identifier.mk "m" (3, "data constructor")) in
      (* build its type scheme and store it *)
      let free_type_vars = [] in
      let free_vars = AtomSet.fold (fun h t -> h :: t) (fv t) [] in
      let free_vars_types = List.map (fun a -> lookup a tenv) free_vars in
      let sch = (foralls free_type_vars
                   (wheres (TyArrow (TyTuple free_vars_types,
                                     arrow_type (translate_type t1) (translate_type t2)))
                      hyps)) in
      let () = Stack.push (m, sch) schemes in
      (* build its corresponding clause and store it *)
      let c = Clause (PatData (Error.dummy, m, free_type_vars, free_vars),
                      TeLet (x, TeVar arg_id, traverse e)) in
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
      TeApp (TeApp (TeTyApp (TeTyApp (TeVar apply_id, t1), t2),
                    traverse e1, ref None),
             traverse e2, ref None)
    (* the rest is just traversal *)
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
  let t_table' = AtomMap.add arrow_tk 2 t_table in
  let dc_table' = Stack.fold (fun res (m, sch) -> AtomMap.add m sch res) dc_table schemes in
  let term' = TeLet (apply_id,
                     build_apply (Stack.fold (fun res x -> x :: res) [] clauses),
                     traversed) in
  let res = Prog (t_table', dc_table', term') in
  let xenv, ty = Typecheck.run res in
  res
