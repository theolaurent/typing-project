open Atom
open Types
open Terms

(* TODO: comment code *)

let arrow_type (a1 : ftype) (a2 : ftype) =
  let arrow_tk : atom = fresh (Identifier.mk "arrow" (4, "type constructor")) in
  TyCon (arrow_tk, [a1 ; a2])

let rec translate_type (ty : ftype) : ftype = match ty with
  | TyBoundVar _ -> assert false
  | TyFreeVar a -> TyFreeVar a
  | TyArrow (t1, t2) -> arrow_type t1 t2
  | TyForall tc -> let a = fresh (Identifier.mk "dummy" (1, "type")) in
    TyForall (abstract a (translate_type (fill tc (TyFreeVar a))))
  | TyCon (a, l) -> TyCon (a, List.map translate_type l)
  | TyTuple l -> TyTuple (List.map translate_type l)
  | TyWhere (tl, tr, t) -> TyWhere (translate_type tl, translate_type tr, translate_type t)


let apply_type : ftype =
  let a1 = fresh (Identifier.mk "dummy" (1, "type")) in
  let a2 = fresh (Identifier.mk "dummy" (1, "type")) in
  TyForall (abstract a1 (
      TyForall (abstract a2 (
          TyArrow (arrow_type (TyFreeVar a1) (TyFreeVar a2),
                   TyArrow (TyFreeVar a1, TyFreeVar a2))))))

let build_apply (clauses : clause list) : fterm =
  let a1 = fresh (Identifier.mk "a1" (1, "type")) in
  let a2 = fresh (Identifier.mk "a2" (1, "type")) in
  let apply_rec : atom = fresh (Identifier.mk "apply" (0, "term")) in
  let apply_f   : atom = fresh (Identifier.mk "f"     (0, "term")) in
  let apply_arg : atom = fresh (Identifier.mk "arg"   (0, "term")) in
  TeFix (apply_rec, apply_type,
         TeTyAbs (a1,
                  TeTyAbs (a2,
                           TeAbs (apply_f,
                                  arrow_type (TyFreeVar a1) (TyFreeVar a2),
                                  TeAbs (apply_arg,
                                         TyFreeVar a1,
                                         TeMatch (TeVar apply_f, TyFreeVar a2, clauses),
                                         ref None),
                                  ref None))))

let apply_id : fterm = TeVar (fresh (Identifier.mk "apply" (0, "term")))

let mk_closure x m = failwith "TODO"

let translate (Prog (t_table, dc_table, term) : program) =
  let closures = Stack.create () in
  let rec traverse t = match t with
    | TeVar x -> TeVar x
    | TeAbs (x, t1, e, fun_info) ->
      let (hyps, tenv, t1, t2) = match !fun_info with
        | None -> failwith "You need to call the typechecker before defunctionalization"
        | Some r -> begin match r.fty with
            | TyArrow (t1, t2) -> (r.hyps, r.tenv, t1, t2)
            | _ -> assert false
            end
      in
      let m : atom = fresh (Identifier.mk "m" (3, "data constructor")) in
      let () = Stack.push (mk_closure e m) closures in
      TeData (m, failwith "TODO", failwith "TODO")
    | TeApp (e1, e2, app_info) ->
      let (t1, t2) = match !app_info with
        | None -> failwith "You need to call the typechecker before defunctionalization"
        | Some r -> (r.domain, r.codomain)
      in
      TeApp (TeApp (TeTyApp (TeTyApp (apply_id, t1), t2),
                    traverse e1, ref None),
             traverse e2, ref None)
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
  let term' = traverse term in
  Prog (t_table, dc_table, term')
