open Atom
open Types
open Terms

let arrow_tk : atom = fresh (Identifier.mk "arrow" (4, "type constructor"))

let rec translate_type (ty : ftype) : ftype = match ty with
  | TyBoundVar _ -> assert false
  | TyFreeVar a -> TyFreeVar a
  | TyArrow (t1, t2) -> TyCon (arrow_tk, [t1 ; t2])
  | TyForall tc -> let a = fresh (Identifier.mk "dummy" (1, "type")) in
    TyForall (abstract a (translate_type (fill tc (TyFreeVar a))))
  | TyCon (a, l) -> TyCon (a, List.map translate_type l)
  | TyTuple l -> TyTuple (List.map translate_type l)
  | TyWhere (tl, tr, t) -> TyWhere (translate_type tl, translate_type tr, translate_type t)

(* let arrow_sch : ftype = *)
(*   let a = fresh (Identifier.mk "dummy" (1, "type")) in *)
(*   let b = fresh (Identifier.mk "dummy" (1, "type")) in *)
(*   TyForall (abstract a ( *)
(*       TyForall (abstract b ( *)
(*           TyArrow (TyTuple [TyFreeVar a ; TyFreeVar b], *)
(*                    TyCon (arrow_tk, [TyFreeVar a ; TyFreeVar b])))))) *)

(* let arrow_k : atom = fresh (Identifier.mk "Arrow" (3, "data constructor")) *)

let translate (Prog (t_table, dc_table, term) : program) =
  let rec traverse t = match t with
    | TeVar x -> TeVar x
    | TeAbs (x, t1, e, fun_info) -> failwith "TODO"
    | TeApp (f, e, app_info) -> failwith "TODO"
    | TeLet (x, e1, e2) -> TeLet (x, traverse e1, traverse e2)
    | TeFix (x, t, e) -> TeFix (x, translate_type t, traverse e)
    | TeTyAbs (alpha, e) -> TeTyAbs (alpha, traverse e)
    | TeTyApp (e, t) -> TeTyApp (traverse e, translate_type t)
    | TeData (k, tys, terms) -> TeData (k, List.map translate_type tys, List.map traverse terms)
    | TeTyAnnot (e, t) -> TeTyAnnot (traverse e, translate_type t)
    | TeMatch (e, t2, clauses) -> failwith "TODO"
    | TeLoc (loc, e) -> TeLoc (loc, traverse e)
  in
  let term' = traverse term in
  Prog (t_table, dc_table, term')
