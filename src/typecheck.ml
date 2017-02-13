open Printf
open Atom
open Types
open Equations
open Terms
open Symbols
open Print
open Typerr

(* ------------------------------------------------------------------------- *)

(* Specification of the type-checker. *)

(* The core of the typechecker is made up of two mutually recursive
   functions. [infer] infers a type and returns it; [check] infers a
   type, checks that it is equal to the expected type, and returns
   nothing. *)

(* The type [ty] that is produced by [infer] should be correct, that
   is, the typing judgement [hyps, tenv |- term : ty] should hold.
   Furthermore, it should be unique, that is, for every type [ty']
   such that the judgement [hyps, tenv |- term : ty'] holds, the
   hypotheses [hyps] entail the equation [ty = ty']. *)

(* The function [check] should be correct, that is, if it succeeds,
   then the typing judgement [hyps, tenv |- term : expected] holds. *)

(* ------------------------------------------------------------------------- *)

(* A completeness issue. *)

(* Ideally, the functions [infer] and [check] should be complete, that
   is, if they fail, then the term is ill-typed according to the
   typing rules in Pottier and Gauthier's paper. However, with the
   tools that we provide, this goal is difficult to meet, for the
   following reason.

   Consider, for instance, a function application [x1 x2]. We can use
   [infer] to obtain the types of [x1] and [x2], say, [ty1] and
   [ty2]. Then, we must check that, FOR SOME TYPE [ty], THE HYPOTHESES
   [hyps] ENTAIL THAT the type [ty1] is equal to the function type
   [TyArrow ty2 ty].

   This is a bit problematic. Of course, if the hypotheses [hyps] are
   empty, this is easy: it is just a syntactic check. If somehow the
   type [ty] was known, this would be easy as well: it would be an
   entailment check, for which we provide a decision procedure.
   However, in the general case, we need to solve a more difficult
   problem -- entailment with unknowns -- for which (out of laziness,
   perhaps) we haven't provided an algorithm.

   As a result, we suggest that you stick with a simple syntactic
   check. Your type-checker will thus be incomplete. That will not be
   a real problem: the user can work around it by adding an explicit
   type annotation to convert [ty1] into the desired function type
   [TyArrow ty1 ty]. The sample file [test/good/conversion.f]
   illustrates this.

   If you follow our suggestion and develop an incomplete
   type-checker, then you may run into a problem when implementing
   defunctionalization. The program produced by your
   defunctionalization phase may be well-typed, yet may be rejected by
   your type-checker, for the above reason. If this happens, you will
   have to work around the problem by having your defunctionalization
   algorithm produce explicit type annotations where appropriate. *)

(* ------------------------------------------------------------------------- *)


(* TODO: move the following functions to the appropriate file? *)

(* Instantiate a type scheme with a list of types *)
(* TODO: fold_left or fold_right? Test with lists! *)
let instanciate scheme ty_list = List.fold_left (fun tsch t -> match tsch with
    | TyForall tc -> fill tc t
    | _ -> failwith "TODO: handle type errors"
  ) scheme ty_list

(* Extract the equations in head position *)
let head_equations (ty : ftype) : equations * ftype =
  let rec loop ty acc = match ty with
    | TyWhere (t, l, r) -> loop t ((l,r) :: acc)
    | _ -> (acc, ty)
  in loop ty []

(* The type-checker. *)

let rec infer              (* [infer] expects... *)
    (p : program)          (* a program, which provides information about type & data constructors; *)
    (xenv : Export.env)    (* a pretty-printer environment, for printing types; *)
    (loc : Error.location) (* a location, for reporting errors; *)
    (hyps : equations)     (* a set of equality assumptions *)
    (tenv : tenv)          (* a typing environment; *)
    (term : fterm)         (* a term; *)
    : ftype =              (* ...and returns a type. *)

  match term with
  (* TODO: add comments *)
  | TeVar x -> lookup x tenv
  | TeAbs (x, t, b, fun_info) ->
    let t' = infer p xenv loc hyps (bind x t tenv) b in
    (* TODO: I do not restrict tenv, is it inefficient? *)
    let res = TyArrow (t, t') in
    let () = fun_info := Some { hyps = hyps ; tenv = tenv ; fty = res } in
    res
  | TeApp (f, e, app_info) ->
    begin match infer p xenv loc hyps tenv f with
      | TyArrow (t1, t2) ->
        let () = check p xenv hyps tenv e t1 in
        let () = app_info := Some { domain = t1 ; codomain = t2 } in
        t2
      | _ -> failwith "TODO: handle type errors"
    end
  | TeLet (x, e, b) ->
    let t = infer p xenv loc hyps tenv e in
    infer p xenv loc hyps (bind x t tenv) b
  | TeFix (x, t, b) ->
    let () = check p xenv hyps (bind x t tenv) b t in
    t
  | TeTyAbs (a, e) ->
    (* thanks to the internalization mechanism, we may we assume that *)
    (* a is free in tenv and hyps                                     *)
    let t = infer p xenv loc hyps tenv e in
    TyForall (abstract a t)
  | TeTyApp (e, t) ->
    begin match infer p xenv loc hyps tenv e with
      | TyForall tc -> fill tc t
      | _ -> failwith "TODO: handle type errors"
    end
  | TeData (k, tys, terms) ->
    (* Instantiate the type scheme and extract equations *)
    let (equs, t) = head_equations (instanciate (type_scheme p k) tys) in
    let () = if not (entailment hyps equs) then failwith "TODO: handle type errors" in
    (* Check the type of constructor itself *)
    begin match t with
      | TyArrow (TyTuple tl, (TyCon (tk, _) as tres)) ->
        let () = try List.fold_left2 (fun () t e -> check p xenv hyps tenv e t) () tl terms
          with Invalid_argument _ -> failwith "TODO: handle type errors" in
        let () = if not (Atom.equal (type_constructor p k) tk)
                 then failwith "TODO: handle type errors" in
        tres
      | _ -> failwith "TODO: handle type errors"
    end
  | TeTyAnnot (e, t) ->
    let () = check p xenv hyps tenv e t in
    t
  | TeMatch (e, rt, clauses) ->
    begin match infer p xenv loc hyps tenv e with
      | TyCon (tk, tys) ->
        (* An auxiliary function to type check the clause *)
        let check_clause (Clause (PatData (newloc, k, al, xl), e)) =
          let (equs, t) = head_equations (instanciate (type_scheme p k) (List.map (fun a -> TyFreeVar a) al)) in
          begin match t with
            | TyArrow (TyTuple tl, TyCon (tk', tys')) ->
              let nhyps = try
                  List.rev_append hyps (List.rev_append equs (List.combine tys tys'))
                with Invalid_argument _ -> failwith "TODO: handle type errors"
              in
              let () = if inconsistent nhyps then failwith "TODO: handle type errors" in
              let () = if not (Atom.equal tk tk') then failwith "TODO: handle type errors" in
              let ntenv = try binds (List.combine xl tl) tenv
                with Invalid_argument _ -> failwith "TODO: handle type errors"
              in
              check p xenv nhyps ntenv e rt
            | _ -> failwith "TODO: handle type errors"
          end
        in
        (* Check all the clauses and return the provided return type *)
        let () = List.fold_left (fun () c -> check_clause c) () clauses in
        rt
      | _ -> failwith "TODO: handle type errors"
    end
  | TeLoc (newloc, e) -> infer p xenv newloc hyps tenv e

and check                  (* [check] expects... *)
    (p : program)          (* a program, which provides information about type & data constructors; *)
    (xenv : Export.env)    (* a pretty-printer environment, for printing types; *)
    (hyps : equations)     (* a set of equality assumptions *)
    (tenv : tenv)          (* a typing environment; *)
    (term : fterm)         (* a term; *)
    (expected : ftype)     (* an expected type; *)
    : unit =               (* ...and returns nothing. *)

  (* We bet that the term begins with a [TeLoc] constructor. This should be
     true because the parser inserts one such constructor between every two
     ordinary nodes. In fact, this is not quite true, because the parser
     sometimes expands syntactic sugar without creating intermediate [TeLoc]
     nodes. If you invoke [check] in reasonable places, it should just work. *)

  match term with
  | TeLoc (loc, term) ->
      let inferred = infer p xenv loc hyps tenv term in
      (* TODO: what about equations compatibility? *)
      if not (equal inferred expected) then
        failwith "TODO: handle type errors"

  | _ ->
      (* out of luck! *)
      assert false

(* ------------------------------------------------------------------------- *)

(* A complete program is typechecked within empty environments. *)

let run (Prog (tctable, dctable, term) as p : program) =
  let xenv = Export.empty
  and loc = Error.dummy
  and hyps = []
  and tenv = Types.empty in
  let xenv = AtomMap.fold (fun tc _ xenv -> Export.bind xenv tc) tctable xenv in
  let xenv = AtomMap.fold (fun dc _ xenv -> Export.bind xenv dc) dctable xenv in
  xenv, infer p xenv loc hyps tenv term
