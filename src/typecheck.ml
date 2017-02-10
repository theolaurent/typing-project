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
  | TeVar x -> lookup x tenv
  (* | TeAbs of *)
  (*     atom *                      (\* function parameter *\) *)
  (*     ftype *                     (\* function parameter's type *\) *)
  (*     fterm *                     (\* function body *\) *)
  (*     function_info option ref    (\* information recorded by the type-checker *\) *)
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
  (* | TeFix of atom * ftype * fterm *)
  (*     (\* fix x : T = t *\) *)
  (* TODO: introduce new variable + equation ? *)
  (* | TeTyAbs of atom * fterm *)
  (*     (\* fun [ a ] = t *\) *)
  (* TODO: what about type variables that are not free in tenv / hyps ? *)
  | TeTyApp (e, t) ->
    begin match infer p xenv loc hyps tenv e with
      | TyForall tc -> fill tc t
      | _ -> failwith "TODO:handle type errors"
    end
  (* | TeTyApp of fterm * ftype *)
  (*     (\* t [ T ] *\) *)
  (* | TeData of atom * ftype list * fterm list *)
  (*     (\* K [ T ... T ] { t; ...; t } *\) *)
  | TeTyAnnot (e, t) ->
    let () = check p xenv hyps tenv e t in
    t
  (* | TeMatch of fterm * ftype * clause list *)
  (*     (\* match t return T with clause ... clause end *\) *)
  | TeLoc (_, e) -> infer p xenv loc hyps tenv e
  | _ ->
     failwith "TYPECHECKING IS NOT IMPLEMENTED YET!" (* do something here! *)

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

      (* let inferred = infer p xenv loc hyps tenv term in *)
      failwith "CHECK IS NOT COMPLETE YET!" (* do something here! *)

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
