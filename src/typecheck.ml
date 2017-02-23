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
(* TODO: update xenv when necessary and handle errors properly? *)

(* Instantiate a type scheme with a list of types *)
let instanciate xenv loc scheme ty_list = List.fold_left (fun tsch t -> match tsch with
    | TyForall tc -> fill tc t
    | _ -> expected_form xenv loc "forall _ . _" t
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
  (* x *)
  | TeVar x -> lookup x tenv
  (* fun x : t1 = e *)
  | TeAbs (x, t1, e, fun_info) ->
    (* infer return type *)
    let t2 = infer p xenv loc hyps (bind x t1 tenv) e in
    let res = TyArrow (t1, t2) in
    let () = fun_info := Some { hyps = hyps ; tenv = tenv ; fty = res } in
    res
  (* f e *)
  | TeApp (f, e, app_info) ->
    (* match the applied type against the arrow pattern *)
    begin match infer p xenv loc hyps tenv f with
      | TyArrow (t1, t2) ->
        (* and check the argument type *)
        let () = check p xenv hyps tenv e t1 in
        let () = app_info := Some { domain = t1 ; codomain = t2 } in
        t2
      | t -> expected_form xenv loc "_ -> _" t
    end
  (* let x = e1 in e2 *)
  | TeLet (x, e1, e2) ->
    (* infer type of the bound expression *)
    let t1 = infer p xenv loc hyps tenv e1 in
    (* and add it to the environment to infer the body type *)
    infer p xenv loc hyps (bind x t1 tenv) e2
  (* fix x : t = e *)
  | TeFix (x, t, e) ->
    (* check the type of the fixpoint, adding itself to the environment *)
    let () = check p xenv hyps (bind x t tenv) e t in
    t
  (* fun [ alpha ] = e *)
  | TeTyAbs (alpha, e) ->
    (* thanks to the internalization mechanism, we may we assume that *)
    (* a is free in tenv and hyps.                                    *)
    (* infer the type of the body and abstract the type variable *)
    let t = infer p (Export.bind xenv alpha) loc hyps tenv e in
    TyForall (abstract alpha t)
  (* e [ t ] *)
  | TeTyApp (e, t) ->
    (* match the expression type against the forall pattern *)
    begin match infer p xenv loc hyps tenv e with
      | TyForall tc -> fill tc t
      | t ->
        expected_form xenv loc "forall _ . _" t
    end
  (* k [ ty ... ty ] { term; ...; term } *)
  | TeData (k, tys, terms) ->
    (* instantiate the type scheme and extract equations *)
    let (equs, t) = head_equations (instanciate xenv loc (type_scheme p k) tys) in
    let () = if not (entailment hyps equs)
             then unsatisfied_equations xenv loc hyps equs in
    (* match the type of the constructor itself *)
    begin match t with
      | TyArrow (TyTuple arg_tys, (TyCon (tk, _) as tres)) ->
        (* check for the arguments to have the right types *)
        let () = try List.iter2 (fun t e -> check p xenv hyps tenv e t) arg_tys terms
          with Invalid_argument _ ->
            Error.error [loc] "TODO: handle arity mismatch in the case of data constructors"in
        (* and check the constructor *)
        let () = if not (Atom.equal (type_constructor p k) tk)
                 then Error.error [loc] "TODO: handle constructor mismatch" in
        tres
      | t -> expected_form xenv loc "{ _ ; ... _ } -> k _ ... _" t
    end
  (* (e : t) *)
  | TeTyAnnot (e, t) ->
    let () = check p xenv hyps tenv e t in
    t
  (* match e return t2 with clause ... clause end *)
  | TeMatch (e, t2, clauses) ->
    (* infer the type of the expression and check each clause *)
    let t1 = infer p xenv loc hyps tenv e in
    begin match t1 with
      | TyCon (tk, _) ->
        (* exhaustiveness/redudancy check *)
        let () = AtomSet.iter (fun a ->
            match List.filter (fun (Clause (PatData (_, k, _, _), _)) -> Atom.equal a k) clauses with
            | [] ->
              (* check_inconsisten_clause *)
              if not (check_inconsistent p xenv loc hyps a t1)
              then missing_clause xenv hyps loc a
            | [ c ] -> ()
            | _ :: c2 :: _ -> let (Clause (PatData (loc, _, _, _), _)) = c2 in
              redundant_clause loc
          ) (data_constructors p tk) in
        let () = List.iter (fun c -> check_clause p xenv hyps tenv c t1 t2) clauses in
        t2
      | t -> expected_form xenv loc "k _ ... _" t
    end
  (* e *)
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
      if not (entailment hyps [(inferred, expected)]) then
        mismatch xenv loc hyps expected inferred
        (* TODO: is "unsatisfied_equation xenv loc hyps inferred expected" better?*)
  | _ ->
      (* out of luck! *)
      assert false

and check_clause          (* [check_clause] expects... *)
    (p      : program)    (* a program, which provides information about type & data constructors; *)
    (xenv   : Export.env) (* a pretty-printer environment, for printing types; *)
    (hyps   : equations)  (* a set of equality assumptions *)
    (tenv   : tenv)       (* a typing environment; *)
    (clause : clause)     (* a clause; *)
    (arg    : ftype)      (* an argument type; *)
    (ret    : ftype)      (* an return type; *)
    : unit =              (* ...and returns nothing. *)

  (* k [ alpha ... alpha ] { id; ...; id } -> e *)
  let (Clause (PatData (loc, k, alphas, ids), e)) = clause in
  match arg with
  | TyCon (tk, t2s) ->
    let (equs, t) = head_equations (instanciate xenv loc (type_scheme p k)
                                   (List.map (fun a -> TyFreeVar a) alphas)) in
    begin match t with
      | TyArrow (TyTuple ts, TyCon (tk', t1s)) ->
        let () = if not (Atom.equal tk tk')
                 then typecon_mismatch xenv loc k tk tk' in
        let nhyps = try
            List.rev_append hyps (List.rev_append equs (List.combine t1s t2s))
          with Invalid_argument _ -> Error.error [loc] "TODO: handle arity mismatch in the case of clauses (1)"
        in
        let () = if inconsistent nhyps then inaccessible_clause loc in
        let ntenv = try binds (List.combine ids ts) tenv
          with Invalid_argument _ -> Error.error [loc] "TODO: handle arity mismatch in the case of clauses (2)"
        in
        check p (Export.sbind xenv alphas) nhyps ntenv e ret
      | t -> expected_form xenv loc "{ _ ; ... _ } -> k _ ... _" t
    end
  | t -> expected_form xenv loc "k _ ... _" t
and check_inconsistent    (* [check_clause] expects... *)
    (p      : program)    (* a program, which provides information about type & data constructors; *)
    (xenv   : Export.env) (* a pretty-printer environment, for printing types; *)
    (loc    : Error.location) (* a location, for reporting errors; *)
    (hyps   : equations)  (* a set of equality assumptions *)
    (k      : atom)       (* a data constructor; *)
    (arg    : ftype)      (* an argument type; *)
    : bool =              (* ...and returns true if the clause should not be. *)

  match arg with
  | TyCon (tk, t2s) ->
    let tsch = type_scheme p k in
    let freshes =
      let rec loop n l =
        if n = 0 then l
        else loop (n - 1) (fresh (Identifier.mk "dummy" (1, "type")) :: l)
      in loop (count_foralls tsch) []
    in
    let (equs, t) = head_equations (instanciate xenv loc tsch
                                   (List.map (fun a -> TyFreeVar a) freshes)) in
    begin match t with
      | TyArrow (TyTuple ts, TyCon (tk', t1s)) ->
        let () = if not (Atom.equal tk tk')
                 then Error.error [loc] "TODO: handle type constructor mismatch in the case of clauses" in
        let nhyps = try
            List.rev_append hyps (List.rev_append equs (List.combine t1s t2s))
          with Invalid_argument _ -> Error.error [loc] "TODO: handle arity mismatch in the case of clauses (1)"
        in
        inconsistent nhyps
      | t -> expected_form xenv loc "{ _ ; ... _ } -> k _ ... _" t
    end
  | t -> expected_form xenv loc "k _ ... _" t

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
