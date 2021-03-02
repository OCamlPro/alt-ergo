(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

module E = Expr
module Sy = Symbols

let verb = Options.get_simplify_verbose

let silent (msg : ('a, Format.formatter, unit) format) =
  Format.ifprintf Format.std_formatter msg

let talk (msg : ('a, Format.formatter, unit) format) =
  Format.printf "[Preprocess] ";
  Format.printf msg

let debug (msg : ('a, Format.formatter, unit) format) =
  if verb ()
  then talk msg
  else silent msg

(** 1. Utils *)

(** Values are representations of expressions
    that have been "solved", in the sense that they can
    be reduced to a boolean or a float/int.
type value =
  | Bool of bool
  | Num of Q.t

let (++) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> Bool (b1 || b2)
  | Num n1, Num n2 -> Num (Q.add n1 n2)
  | _,_ -> assert false

let (--) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> Num (Q.sub n1 n2)
  | _,_ -> assert false

let ( ** ) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> Bool (b1 && b2)
  | Num n1, Num n2 -> Num (Q.mul n1 n2)
  | _,_ -> assert false

let (|=) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> b1 == b2
  | Num n1, Num n2 -> (Stdlib.(=)) n1 n2
  | _,_ -> false

let (|<>) v1 v2 = not (v1 |= v2)

let (|<) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> n1 < n2
  | _,_ -> assert false

let (|<=) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> n1 <= n2
  | _,_ -> assert false

let (|>) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> n1 > n2
  | _,_ -> assert false

let (|>=) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> n1 >= n2
  | _,_ -> assert false


let pp_val fmt v =
  match v with
    Bool b -> Format.fprintf fmt "Bool %b" b
  | Num n -> Format.fprintf fmt "Num %a" Q.pp_print n*)

(** A simplified formula/expr/... type.
    The diff field is set to false if the operation did not change the
    input.
    As queries may provide explanations, the third field correspond to the
    explanation behind the simplification. *)

(** Same as List.fold_left, but f returns
    a tuple (acc, stop) where stop is a boolean
    stating that the loop has to stop. *)
let fold_left_stop
    (f : 'a -> 'b -> ('a * bool))
    (acc : 'a)
    (l : 'b list) : 'a
  =
  let rec __fold acc l =
    match l with
      [] -> acc
    | hd :: tl ->
      let acc, stop = f acc hd in
      if stop then acc
      else __fold acc tl
  in __fold acc l

type ('expr, 'abs_val) simp = {
    exp : 'expr;
    diff : bool;
    v : 'abs_val
  }

let get_expr e = e.exp
let get_abs_val e = e.v
let has_changed e = e.diff

type 'abs_val add_constraint_res =
  | AlreadyTrue (* The constraint is already true *)
  | AlreadyFalse (* The constraint is already false*)
  | NewConstraint of 'abs_val (* The new abstract value *)

(** 2. Simplifyer *)

(** As the simplifyer interacts with different components of alt-ergo,
    it is written to be as generic as possible.
    The simplifyer is then a functor of different modules which type is
    defined below. *)

(** Dom is the signature of the abstact domain. *)
module type Dom =
sig
  type v

  (** Top/Bottom value *)
  val top : v
  val bottom : v

  (** (Partial) Compare function *)
  val compare : v -> v -> int option

  (** Join operator *)
  val join : v -> v -> v

  (** Add constraint *)
  val add_constraint : Expr.t -> Expr.t -> Symbols.lit -> v -> v add_constraint_res

  val pp : Format.formatter -> v -> unit
end

(** This is the signature of the simplifyer. *)
module type S =
sig
  type v

  (** Simplifies an expression. *)
  val simp_expr : Expr.t -> (Expr.t, v) simp
end

module SimpleReasoner
    (D : Dom)
  : S with type v = D.v = struct
  type v = D.v

  let identity v exp = {exp; diff = false; v}

  (*
  let (|=) v1 v2 =
    match D.compare v1 v2 with
    | Some i -> i = 0
    | None -> false*)

  let simp_true = {exp = E.vrai; diff = true; v = D.top}
  let simp_false = {exp = E.faux; diff = true; v = D.top}

  let is_true e = E.equal e.exp E.vrai
  let is_false e = E.equal e.exp E.faux

  let rec add_lit_constraint (v : v) (e : Expr.t) =
    let exception Stop of v add_constraint_res in
    match E.lit_view e with
    | Eq (e1, e2) ->
      debug "[add_lit_constraint] Eq@.";
      D.add_constraint e1 e2 Sy.L_eq v

    | Eql [] -> assert false
    | Eql (hd :: tl) -> begin try
          debug "[add_lit_constraint] Eql@.";
          NewConstraint (
            List.fold_left
              (fun v e ->
                 match D.add_constraint hd e Sy.L_eq v with
                 | AlreadyTrue -> v
                 | AlreadyFalse -> raise (Stop AlreadyFalse)
                 | NewConstraint v' -> v'
              ) v tl
          )
        with Stop res -> res
      end
    | Distinct [] -> assert false
    | Distinct (hd :: tl) -> begin try
          debug "[add_lit_constraint] Distinct@.";
          NewConstraint (
            List.fold_left
              (fun v e ->
                 match D.add_constraint hd e Sy.L_neg_eq v with
                 | AlreadyTrue -> v
                 | AlreadyFalse -> raise (Stop AlreadyFalse)
                 | NewConstraint v' -> v') v tl)
        with Stop res -> res
      end
    | Builtin (_, btin, [e1; e2]) -> begin
        match D.add_constraint e1 e2 (Sy.L_built btin) v with
        | AlreadyTrue ->
          debug "[add_lit_constraint] Already true@.";
          AlreadyTrue
        | AlreadyFalse ->
          debug "[add_lit_constraint] Already false@.";
          AlreadyFalse
        | NewConstraint v' ->
          debug "[add_lit_constraint] New constraint: %a@."
            D.pp v';
          NewConstraint v'
      end
    | Builtin (_, _, _) -> failwith "Unhandled builtin"
    | Pred _ ->
      debug "[add_lit_constraint] Pred@.";
      NewConstraint v
    | Not_a_lit _ ->
      debug "[add_lit_constraint] Not a lit@.";
      failwith "add_lit_constraint should be only called on litterals"
 (*
  and add_form_constraint (v : v) (e : Expr.t) =
    match E.form_view e with
    | E.Unit (f1, f2) -> begin
        match add_lit_constaint v f1 with
        | AlreadyFalse ->
          
      end
      add_lit_constraint (add_lit_constraint v f1) f2

    | Clause (f1, f2, _) ->
      let v1 = add_lit_constraint v f1 in
      let v2 = add_lit_constraint v f2 in
      D.join v1 v2

    | Iff (f1, f2) ->
      let pos = add_lit_constraint (add_lit_constraint v f1) f2 in
      let neg = add_lit_constraint (add_lit_constraint v (E.neg f1)) (E.neg f2) in
      D.join pos neg

    | Xor (f1, f2) ->
      let v1 = add_lit_constraint (add_lit_constraint v f1) (E.neg f2) in
      let v2 = add_lit_constraint (add_lit_constraint v (E.neg f1)) f2 in
      D.join v1 v2

    | Literal e -> add_lit_constraint v e

    | Lemma _ | Skolem _ | Not_a_form -> v

    | Let _ -> failwith "todo"
 *)

  and (&&&) v e =
    add_lit_constraint v e
(*
  let is_true v = v |= D.vrai
  let is_false v = v |= D.faux
*)


  (*
  let is_constr (constr : Hstring.t) (e : expr) : bool option =
    match E.get_comp e with
    | Op (Constr s') -> Some (Hstring.equal constr s')
    | _ -> None*)

  and simp_ite
      (state : v)
      (cond : E.t)
      (th : E.t)
      (el : E.t) :
    (E.t, v) simp list =
    debug "[simp_ite] Simplifying condition %a with %a@." E.print cond D.pp state;
    let scond = simp_expr state cond in
    debug "[simp_ite] New condition %a ~~> %a@." E.print cond E.print scond.exp;
    if is_true scond then begin
      debug "[simp_ite] It is true, ending@.";
      let th : (E.t, v) simp = simp_expr state th in
      [{th with diff = true}]
    end else if is_false scond then begin
      debug "[simp_ite] It is false, ending@.";
      let el : (E.t, v) simp = simp_expr state el in
      [{el with diff = true}]
    end else let cth = scond.v in begin
        let neg_cond = E.neg scond.exp in
        match state &&& neg_cond with
        | AlreadyTrue ->
          debug "[simp_ite] Negation is true, ending@.";
          let el : (E.t, v) simp = simp_expr state el in
          [{el with diff = true}]
        | AlreadyFalse ->
          debug "[simp_ite] Negation is fakse, ending@.";
          let th : (E.t, v) simp = simp_expr state th in
          [{th with diff = true}]
        | NewConstraint cel ->
          debug "[simp_ite] Cannot conclude, simplifying branches@.";
          let sth : (E.t, v) simp = simp_expr cth th in
          let sel : (E.t, v) simp = simp_expr cel el in
          if scond.diff || sth.diff || sel.diff then
            [scond; sth; sel]
          else [
            identity scond.v cond;
            identity sth.v th;
            identity sel.v el]
      end

  and simp_form
      (state : v)
      (f : Symbols.form)
      (elist : E.t list)
    : v * (E.t, v) simp list =
    match f with
    | Symbols.F_Unit _ -> begin (* <=> AND *)
        let () = debug "F_Unit@." in
        let state,rev_res =
          fold_left_stop
            (fun (state, simp_exps) e ->
               let esimp : (E.t, v) simp = simp_expr state e in
               match state &&& esimp.exp with
               | AlreadyTrue -> (
                   debug "%a = true@." E.print e;
                   (state, simp_exps), false
                 )
               | AlreadyFalse -> (
                   debug "%a = false@." E.print e;
                   (state, [simp_false]), true
                 )
               | NewConstraint c -> (
                   debug "Keeping %a@." E.print e;
                   (c, esimp :: simp_exps), false
                 )
            )
            (state, [])
            elist
        in
        match rev_res with
        | [] -> state, [simp_true]
        | _ -> state, List.rev rev_res
      end

    | F_Clause _ -> begin (* <=> OR *)
        let () = debug "F_Clause@." in
        let state, rev_res =
          fold_left_stop
            (fun (state, simp_exps) e ->
               let (esimp : (E.t, v) simp) = simp_expr state e in
               if is_false esimp then (
                 debug "%a = false@." E.print e;
                 (state, simp_exps), false
               )
               else if is_true esimp then (
                 debug "%a = true@." E.print e;
                 (state, [simp_true]), true
               )
               else (
                 debug "Keeping %a@." E.print e;
                 (D.join state esimp.v, (esimp :: simp_exps)))
               , false)
            (state, [])
            elist
        in
        match rev_res with
        | [] -> state, [simp_false]
        | _ -> state, List.rev rev_res
      end
    | _ ->
      let () = debug "No additional simplification@." in
      D.top, List.map (identity D.top) elist

  and simp_expr state (e : E.t) : (E.t, v) simp =
    debug "[simp_expr] Simplifying expression %a with %a@." E.print e D.pp state;
    let ty = E.type_info e in
    let elist = E.get_sub_expr e in
    let symb = E.get_symb e in
    match symb, elist with
    | Op Tite, [cond; th; el] -> begin
        debug "[simp_expr] Ite@.";
        let simp = simp_ite state cond th el in
        debug "[simp_expr] Ite treated@.";
        match simp with
        | [branch] ->
          debug "[simp_expr] Simplification cut a branch, yielding %a@." Expr.print branch.exp;
          branch
        | [cond; th; el] ->
          if cond.diff || th.diff || el.diff then
            (* If by any luck, th == el... *)
            if Expr.equal th.exp el.exp then begin (* bingo *)
              debug "[simp_expr] Both branches are equal @.";
              {th with diff = true}
            end else begin
              (* A simplification has been made *)
              debug "[simp_expr] Simplification worked on a branch@."; {
                exp = E.mk_term (Op Tite) [cond.exp; th.exp; el.exp] ty;
                diff = true;
                v = D.join th.v el.v
              }
            end else begin
            debug "[simp_expr] Simplification worked on a branch@.";
            { (* Simplification failed *)
            exp = e;
            diff = false;
            v = D.join th.v el.v
          } end
        | _ -> assert false
      end
    | Op Tite, _ -> assert false
    | Symbols.Form f, _ ->
      debug "[simp_expr] Formula: %a@." Symbols.print symb;
      let v, l = simp_form state f elist in
      if List.exists (fun e -> e.diff) l then {
        exp = E.mk_term symb (List.map (fun e -> e.exp) l) ty;
        diff = true;
        v
      }
      else {exp = e; diff = false; v = D.top}
    | Symbols.Lit _, _ -> begin
      debug
        "[simp_expr] Litteral : %a@."
        Symbols.print symb;
      match add_lit_constraint state e with
      | AlreadyTrue  -> simp_true
      | AlreadyFalse -> simp_false
      | NewConstraint v -> {exp = e; diff = false; v}
    end
    | _ ->
      debug
        "[simp_expr] Other: %a@."
        Symbols.print symb;
      let (l : (E.t, v) simp list) = List.map (simp_expr state) elist in (
        if List.exists (fun e -> e.diff) l then {
          exp = E.mk_term symb (List.map (fun e -> e.exp) l) ty;
          diff = true;
          v = D.top
        }
        else {exp = e; diff = false; v = D.top}
      )

  (** Wrapper of simp_expr for verbose *)
  let simp_expr e =
    try
      debug "START Simplifying %a@." E.print e;
      let res = simp_expr D.top e in
      if res.diff
      then
        let () =
          debug
            "Old expression = %a@."
            E.print e;
          debug
            "New expression = %a@."
            E.print res.exp in
        res
      else
        let () =
          debug
            "No change on %a@."
            E.print e in
        identity res.v e
    with
      Failure s ->
      talk
        "Error while simplifying %a\n%s\n\
         I will continue with the initial expression@."
        E.print e
        s;
      identity D.top e
end
