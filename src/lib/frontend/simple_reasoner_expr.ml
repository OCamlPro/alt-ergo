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

(** 2. Simplifyer *)

(** As the simplifyer interacts with different components of alt-ergo,
    it is written to be as generic as possible.
    The simplifyer is then a functor of different modules which type is
    defined below. *)

(** Dom is the signature of the abstact domain. *)
module type Dom =
sig
  type v
  type expr

  (** Top/Bottom value *)
  val top : v
  val bottom : v

  (** (Partial) Compare function *)
  val compare : v -> v -> int option

  (** Join operator *)
  val join : v -> v -> v

  (** Add constraint *)
  val add_constraint : expr -> v -> v

  (** Constants *)
  val vrai : v
  val faux : v
end

module type Expr = sig
  type t
  val equal : t -> t -> bool
  val mk_term : Symbols.t -> t list -> Ty.t -> t
  val get_comp : t -> Symbols.t
  val get_sub_expr : t -> t list
  val get_type : t -> Ty.t
  val neg : t -> t
  val vrai : t
  val faux : t
  val int : string -> t
  val real : string -> t
  val print : Format.formatter -> t -> unit
end

(** This is the signature of the simplifyer. *)
module type S =
sig
  type v
  type expr

  (** Simplifies an expression. *)
  val simp_expr : expr -> (expr, v) simp
end


module SimpleReasoner
    (E : Expr)
    (D : Dom with type expr = E.t)
  : S with type v = D.v and type expr = E.t = struct
  type expr = E.t
  type v = D.v

  let identity v exp = {exp; diff = false; v}

  (*

  let diff_list (l : ('a, 'expl) simp list) : (('a list), 'expl) simp =
    let rev =
      List.fold_left
        (fun acc s ->
           {exp = s.exp :: acc.exp;
            diff = acc.diff || s.diff;
            v = D.join acc.v s.v
           }
        )
        (identity [])
        l
    in
    {rev with exp = List.rev rev.exp}
  (* Check is an expression has an arithmetic type (Some true),
     a boolean type (Some false) or else (None). *)
  let is_arith (e : expr) : bool option =
    match E.get_type e with
      Ty.Tbool -> Some false
    | Ty.Tint | Ty.Treal
    | Ty.Tvar {value = Some Ty.Tint;_}
    | Ty.Tvar {value = Some Ty.Treal;_} -> Some true
    | _ -> None

  let value_from_query (e : expr) : (value * expl) option =
    match is_arith e with
      Some true -> (
        match T.q_query e !env with
          Some (res_query, expl) ->
          Some ((Num res_query), expl)
        | None -> None
      )
    | Some false -> (
        match T.bool_query e !env with
          Some (res_query, expl) ->
          Some ((Bool res_query), expl)
        | None -> None
      )
    | None -> None

  let expr_to_value (e : expr) : (value * expl) option  =
    match E.get_comp e with
      True -> Some ((Bool true), no_reason)
    | False -> Some ((Bool false), no_reason)
    | Int s -> Some ((Num (Q.of_string (Hstring.view s))), no_reason)
    | Real s -> Some ((Num (Q.of_string (Hstring.view s))), no_reason)
    | _ -> value_from_query e

  let value_to_expr (ty : Ty.t) (v : value) : expr =
    debug "Type = %a@." Ty.print ty;
    match v with
      Bool true -> E._true
    | Bool false -> E._false
    | Num i ->
      let i' = Q.to_string i in
      if ty == Ty.Treal
      then E.real i'
      else E.int i'

  let arith
      (ty : Ty.t)
      (op : value -> value -> value)
      (e_list : expr list): (expr list, expl) simp =
    (* Wrapper for op. Checks that it has been called.
       If it has never been called, then there have been no
       simplification. *)
    let op_has_been_called = ref 0 in
    let op v1 v2 =
      op_has_been_called := !op_has_been_called + 1 ;
      debug "Calling operator@.";
      op v1 v2
    in

    let vals,expl,exprs =
      fold_left
        (fun (acc_solved,acc_expl,acc_remain) v ->
           match expr_to_value v with
             None -> (acc_solved, acc_expl, v :: acc_remain)
           | Some (v, expl) ->
             let new_expl = Expl.union expl acc_expl in
             match acc_solved with
               None ->
               (Some v, new_expl, acc_remain)
             | Some old_v -> (Some (op old_v v), new_expl, acc_remain)
        )
        (None, Expl.empty, [])
        e_list
    in
      if !op_has_been_called = 0
      then
        begin
          debug "Operator has not been called.@.";
          identity e_list
        end
      else
        match vals with
          None -> identity e_list
        | Some v ->
          let cst_expr = value_to_expr ty v in
          debug "Result of simplifyable operations : %a@." E.pretty cst_expr;
          {v = List.rev exprs @ [value_to_expr ty v]; diff = true; expl}

  let oper (op : value -> value -> bool) (l : expr list) : bool * bool * expl =
    (* all_true is a boolean stating that every call of 'op' returned 'true'.
       set to true at the beginning, it is set to false if one of the
       list term.
       last_val is the last value that has been accepted by the test
       acc_expl is the accumulated explanations of each value tested
    *)
    let rec _oper
        (all_true : bool)
        (last_val : value option)
        (acc_expl : expl)
        (l : expr list) : bool * bool * expl =
      match l with
        [] -> (* No more elements, and none failed the test. *)
        false, all_true, acc_expl
      | hd :: tl ->
        let hd_val = expr_to_value hd in
        match hd_val, last_val with
        | None, None ->
          _oper false None acc_expl tl

        | Some (v, expl), None ->
          _oper
            all_true
            (Some v)
            (Expl.union expl acc_expl)
            tl

        | None, Some v ->
          _oper false (Some v) acc_expl tl

        | Some (v, expl), Some v' ->
          let res = op v v' in
          debug "Result : %a (op) %a = %b@."
            pp_val v' pp_val v res;
          if op v' v
          then (
            _oper all_true (Some v') (Expl.union expl acc_expl) tl
          )
          else (* The operation is not respected *) (
            true, false, (Expl.union expl acc_expl)
          )
    in
    _oper true None no_reason l

  let apply_op
      (op : value -> value -> bool)
      (l : expr list) : (expr list, expl) simp =
    let falsify,all_true,expl = oper op l in
    if falsify
    then {v = [E._false]; diff = true; expl}
    else if all_true
    then {v = [E._true]; diff = true; expl}
    else {v = l; diff = false; expl}

  let is_unary (o : Symbols.operator) : bool =
    let open Symbols in
    match o with
    | Plus | Minus | Mult | Div | Modulo
    | Concat | Extract | Get | Set | Fixed | Float
    | Reach | Record | Min_real | Min_int | Max_real | Max_int
    | Integer_log2 | Pow | Tite -> false

    | Access _
    | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
    | Sqrt_real_default | Sqrt_real_excess | Integer_round
    | Constr _
                | Destruct (_,_) -> true *)

  let (|=) v1 v2 =
    match D.compare v1 v2 with
    | Some i -> i = 0
    | None -> false

  let (&&&) v e = D.add_constraint e v

  let is_true v = v |= D.vrai
  let is_false v = v |= D.faux

  let simp_true = {exp = E.vrai; diff = true; v = D.vrai}
  let simp_false = {exp = E.faux; diff = true; v = D.faux}

  (*
  let is_constr (constr : Hstring.t) (e : expr) : bool option =
    match E.get_comp e with
    | Op (Constr s') -> Some (Hstring.equal constr s')
    | _ -> None*)

  let rec simp_ite
      (state : v)
      (cond : expr)
      (th : expr)
      (el : expr) :
    (expr, v) simp list =
    let scond : (expr, v) simp = simp_expr state cond in
    if is_true scond.v then
      let th : (expr, v) simp = simp_expr state th in
      [{th with diff = true}]
    else if is_false scond.v then
      let el : (expr, v) simp = simp_expr state el in
      [{el with diff = true}]
    else
      let neg_cond = E.neg scond.exp in
      let sth : (expr, v) simp = simp_expr (state &&& scond.exp) th in
      let sel : (expr, v) simp = simp_expr (state &&& neg_cond) el in
      if scond.diff || sth.diff || sel.diff then
         [scond; sth; sel]
      else [
        identity scond.v cond;
        identity sth.v th;
        identity sel.v el]

  and simp_form
      (state : v)
      (f : Symbols.form)
      (elist : expr list)
    : v * (expr, v) simp list =
        match f with
        | Symbols.F_Unit _ -> begin (* <=> AND *)
            let () = debug "F_Unit@." in
            let state,rev_res =
              fold_left_stop
                (fun (state, simp_exps) e ->
                   let esimp : (expr, v) simp = simp_expr state e in
                   if is_true esimp.v then (
                     debug "%a = true@." E.print e;
                     (state, simp_exps), false
                   )
                   else if is_false esimp.v then (
                     debug "%a = false@." E.print e;
                     (D.faux, [simp_false]), true
                   ) else (
                     debug "Keeping %a@." E.print e;
                     (state &&& esimp.exp, esimp :: simp_exps), false
                   )
                )
                (state, [])
                elist
            in
            match rev_res with
            | [] -> D.vrai, [simp_true]
            | _ -> state, List.rev rev_res
          end

        | F_Clause _ -> begin (* <=> OR *)
            let () = debug "F_Clause@." in
            let state, rev_res =
              fold_left_stop
                (fun (state, simp_exps) e ->
                   let (esimp : (expr, v) simp) = simp_expr state e in
                   if is_false esimp.v then (
                       debug "%a = false@." E.print e;
                       (state, simp_exps), false
                     )
                   else if is_true esimp.v then (
                     debug "%a = true@." E.print e;
                     (D.vrai, [simp_true]), true
                   )
                   else (
                     debug "Keeping %a@." E.print e;
                     (D.join state esimp.v, (esimp :: simp_exps)))
                   , false)
                (state, [])
                elist
            in
            match rev_res with
            | [] -> D.faux, [simp_false]
            | _ -> state, List.rev rev_res
          end
        | _ ->
          let () = debug "No additional simplification@." in
          D.top, List.map (identity D.top) elist

  and simp_expr state (e : expr) : (expr, v) simp =
    let ty = E.get_type e in
    let elist = E.get_sub_expr e in
    let symb = E.get_comp e in
    match symb, elist with
    | Op Tite, [cond; th; el] -> begin
        debug "Ite";
        let simp = simp_ite state cond th el in
        match simp with
        | [branch] -> branch
        | [cond; th; el] ->
          if cond.diff || th.diff || el.diff then { (* A simplification has been made *)
            exp = E.mk_term (Op Tite) [cond.exp; th.exp; el.exp] ty;
            diff = true;
            v = D.join th.v el.v
          } else { (* No simplification has been done *)
            exp = e;
            diff = false;
            v = D.join th.v el.v
          }
        | _ -> assert false
      end
    | Op Tite, _ -> assert false
    | Symbols.Form f, _ ->
      debug "Formula: %a@." Symbols.print symb;
      let v, l = simp_form state f elist in
      if List.exists (fun e -> e.diff) l then {
        exp = E.mk_term symb (List.map (fun e -> e.exp) l) ty;
        diff = true;
        v
      }
      else {exp = e; diff = false; v = D.top}
    | _ ->
      debug
        "Other: %a@."
        Symbols.print symb;
      let (l : (expr, v) simp list) = List.map (simp_expr state) elist in (
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
      debug "Simplifying %a@." E.print e;
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
