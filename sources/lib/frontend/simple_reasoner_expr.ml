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

let verb = Options.simplify_verbose

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
    be reduced to a boolean or a float/int. *)
type value =
    Bool of bool
  | Num of float

let (++) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> Bool (b1 || b2)
  | Num n1, Num n2 -> Num (n1 +. n2)
  | _,_ -> assert false

let (--) v1 v2 =
  match v1, v2 with
  | Num n1, Num n2 -> Num (n1 -. n2)
  | _,_ -> assert false

let ( ** ) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> Bool (b1 && b2)
  | Num n1, Num n2 -> Num (n1 *. n2)
  | _,_ -> assert false

let (|=) v1 v2 =
  match v1, v2 with
    Bool b1, Bool b2 -> b1 == b2
  | Num n1, Num n2 -> Float.equal n1 n2
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

let pp_val fmt v =
  match v with
    Bool b -> Format.fprintf fmt "Bool %b" b
  | Num n -> Format.fprintf fmt "Num %f" n

(** A simplified formula/expr/... type.
    The diff field is set to false if the operation did not change the
    input.
    As queries may provide explanations, the third field correspond to the explanation
    behind the simplification.

 *)
type ('a, 'expl) simp =
  {
    v : 'a;
    diff : bool;
    expl : 'expl
  }

let get_expr (e : ('a,_) simp) : 'a = e.v
let has_changed (e : _ simp) : bool = e.diff
let get_expl (e : (_,'expl) simp) : 'a = e.expl

(** 2. Simplifyer *)

(** As the simplifyer interacts with different components of alt-ergo,
    it is written to be as generic as possible.
    The simplifyer is then a functor of different modules which type is
    defined below.
*)

(** Expr is the signature of the module dedicated to
    the representation of expressions that are to be
    simplified. *)
module type Expr =
sig
  type t

  val equal : t -> t -> bool
  val mk_expr : Symbols.t -> t list -> Ty.t -> t

  (** Expressions are generally defined by 3 elements:
      - a type
      - a set of sub expressions
      - a composition operator *)
  val get_comp : t -> Symbols.t
  val get_sub_expr : t -> t list
  val get_type : t -> Ty.t

  val vrai : t
  val faux : t

  val real : string -> t
  val int : string -> t

  val pretty : Format.formatter -> t -> unit
end

(** Expl is the signature of the module dedicated to
    the explanations of the calculations. *)
module type Expl =
sig
  type t

  (** Represents no explanation. *)
  val empty : t

  (** Merges two explanations. *)
  val union : t -> t -> t
end

(** Th is the signature of the module dedicated to
    the interactions with the theory. *)
module type Th =
sig
  type expr
  type env
  type expl

  (** An empty environment. Know nothing. *)
  val empty : unit -> env

  (** Tries to decide the expression in argument given the environment.
      If it fails, returns None. Otherwise, provides the answer and
      an explanation (possibly empty)
  *)
  val query : expr -> env -> (bool * expl) option
end

(** This is the signature of the simplifyer. *)
module type S =
sig
  (** The type of expressions. *)
  type expr

  (** The type of environments the theory works in. *)
  type env

  (** The type of explanations *)
  type expl

  (** Sets the environment to be used in the simplifyer.
      Set to empty by default. *)
  val set_env : env -> unit

  (** Simplifies an expression. *)
  val simp_expr : expr -> (expr,expl) simp
end

module SimpleReasoner
    (E : Expr)
    (Expl : Expl)
    (T : Th with type expr = E.t and type expl = Expl.t)
  : S with type expr = E.t and type env = T.env and type expl = Expl.t
=
struct
  type expr = E.t
  type env = T.env
  type expl = Expl.t

  let env = ref (T.empty ())

  let set_env e = env := e
  let no_reason = Expl.empty

  let identity v = {v; diff = false; expl = Expl.empty}
  let diff_list (l : ('a, 'expl) simp list) : (('a list), 'expl) simp =
    let rev =
      List.fold_left
        (fun acc s ->
           {v = s.v :: acc.v;
            diff = acc.diff || s.diff;
            expl = Expl.union acc.expl s.expl
           }
        )
        (identity [])
        l
    in
    {rev with v = List.rev rev.v}

  let expr_to_value (e : expr) : (value * expl) option  =
    match E.get_comp e with
      True -> Some ((Bool true), no_reason)
    | False -> Some ((Bool false), no_reason)
    | Int s -> Some ((Num (Float.of_string (Hstring.view s))), no_reason)
    | Real s -> Some ((Num (Float.of_string (Hstring.view s))), no_reason)
    | _ ->
      match T.query e !env with
        Some (res_query, expl) ->
        Some ((Bool res_query), expl)
      | None -> None

  let value_to_expr (ty : Ty.t) (v : value) : expr =
    debug "Type = %a@." Ty.print ty;
    match v with
      Bool true -> E.vrai
    | Bool false -> E.faux
    | Num i ->
      if ty == Ty.Treal
      then E.real (string_of_float i)
      else E.int (string_of_int @@ int_of_float i)

  let arith
      (ty : Ty.t)
      (op : value -> value -> value)
      (e_list : expr list): (expr list, expl) simp =
    (* Wrapper for op. Checks that it has been called.
       If it has never been called, then there have been no
       simplification. *)
    let op_has_been_called = ref false in
    let op v1 v2 =
      op_has_been_called := true ;
      debug "Calling operator.@.";
      op v1 v2
    in

    let vals,expl,exprs =
      List.fold_left
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
    if not (!op_has_been_called)
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
          else (
            true, false, (Expl.union expl acc_expl) (* The operation is not respected *)
          )
    in
    _oper true None no_reason l

  let apply_op (op : value -> value -> bool) (l : expr list) : (expr list, expl) simp =
    let falsify,all_true,expl = oper op l in
    if falsify
    then {v = [E.faux]; diff = true; expl}
    else if all_true
    then {v = [E.vrai]; diff = true; expl}
    else {v = l; diff = false; expl}

  let is_unary (o : Symbols.operator) : bool =
    let open Symbols in
    match o with
    | Plus | Minus | Mult | Div | Modulo
    | Concat | Extract | Get | Set | Fixed | Float
    | Reach | Record | Min_real | Min_int | Max_real | Max_int
    | Integer_log2 | Pow_real_int | Pow_real_real | Tite -> false

    | Access _
    | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
    | Sqrt_real_default | Sqrt_real_excess | Integer_round
    | Constr _
    | Destruct (_,_) -> true

  let rec simp_expr (e : expr) : (expr, expl) simp =
    if E.equal e E.vrai || E.equal e E.faux
    then {v = e; diff = false; expl = no_reason}
    else
      let query_res = T.query e !env in
      match query_res with
        Some (true, expl) -> {v = E.vrai; diff = true; expl}
      | Some (false, expl) -> {v = E.faux; diff = true; expl}
      | None ->
        let ty = E.get_type e in
        (* simp_expr treats 3 cases : either the expression is an operation,
           a formula or a literal.
           A function is dedicated to each of these cases, returning a simplified list
           of subexpressions. If this list contains only 1 element, it is either because
           it has been simplified to 1 element or because it is an operation over
           a single expression.
        *)

        (* The boolean states that the operation is a unary operation and must be preserved.
           Otherwise, it can be discarded.
           For example, (3 + 2) is simplified to 5, the operator '+' can be discarded.
           However, in f(3 + 2), f must not be discarded. *)
        let by_operator
            (op : Symbols.operator)
            (elist : expr list) :
          (expr list, expl) simp * bool =
          match op with
          | Symbols.Plus  -> arith ty (++) elist, false
          | Symbols.Minus -> arith ty (--) elist, false
          | Symbols.Mult  -> arith ty ( ** ) elist, false
          | Symbols.Tite -> (
              match elist with
                cond :: th :: el :: [] ->
                if E.(equal cond vrai) then {v = [th]; diff = true; expl = no_reason}
                else if E.(equal cond faux) then {v = [el]; diff = true; expl = no_reason}
                else if E.equal th el then {v = [th]; diff = true; expl = no_reason}
                else identity elist
              | _ -> assert false
            ), false
          | o -> identity elist, is_unary o in

        let by_form (f : Symbols.form) (elist : expr list) : (expr list, expl) simp =
          match f with
          | Symbols.F_Unit _ -> (* <=> AND *) (
              let () = debug "F_Unit@." in
              let res =
                fold_left_stop
                  (fun acc e ->
                     if E.(equal e vrai)
                     then (
                       debug "%a = true@." E.pretty e;
                       {acc with diff = true}, false
                     )
                     else if E.(equal e faux)
                     then (
                       debug "%a = false@." E.pretty e;
                       {v = [E.faux]; diff = true; expl = no_reason}, true
                     )
                     else
                       (
                         debug "Keeping %a@." E.pretty e;
                         {acc with v = (e :: acc.v)}, false
                       )
                  )
                  {v = []; diff= false; expl = no_reason}
                  elist
              in
              match res.v with
                [] -> {v = [E.vrai]; diff = true; expl = no_reason}
              | _ -> {res with v = List.rev res.v}
            )
          | F_Clause _ -> (* <=> OR *) (
              let () = debug "F_Clause@." in
              let res =
                fold_left_stop
                  (fun acc e ->
                     if E.(equal e faux)
                     then  (
                       debug "%a = false@." E.pretty e;
                       {acc with diff = true}, false
                     )
                     else if E.(equal e vrai)
                     then (
                       debug "%a = true@." E.pretty e;
                       {v = [E.vrai]; diff = true; expl = no_reason}, true
                     )
                     else (
                       debug "Keeping %a@." E.pretty e;
                       {acc with v = (e :: acc.v)}, false
                     )
                  )
                  {v = []; diff= false; expl = no_reason}
                  elist
              in
              match res.v with
                [] -> {v = [E.faux]; diff = true; expl = no_reason}
              | _ ->  {res with v = List.rev res.v}
            )
          | _ ->
            let () = debug "No additional simplification@." in identity elist

        and by_lit (l : Symbols.lit) (elist : expr list) : (expr list, expl) simp =
          let is_constr (constr : Hstring.t) (e : expr) : bool option =
            match E.get_comp e with
              Op (Constr s') -> Some (Hstring.equal constr s')
            | _ -> None
          in
          match l with
            L_eq -> (
              let res = apply_op (|=) elist in
              match res.v with
                [] | _ :: [] -> res
              | _ -> (* structural equality check *)
                if
                  List.for_all
                    (fun elt -> E.equal elt @@ List.hd res.v) (List.tl res.v)
                then
                  {v = [E.vrai]; diff = true; expl = no_reason}
                else res
            )
          | L_built LE -> apply_op (|<=) elist
          | L_built LT -> apply_op (|<) elist
          | L_neg_built LE -> apply_op (|>) elist
          | L_neg_built LT -> apply_op (|>=) elist
          | L_neg_built (IsConstr s) -> (
              match elist with
                e :: [] -> (
                  match is_constr s e with
                    None ->
                    debug
                      "%a is not explicitely the constructor %a, leaving as is@."
                      E.pretty e
                      Hstring.print s
                    ;
                    identity elist
                  | Some true  ->
                    debug
                      "%a is explicitely the constructor %a, this is FALSE@."
                      E.pretty e
                      Hstring.print s;
                    {v = [E.faux]; diff = true; expl = no_reason}
                  | Some false ->
                    debug
                      "%a is explicitely NOT the constructor %a, this is TRUE@."
                      E.pretty e
                      Hstring.print s;
                    {v = [E.vrai]; diff = true; expl = no_reason}
                )
              | _ -> assert false
            )
          | L_neg_pred -> identity elist
          | L_neg_eq -> apply_op (|<>) elist

          | L_built (IsConstr s) -> (
              match elist with
                e :: [] -> (
                  match is_constr s e with
                    None ->
                    debug
                      "%a is not explicitely the constructor %a, leaving as is@."
                      E.pretty e
                      Hstring.print s
                    ;
                    identity elist
                  | Some true  ->
                    debug
                      "%a is explicitely the constructor %a, this is TRUE@."
                      E.pretty e
                      Hstring.print s;
                    {v = [E.vrai]; diff = true; expl = no_reason}
                  | Some false ->
                    debug
                        "%a is explicitely NOT the constructor %a, this is FALSE@."
                        E.pretty e
                        Hstring.print s;
                    {v = [E.faux]; diff = true; expl = no_reason}
                )
              | _ -> assert false
            )
        in
        let elist =
          (List.map (fun e -> simp_expr e)) (E.get_sub_expr e) in
        let elist = diff_list elist in
        let xs, may_be_unary_op =
          let symb = E.get_comp e in
          match symb with
            Op o ->
            debug
              "Operator: %a@."
              Symbols.print symb;
            by_operator o elist.v
          | Form f ->
            debug
              "Formula: %a@."
              Symbols.print symb;
            by_form f elist.v, false
          | Lit l ->
            debug
              "Literal: %a@."
              Symbols.print symb;
            by_lit l elist.v, false
          | Name _ ->
            debug
              "Name: %a@."
              Symbols.print symb;
            elist, true
          | _ ->
            debug
              "Other: %a@."
              Symbols.print symb;
            elist, true
        in
        let diff = elist.diff || xs.diff in
        let expl = Expl.union elist.expl xs.expl in
        let v =
          if not diff then e
          else
            match xs.v with
              [] -> (* The simplification did something strange and discarded everything.
                       This should not happen. *)
              debug
                "Expression %a was discarded by simplifyer. Keeping it."
                E.pretty e;
              e
            | elt :: [] when not (may_be_unary_op) ->
              debug
                "Expression %a is now %a.@."
                E.pretty e E.pretty elt;
              (* It usually means that the expression is trivial. *)
              elt
            | l -> E.mk_expr (E.get_comp e) l (E.get_type e)
        in
        {v; diff; expl}

  (** Wrapper of simp_expr for verbose *)
  let simp_expr e =
    try
      debug "Simplifying %a@." E.pretty e;
      let res = simp_expr e in
      if res.diff
      then
        let () =
          debug
            "Old expression = %a@."
            E.pretty e;
          debug
            "New expression = %a@."
            E.pretty res.v in
        res
      else
        let () =
          debug
            "No change on %a@."
            E.pretty e
        in
        identity e
    with
      Failure s ->
      talk
        "Error while simplifying %a\n%s\nI will continue with the initial expression@."
        E.pretty e
        s;
      {v=e;diff=false;expl=no_reason}
end
