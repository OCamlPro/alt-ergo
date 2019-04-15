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

let unary_op_opt (op : 'a -> 'b) (v : 'a option) : 'b option =
  match v with
    None -> None
  | Some v -> Some (op v)

(* Lazy evaluation of arguments is important. *)
let op_opt (op : 'a -> 'a -> 'b) (v1 : 'a option) (v2 : 'a option) : 'b option =
  match v1 with
    Some v1 ->
    unary_op_opt
      (fun v2 -> op v1 v2)
      v2
  | None -> None

(** All the following function try to check whether the expression in argument is
    true, false or unknown.
    They respectively return Some true, Some false and None.
    Similarily, functions manipulating values with return an option.
*)

let solve_const (c : Parsed.constant) : bool option =
  match c with
    Parsed.ConstTrue ->  Some true
  | Parsed.ConstFalse -> Some false
  | _c -> None (* This should not happen if the formula is well typed *)

type value =
    Bool of bool
  | Num of Num.num

let const_to_value (c : Parsed.constant) : value option =
  match c with
  | Parsed.ConstInt i -> (
      try Some (Num (Num.num_of_int @@ int_of_string i)) with _ -> None
    )
  | Parsed.ConstReal n -> Some (Num n)

  | Parsed.ConstTrue -> Some (Bool true)
  | Parsed.ConstFalse -> Some (Bool false)
  | _ -> None

let arith_op (op : Parsed.pp_infix)
  : (value option -> value option -> value option) =
  let none _ _ = None in
  let arith op v1 v2 =
    match v1, v2 with
      Some (Num v1), Some (Num v2) -> Some (Num (op v1 v2))
    | _ -> none v1 v2
  in
  match op with
    Parsed.PPadd -> arith Num.add_num
  | Parsed.PPsub -> arith Num.sub_num
  | Parsed.PPmul -> arith Num.mult_num
  | Parsed.PPmod -> arith Num.mod_num
  | Parsed.PPdiv -> none (* This is not defined yet as no type info is given *)
  | Parsed.PPand | Parsed.PPor | Parsed.PPxor
  | Parsed.PPimplies | Parsed.PPiff | Parsed.PPlt
  | Parsed.PPle | Parsed.PPgt | Parsed.PPge
  | Parsed.PPneq | Parsed.PPeq -> none (* Bad type *)

let rec lexpr_to_value (c : Parsed.lexpr) : value option =
  match c.pp_desc with
  | Parsed.PPconst c -> const_to_value c
  | Parsed.PPinfix (l1,op,l2) -> (arith_op op) (lexpr_to_value l1) (lexpr_to_value l2)
  | _ -> None

let exp_arith_op
    (pp_loc : Loc.t)
    (is_true : value option -> value option -> bool option)
    (le1 : Parsed.lexpr)
    (le2 : Parsed.lexpr) : Parsed.lexpr =
  let v1 = lexpr_to_value le1 in
  let v2 = lexpr_to_value le2 in
  let pp_desc =
    match is_true v1 v2 with
      Some true -> Parsed.PPconst Parsed.ConstTrue
    | Some false -> Parsed.PPconst Parsed.ConstFalse
    | None -> Parsed.PPinfix (le1, Parsed.PPlt, le2)
  in
  {pp_loc;
   pp_desc}

let rec simplify_infix
  (pp_loc : Loc.t)
  (op : Parsed.pp_infix)
  (le1 : Parsed.lexpr)
  (le2 : Parsed.lexpr) : Parsed.lexpr =
  match op with
  (* boolean operations as lazy as possible *)
    Parsed.PPand -> (
      let sl1 = simplify_boolean_expr le1 in
      match test_trivial_bool sl1 with
      | Some true -> simplify_boolean_expr le2
      | Some false-> {pp_loc; pp_desc =  Parsed.PPconst Parsed.ConstFalse}
      | None ->
        let sl2 = simplify_boolean_expr le2 in
        match test_trivial_bool sl2 with
          Some true -> sl1
        | Some false -> {pp_loc; pp_desc = Parsed.PPconst Parsed.ConstFalse}
        | _ ->
          {pp_loc;
           pp_desc = Parsed.PPinfix (sl1, Parsed.PPand, sl2)}
    )

  | Parsed.PPor -> (
      let sl1 = simplify_boolean_expr le1 in
      match test_trivial_bool sl1 with
      | Some true -> {pp_loc; pp_desc =  Parsed.PPconst Parsed.ConstTrue}
      | Some false -> simplify_boolean_expr le2
      | None ->
        let sl2 = simplify_boolean_expr le2 in
        match test_trivial_bool sl2 with
          Some true ->  {pp_loc; pp_desc =  Parsed.PPconst Parsed.ConstTrue}
        | Some false -> sl1
        | _ ->
          {pp_loc;
           pp_desc = Parsed.PPinfix (sl1, Parsed.PPor, sl2)}
    )

  | Parsed.PPxor -> (
      let sl1 = simplify_boolean_expr le1 in
      let sl2 = simplify_boolean_expr le2 in
      let pp_desc =
        match sl1.pp_desc, sl2.pp_desc with
          Parsed.PPconst Parsed.ConstTrue, Parsed.PPconst Parsed.ConstFalse
        | Parsed.PPconst Parsed.ConstFalse, Parsed.PPconst Parsed.ConstTrue
          -> Parsed.PPconst Parsed.ConstTrue

        | Parsed.PPconst Parsed.ConstFalse, Parsed.PPconst Parsed.ConstFalse
        | Parsed.PPconst Parsed.ConstTrue,Parsed.PPconst Parsed.ConstTrue
          -> Parsed.PPconst Parsed.ConstFalse

        | Parsed.PPconst Parsed.ConstTrue,_ -> Parsed.PPprefix (Parsed.PPnot, sl2)
        | Parsed.PPconst Parsed.ConstFalse, _ -> sl2.pp_desc
        | _,Parsed.PPconst Parsed.ConstTrue -> Parsed.PPprefix (Parsed.PPnot, sl1)
        | _, Parsed.PPconst Parsed.ConstFalse -> sl1.pp_desc
        | _,_ ->
          Parsed.PPinfix (sl1, Parsed.PPxor, sl2)
      in
      {pp_loc; pp_desc}
    )

  | Parsed.PPimplies -> (
      let sl1 = simplify_boolean_expr le1 in
      match test_trivial_bool sl1 with
        Some false -> {pp_loc; pp_desc =  Parsed.PPconst Parsed.ConstTrue}
      | Some true -> simplify_boolean_expr le2
      | None ->
        let sl2 = simplify_boolean_expr le2 in
        {pp_loc; pp_desc = Parsed.PPinfix (sl1, Parsed.PPxor, sl2)}
    )

  | Parsed.PPiff -> (
      let sl1 = simplify_boolean_expr le1 in
      let sl2 = simplify_boolean_expr le2 in
      match test_trivial_bool sl1, test_trivial_bool sl2 with
        Some true, Some true | Some false, Some false ->
        {pp_loc; pp_desc = Parsed.PPconst Parsed.ConstTrue}
      | Some true, Some false | Some false, Some true ->
        {pp_loc; pp_desc = Parsed.PPconst Parsed.ConstFalse}
      | _ ->
        {pp_loc; pp_desc = Parsed.PPinfix (sl1, PPiff, sl2)}
    )

  (* Bool-arith operations. Comparison iff elements can be parsed as int/reals. *)
  | Parsed.PPlt ->
    let is_true v1 v2 =
      match v1, v2 with
        Some (Num v1), (Some Num v2) -> Some ((Num.(</)) v1 v2)
      | _ -> None
    in
    exp_arith_op
      pp_loc
      is_true
      le1
      le2

  | Parsed.PPle ->
    let is_true v1 v2 =
      match v1, v2 with
        Some (Num v1), (Some Num v2) -> Some ((Num.(<=/)) v1 v2)
      | _ -> None
    in
    exp_arith_op
      pp_loc
      is_true
      le1
      le2

  | Parsed.PPgt ->
    let is_true v1 v2 =
      match v1, v2 with
        Some (Num v1), (Some Num v2) -> Some ((Num.(>/)) v1 v2)
      | _ -> None
    in
    exp_arith_op
      pp_loc
      is_true
      le1
      le2

  | PPge ->
    let is_true v1 v2 =
      match v1, v2 with
        Some (Num v1), (Some Num v2) -> Some ((Num.(>=/)) v1 v2)
      | _ -> None
    in
    exp_arith_op
      pp_loc
      is_true
      le1
      le2

  | PPeq ->
    let is_true v1 v2 =
      match v1, v2 with
        Some (Num v1), (Some Num v2) -> Some ((Num.(=/)) v1 v2)
      | Some (Bool b1), Some (Bool b2) -> Some (b1 = b2)
      | _ -> None
    in
    exp_arith_op
      pp_loc
      is_true
      le1
      le2

  | PPneq ->
    let is_true v1 v2 =
      match v1, v2 with
        Some (Num v1), (Some Num v2) -> Some ((Num.(<>/)) v1 v2)
      | Some (Bool b1), Some (Bool b2) -> Some (b1 <> b2)
      | _ -> None
    in
    exp_arith_op
      pp_loc
      is_true
      le1
      le2

  (* These infix does not return a boolean *)
  | PPadd | PPsub | PPmul | PPdiv | PPmod ->
    assert false (* Todo : less trashy *)

and simplify_boolean_prefix (op : Parsed.pp_prefix) (le : Parsed.lexpr) : Parsed.lexpr =
  match op with
    PPnot -> (
      let sl = simplify_boolean_expr le
      in
      match sl.pp_desc with
        Parsed.PPconst Parsed.ConstTrue ->
        {sl with pp_desc = Parsed.PPconst Parsed.ConstFalse}
      | Parsed.PPconst Parsed.ConstFalse ->
        {sl with pp_desc = Parsed.PPconst Parsed.ConstTrue}
      | _ -> {sl with pp_desc = Parsed.PPprefix (PPnot, sl)}
    )
  | PPneg -> assert false

(* Todo : this test may be too simple *)
and solve_isConstr (le : Parsed.lexpr) (lbl : string) : bool option =
  match le.pp_desc with
    Parsed.PPmapsTo (lbl',_) -> Some (String.equal lbl lbl')
  | _ -> None

and simplify_boolean_expr (le : Parsed.lexpr) : Parsed.lexpr =
  let pp_loc = le.pp_loc in
  match le.pp_desc with
  | Parsed.PPinfix (le1, op, le2) -> simplify_infix pp_loc op le1 le2

  | Parsed.PPprefix (op, le) -> simplify_boolean_prefix op le

  | Parsed.PPisConstr (le',lbl) -> (
      match solve_isConstr le' lbl with
        Some true -> {pp_loc; pp_desc = Parsed.PPconst Parsed.ConstTrue}
      | Some false -> {pp_loc; pp_desc = Parsed.PPconst Parsed.ConstFalse}
      | None -> le
  )

  | Parsed.PPforall _ | Parsed.PPexists _
  | Parsed.PPforall_named _ | PPexists_named _ -> le (* todo : find documentation *)

  | Parsed.PPinInterval _ -> le (* todo : simple to do *)

  | _ -> le

and test_trivial_bool lexp = match lexp.pp_desc with
  | Parsed.PPconst Parsed.ConstTrue -> Some true
  | Parsed.PPconst Parsed.ConstFalse -> Some false
  | _ -> None
