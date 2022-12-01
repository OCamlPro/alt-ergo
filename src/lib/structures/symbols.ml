(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

type builtin =
    LE | LT (* arithmetic *)
  | IsConstr of Hstring.t (* ADT tester *)
[@@deriving_inline compare]
let _ = fun (_ : builtin) -> ()
let compare_builtin =
  (fun a__001_ ->
     fun b__002_ ->
       if Ppx_compare_lib.phys_equal a__001_ b__002_
       then 0
       else
         (match (a__001_, b__002_) with
          | (LE, LE) -> 0
          | (LE, _) -> (-1)
          | (_, LE) -> 1
          | (LT, LT) -> 0
          | (LT, _) -> (-1)
          | (_, LT) -> 1
          | (IsConstr _a__003_, IsConstr _b__004_) ->
            Hstring.compare _a__003_ _b__004_) : builtin -> builtin -> int)
let _ = compare_builtin
[@@@end]

type operator =
    Plus | Minus | Mult | Div | Modulo
  | Concat | Extract | Get | Set | Fixed | Float
  | Reach | Access of Hstring.t | Record
  | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
  | Sqrt_real_default | Sqrt_real_excess
  | Min_real | Min_int | Max_real | Max_int | Integer_log2
  | Pow | Integer_round
  | Constr of Hstring.t (* enums, adts *)
  | Destruct of Bool.t * Hstring.t
  | Tite
[@@deriving_inline compare]
let _ = fun (_ : operator) -> ()
let compare_operator =
  (fun a__005_ ->
     fun b__006_ ->
       if Ppx_compare_lib.phys_equal a__005_ b__006_
       then 0
       else
         (match (a__005_, b__006_) with
          | (Plus, Plus) -> 0
          | (Plus, _) -> (-1)
          | (_, Plus) -> 1
          | (Minus, Minus) -> 0
          | (Minus, _) -> (-1)
          | (_, Minus) -> 1
          | (Mult, Mult) -> 0
          | (Mult, _) -> (-1)
          | (_, Mult) -> 1
          | (Div, Div) -> 0
          | (Div, _) -> (-1)
          | (_, Div) -> 1
          | (Modulo, Modulo) -> 0
          | (Modulo, _) -> (-1)
          | (_, Modulo) -> 1
          | (Concat, Concat) -> 0
          | (Concat, _) -> (-1)
          | (_, Concat) -> 1
          | (Extract, Extract) -> 0
          | (Extract, _) -> (-1)
          | (_, Extract) -> 1
          | (Get, Get) -> 0
          | (Get, _) -> (-1)
          | (_, Get) -> 1
          | (Set, Set) -> 0
          | (Set, _) -> (-1)
          | (_, Set) -> 1
          | (Fixed, Fixed) -> 0
          | (Fixed, _) -> (-1)
          | (_, Fixed) -> 1
          | (Float, Float) -> 0
          | (Float, _) -> (-1)
          | (_, Float) -> 1
          | (Reach, Reach) -> 0
          | (Reach, _) -> (-1)
          | (_, Reach) -> 1
          | (Access _a__007_, Access _b__008_) ->
            Hstring.compare _a__007_ _b__008_
          | (Access _, _) -> (-1)
          | (_, Access _) -> 1
          | (Record, Record) -> 0
          | (Record, _) -> (-1)
          | (_, Record) -> 1
          | (Sqrt_real, Sqrt_real) -> 0
          | (Sqrt_real, _) -> (-1)
          | (_, Sqrt_real) -> 1
          | (Abs_int, Abs_int) -> 0
          | (Abs_int, _) -> (-1)
          | (_, Abs_int) -> 1
          | (Abs_real, Abs_real) -> 0
          | (Abs_real, _) -> (-1)
          | (_, Abs_real) -> 1
          | (Real_of_int, Real_of_int) -> 0
          | (Real_of_int, _) -> (-1)
          | (_, Real_of_int) -> 1
          | (Int_floor, Int_floor) -> 0
          | (Int_floor, _) -> (-1)
          | (_, Int_floor) -> 1
          | (Int_ceil, Int_ceil) -> 0
          | (Int_ceil, _) -> (-1)
          | (_, Int_ceil) -> 1
          | (Sqrt_real_default, Sqrt_real_default) -> 0
          | (Sqrt_real_default, _) -> (-1)
          | (_, Sqrt_real_default) -> 1
          | (Sqrt_real_excess, Sqrt_real_excess) -> 0
          | (Sqrt_real_excess, _) -> (-1)
          | (_, Sqrt_real_excess) -> 1
          | (Min_real, Min_real) -> 0
          | (Min_real, _) -> (-1)
          | (_, Min_real) -> 1
          | (Min_int, Min_int) -> 0
          | (Min_int, _) -> (-1)
          | (_, Min_int) -> 1
          | (Max_real, Max_real) -> 0
          | (Max_real, _) -> (-1)
          | (_, Max_real) -> 1
          | (Max_int, Max_int) -> 0
          | (Max_int, _) -> (-1)
          | (_, Max_int) -> 1
          | (Integer_log2, Integer_log2) -> 0
          | (Integer_log2, _) -> (-1)
          | (_, Integer_log2) -> 1
          | (Pow, Pow) -> 0
          | (Pow, _) -> (-1)
          | (_, Pow) -> 1
          | (Integer_round, Integer_round) -> 0
          | (Integer_round, _) -> (-1)
          | (_, Integer_round) -> 1
          | (Constr _a__009_, Constr _b__010_) ->
            Hstring.compare _a__009_ _b__010_
          | (Constr _, _) -> (-1)
          | (_, Constr _) -> 1
          | (Destruct (_a__011_, _a__013_), Destruct (_b__012_, _b__014_)) ->
            (match Bool.compare _a__011_ _b__012_ with
             | 0 -> Hstring.compare _a__013_ _b__014_
             | n -> n)
          | (Destruct _, _) -> (-1)
          | (_, Destruct _) -> 1
          | (Tite, Tite) -> 0) : operator -> operator -> int)
let _ = compare_operator
[@@@end]

type lit =
  (* literals *)
  | L_eq
  | L_built of builtin
  | L_neg_eq
  | L_neg_built of builtin
  | L_neg_pred
[@@deriving_inline compare]
let _ = fun (_ : lit) -> ()
let compare_lit =
  (fun a__015_ ->
     fun b__016_ ->
       if Ppx_compare_lib.phys_equal a__015_ b__016_
       then 0
       else
         (match (a__015_, b__016_) with
          | (L_eq, L_eq) -> 0
          | (L_eq, _) -> (-1)
          | (_, L_eq) -> 1
          | (L_built _a__017_, L_built _b__018_) ->
            compare_builtin _a__017_ _b__018_
          | (L_built _, _) -> (-1)
          | (_, L_built _) -> 1
          | (L_neg_eq, L_neg_eq) -> 0
          | (L_neg_eq, _) -> (-1)
          | (_, L_neg_eq) -> 1
          | (L_neg_built _a__019_, L_neg_built _b__020_) ->
            compare_builtin _a__019_ _b__020_
          | (L_neg_built _, _) -> (-1)
          | (_, L_neg_built _) -> 1
          | (L_neg_pred, L_neg_pred) -> 0) : lit -> lit -> int)
let _ = compare_lit
[@@@end]



type form =
  (* formulas *)
  | F_Unit of Bool.t
  | F_Clause of Bool.t
  | F_Iff
  | F_Xor
  | F_Lemma
  | F_Skolem
[@@deriving_inline compare]
let _ = fun (_ : form) -> ()
let compare_form =
  (fun a__021_ ->
     fun b__022_ ->
       if Ppx_compare_lib.phys_equal a__021_ b__022_
       then 0
       else
         (match (a__021_, b__022_) with
          | (F_Unit _a__023_, F_Unit _b__024_) ->
            Bool.compare _a__023_ _b__024_
          | (F_Unit _, _) -> (-1)
          | (_, F_Unit _) -> 1
          | (F_Clause _a__025_, F_Clause _b__026_) ->
            Bool.compare _a__025_ _b__026_
          | (F_Clause _, _) -> (-1)
          | (_, F_Clause _) -> 1
          | (F_Iff, F_Iff) -> 0
          | (F_Iff, _) -> (-1)
          | (_, F_Iff) -> 1
          | (F_Xor, F_Xor) -> 0
          | (F_Xor, _) -> (-1)
          | (_, F_Xor) -> 1
          | (F_Lemma, F_Lemma) -> 0
          | (F_Lemma, _) -> (-1)
          | (_, F_Lemma) -> 1
          | (F_Skolem, F_Skolem) -> 0) : form -> form -> int)
let _ = compare_form
[@@@end]

type name_kind =
  | Ac
  | Other
[@@deriving_inline compare]
let _ = fun (_ : name_kind) -> ()
let compare_name_kind =
  (Ppx_compare_lib.polymorphic_compare : name_kind -> name_kind -> int)
let _ = compare_name_kind
[@@@end]

type bound_kind = VarBnd of Var.t | ValBnd of Numbers.Q.t
[@@deriving_inline equal, compare]
let _ = fun (_ : bound_kind) -> ()
let equal_bound_kind =
  (fun a__029_ ->
     fun b__030_ ->
       if Ppx_compare_lib.phys_equal a__029_ b__030_
       then true
       else
         (match (a__029_, b__030_) with
          | (VarBnd _a__031_, VarBnd _b__032_) -> Var.equal _a__031_ _b__032_
          | (VarBnd _, _) -> false
          | (_, VarBnd _) -> false
          | (ValBnd _a__033_, ValBnd _b__034_) ->
            Numbers.Q.equal _a__033_ _b__034_) : bound_kind ->
       bound_kind -> bool)
let _ = equal_bound_kind
let compare_bound_kind =
  (fun a__035_ ->
     fun b__036_ ->
       if Ppx_compare_lib.phys_equal a__035_ b__036_
       then 0
       else
         (match (a__035_, b__036_) with
          | (VarBnd _a__037_, VarBnd _b__038_) ->
            Var.compare _a__037_ _b__038_
          | (VarBnd _, _) -> (-1)
          | (_, VarBnd _) -> 1
          | (ValBnd _a__039_, ValBnd _b__040_) ->
            Numbers.Q.compare _a__039_ _b__040_) : bound_kind ->
       bound_kind -> int)
let _ = compare_bound_kind
[@@@end]

type bound = {
  sort: Ty.t;
  is_open: Bool.t;
  is_lower: Bool.t;
  kind: bound_kind;
} [@@deriving_inline equal, compare]
let _ = fun (_ : bound) -> ()
let equal_bound =
  (fun a__041_ ->
     fun b__042_ ->
       if Ppx_compare_lib.phys_equal a__041_ b__042_
       then true
       else
         Ppx_compare_lib.(&&) (Ty.equal a__041_.sort b__042_.sort)
           (Ppx_compare_lib.(&&) (Bool.equal a__041_.is_open b__042_.is_open)
              (Ppx_compare_lib.(&&)
                 (Bool.equal a__041_.is_lower b__042_.is_lower)
                 (equal_bound_kind a__041_.kind b__042_.kind))) : bound ->
       bound ->
       bool)
let _ = equal_bound
let compare_bound =
  (fun a__043_ ->
     fun b__044_ ->
       if Ppx_compare_lib.phys_equal a__043_ b__044_
       then 0
       else
         (match Ty.compare a__043_.sort b__044_.sort with
          | 0 ->
            (match Bool.compare a__043_.is_open b__044_.is_open with
             | 0 ->
               (match Bool.compare a__043_.is_lower b__044_.is_lower with
                | 0 -> compare_bound_kind a__043_.kind b__044_.kind
                | n -> n)
             | n -> n)
          | n -> n) : bound -> bound -> int)
let _ = compare_bound
[@@@end]

type t =
  | True
  | False
  | Void
  | Int of Hstring.t
  | Real of Hstring.t
  | Var of Var.t
  | Name of Hstring.t * name_kind
  | Bitv of String.t
  | Op of operator
  | Lit of lit
  | Form of form
  | In of bound * bound
  | MapsTo of Var.t
  | Let
[@@deriving_inline compare]
let _ = fun (_ : t) -> ()
let compare =
  (fun a__045_ ->
     fun b__046_ ->
       if Ppx_compare_lib.phys_equal a__045_ b__046_
       then 0
       else
         (match (a__045_, b__046_) with
          | (True, True) -> 0
          | (True, _) -> (-1)
          | (_, True) -> 1
          | (False, False) -> 0
          | (False, _) -> (-1)
          | (_, False) -> 1
          | (Void, Void) -> 0
          | (Void, _) -> (-1)
          | (_, Void) -> 1
          | (Int _a__047_, Int _b__048_) -> Hstring.compare _a__047_ _b__048_
          | (Int _, _) -> (-1)
          | (_, Int _) -> 1
          | (Real _a__049_, Real _b__050_) ->
            Hstring.compare _a__049_ _b__050_
          | (Real _, _) -> (-1)
          | (_, Real _) -> 1
          | (Var _a__051_, Var _b__052_) -> Var.compare _a__051_ _b__052_
          | (Var _, _) -> (-1)
          | (_, Var _) -> 1
          | (Name (_a__053_, _a__055_), Name (_b__054_, _b__056_)) ->
            (match Hstring.compare _a__053_ _b__054_ with
             | 0 -> compare_name_kind _a__055_ _b__056_
             | n -> n)
          | (Name _, _) -> (-1)
          | (_, Name _) -> 1
          | (Bitv _a__057_, Bitv _b__058_) ->
            String.compare _a__057_ _b__058_
          | (Bitv _, _) -> (-1)
          | (_, Bitv _) -> 1
          | (Op _a__059_, Op _b__060_) -> compare_operator _a__059_ _b__060_
          | (Op _, _) -> (-1)
          | (_, Op _) -> 1
          | (Lit _a__061_, Lit _b__062_) -> compare_lit _a__061_ _b__062_
          | (Lit _, _) -> (-1)
          | (_, Lit _) -> 1
          | (Form _a__063_, Form _b__064_) -> compare_form _a__063_ _b__064_
          | (Form _, _) -> (-1)
          | (_, Form _) -> 1
          | (In (_a__065_, _a__067_), In (_b__066_, _b__068_)) ->
            (match compare_bound _a__065_ _b__066_ with
             | 0 -> compare_bound _a__067_ _b__068_
             | n -> n)
          | (In _, _) -> (-1)
          | (_, In _) -> 1
          | (MapsTo _a__069_, MapsTo _b__070_) ->
            Var.compare _a__069_ _b__070_
          | (MapsTo _, _) -> (-1)
          | (_, MapsTo _) -> 1
          | (Let, Let) -> 0) : t -> t -> int)
let _ = compare
[@@@end]

type s = t

let name ?(kind=Other) s = Name (Hstring.make s, kind)
let var s = Var s
let int i = Int (Hstring.make i)
let real r = Real (Hstring.make r)
let constr s = Op (Constr (Hstring.make s))
let destruct ~guarded s = Op (Destruct (guarded, Hstring.make s))

let mk_bound kind sort ~is_open ~is_lower =
  {kind; sort; is_open; is_lower}

let mk_in b1 b2 =
  assert (b1.is_lower);
  assert (not b2.is_lower);
  In (b1, b2)

let mk_maps_to x = MapsTo x

let is_ac x = match x with
  | Name(_, Ac) -> true
  | _           -> false

let underscore =
  Random.self_init ();
  var @@ Var.of_string @@ Format.sprintf "_%d" (Random.int 1_000_000)

(*let compare_kinds k1 k2 =
  Util.compare_algebraic k1 k2
    (function
      | _, (Ac | Other) -> assert false
    )

  let compare_operators op1 op2 =
  Util.compare_algebraic op1 op2
    (function
      | Access h1, Access h2 | Constr h1, Constr h2 -> Hstring.compare h1 h2
      | Destruct (h1, b1), Destruct(h2, b2) ->
        let c = Stdlib.compare b1 b2 in
        if c <> 0 then c else Hstring.compare h1 h2
      | _ , (Plus | Minus | Mult | Div | Modulo
            | Concat | Extract | Get | Set | Fixed | Float | Reach
            | Access _ | Record | Sqrt_real | Abs_int | Abs_real
            | Real_of_int | Int_floor | Int_ceil | Sqrt_real_default
            | Sqrt_real_excess | Min_real | Min_int | Max_real | Max_int
            | Integer_log2 | Pow | Integer_round
            | Constr _ | Destruct _ | Tite) -> assert false
    )

  let compare_builtin b1 b2 =
  Util.compare_algebraic b1 b2
    (function
      | IsConstr h1, IsConstr h2 -> Hstring.compare h1 h2
      | _, (LT | LE | IsConstr _) -> assert false
    )

  let compare_lits lit1 lit2 =
  Util.compare_algebraic lit1 lit2
    (function
      | L_built b1, L_built b2 -> compare_builtin b1 b2
      | L_neg_built b1, L_neg_built b2 -> compare_builtin b1 b2
      | _, (L_eq | L_built _ | L_neg_eq | L_neg_built _ | L_neg_pred) ->
        assert false
    )

  let compare_forms f1 f2 =
  Util.compare_algebraic f1 f2
    (function
      | F_Unit b1, F_Unit b2
      | F_Clause b1, F_Clause b2 -> Stdlib.compare b1 b2
      | _, (F_Unit _ | F_Clause _ | F_Lemma | F_Skolem
           | F_Iff | F_Xor) ->
        assert false
    )
*)
(*let compare_bounds_kind a b =
  Util.compare_algebraic a b
    (function
      | VarBnd h1, VarBnd h2 -> Var.compare h1 h2
      | ValBnd q1, ValBnd q2 -> Numbers.Q.compare q1 q2
      | _, (VarBnd _ | ValBnd _) -> assert false
    )*)


(*let compare_bounds a b =
  let c = Ty.compare a.sort b.sort in
  if c <> 0 then c
  else
    let c = Stdlib.compare a.is_open b.is_open in
    if c <> 0 then c
    else
      let c = Stdlib.compare a.is_lower b.is_lower in
      if c <> 0 then c
      else compare_bound_kind a.kind b.kind*)

(*let compare s1 s2 =
  Util.compare_algebraic s1 s2
    (function
      | Int h1, Int h2
      | Real h1, Real h2 -> Hstring.compare h1 h2
      | Var v1, Var v2 | MapsTo v1, MapsTo v2 -> Var.compare v1 v2
      | Name (h1, k1), Name (h2, k2) ->
        let c = Hstring.compare h1 h2 in
        if c <> 0 then c else compare_kinds k1 k2
      | Bitv s1, Bitv s2 -> String.compare s1 s2
      | Op op1, Op op2 -> compare_operators op1 op2
      | Lit lit1, Lit lit2 -> compare_lits lit1 lit2
      | Form f1, Form f2 -> compare_forms f1 f2
      | In (b1, b2), In (b1', b2') ->
        let c = compare_bounds b1 b1' in
        if c <> 0 then c else compare_bounds b2 b2'
      | _ ,
        (True | False | Void | Name _ | Int _ | Real _ | Bitv _
        | Op _ | Lit _ | Form _ | Var _ | In _ | MapsTo _ | Let) ->
        assert false
    )*)

let equal s1 s2 = compare s1 s2 = 0

let hash x =
  abs @@
  match x with
  | Void -> 0
  | True -> 1
  | False -> 2
  | Let -> 3
  | Bitv s -> 19 * Hashtbl.hash s + 3
  | In (b1, b2) -> 19 * (Hashtbl.hash b1 + Hashtbl.hash b2) + 4
  | Name (n,Ac) -> 19 * Hstring.hash n + 5
  | Name (n,Other) -> 19 * Hstring.hash n + 6
  | Int n | Real n -> 19 * Hstring.hash n + 7
  | Var v -> 19 * Var.hash v + 8
  | MapsTo v -> 19 * Var.hash v + 9
  | Op op -> 19 * Hashtbl.hash op + 10
  | Lit lit -> 19 * Hashtbl.hash lit + 11
  | Form x -> 19 * Hashtbl.hash x + 12

let string_of_bound_kind x = match x with
  | VarBnd v -> Var.to_string v
  | ValBnd v -> Numbers.Q.to_string v

let string_of_bound b =
  let kd = string_of_bound_kind b.kind in
  if b.is_lower then
    Format.sprintf "%s %s" (if b.is_open then "]" else "[") kd
  else
    Format.sprintf "%s %s" kd (if b.is_open then "[" else "]")

let print_bound fmt b = Format.fprintf fmt "%s" (string_of_bound b)

let string_of_lit lit = match lit with
  | L_eq -> "="
  | L_neg_eq -> "<>"
  | L_neg_pred -> "not "
  | L_built LE -> "<="
  | L_built LT -> "<"
  | L_neg_built LE -> ">"
  | L_neg_built LT -> ">="
  | L_built (IsConstr h) ->
    Format.sprintf "? %s" (Hstring.view h)
  | L_neg_built (IsConstr h) ->
    Format.sprintf "?not? %s" (Hstring.view h)

let string_of_form f = match f with
  | F_Unit _ -> "/\\"
  | F_Clause _ -> "\\/"
  | F_Lemma -> "Lemma"
  | F_Skolem -> "Skolem"
  | F_Iff -> "<->"
  | F_Xor -> "xor"

let to_string ?(show_vars=true) x = match x with
  | Name (n,_) -> Hstring.view n
  | Var v when show_vars -> Format.sprintf "'%s'" (Var.to_string v)
  | Var v -> Var.to_string v
  | Int n -> Hstring.view n
  | Real n -> Hstring.view n
  | Bitv hs -> "[|"^hs^"|]"
  | Op Plus -> "+"
  | Op Minus -> "-"
  | Op Mult -> "*"
  | Op Div -> "/"
  | Op Modulo -> "%"
  | Op (Access hs) ->
    if Options.get_output_smtlib () then
      (Hstring.view hs)
    else
      "@Access_"^(Hstring.view hs)
  | Op (Constr hs) -> (Hstring.view hs)
  | Op (Destruct (guarded, hs)) ->
    Format.sprintf "%s%s" (if guarded then "" else "!") (Hstring.view hs)

  | Op Record -> "@Record"
  | Op Get -> "get"
  | Op Set -> "set"
  | Op Float -> "float"
  | Op Fixed -> "fixed"
  | Op Abs_int -> "abs_int"
  | Op Abs_real -> "abs_real"
  | Op Sqrt_real -> "sqrt_real"
  | Op Sqrt_real_default -> "sqrt_real_default"
  | Op Sqrt_real_excess -> "sqrt_real_excess"
  | Op Real_of_int -> "real_of_int"
  | Op Int_floor -> "int_floor"
  | Op Int_ceil -> "int_ceil"
  | Op Max_real -> "max_real"
  | Op Max_int -> "max_int"
  | Op Min_real -> "min_real"
  | Op Min_int -> "min_int"
  | Op Integer_log2 -> "integer_log2"
  | Op Pow -> "**"
  | Op Integer_round -> "integer_round"
  | Op Concat -> "@"
  | Op Extract -> "^"
  | Op Tite -> "ite"
  | Op Reach -> assert false
  | True -> "true"
  | False -> "false"
  | Void -> "void"
  | In (lb, rb) ->
    Format.sprintf "%s , %s" (string_of_bound lb) (string_of_bound rb)

  | MapsTo x ->  Format.sprintf "%s |->" (Var.to_string x)

  | Lit lit -> string_of_lit lit
  | Form form -> string_of_form form
  | Let -> "let"

let to_string_clean s = to_string ~show_vars:false s
let to_string s = to_string ~show_vars:true s

let print_clean fmt s = Format.fprintf fmt "%s" (to_string_clean s)
let print fmt s = Format.fprintf fmt "%s" (to_string s)


let fresh, reinit_fresh_sy_cpt =
  let cpt = ref 0 in
  let fresh ?(is_var=false) s =
    incr cpt;
    (* garder le suffixe "__" car cela influence l'ordre *)
    let s = (Format.sprintf "!?__%s%i" s (!cpt)) in
    if is_var then var @@ Var.of_string s else name s
  in
  let reinit_fresh_sy_cpt () =
    cpt := 0
  in
  fresh, reinit_fresh_sy_cpt

let is_get f = equal f (Op Get)
let is_set f = equal f (Op Set)


let fake_eq  =  name "@eq"
let fake_neq =  name "@neq"
let fake_lt  =  name "@lt"
let fake_le  =  name "@le"



module Labels = Hashtbl.Make(struct
    type t = s
    let equal = equal
    let hash = hash
  end)

let labels = Labels.create 107

let add_label lbl t = Labels.replace labels t lbl

let label t = try Labels.find labels t with Not_found -> Hstring.empty

let clear_labels () = Labels.clear labels

module Set : Set.S with type elt = t =
  Set.Make (struct type t=s let compare=compare end)

module Map : sig
  include Map.S with type key = t
  val print :
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end = struct
  include Map.Make (struct type t = s let compare = compare end)
  let print pr_elt fmt sbt =
    iter (fun k v -> Format.fprintf fmt "%a -> %a  " print k pr_elt v) sbt
end

