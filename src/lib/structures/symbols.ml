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

open Ppx_compare_lib.Builtin

type builtin =
    LE | LT (* arithmetic *)
  | IsConstr of Hstring.t (* ADT tester *)
[@@deriving compare, equal]

type operator =
    Plus | Minus | Mult | Div | Modulo
  | Concat | Extract | Get | Set | Fixed | Float
  | Reach | Access of Hstring.t | Record
  | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
  | Sqrt_real_default | Sqrt_real_excess
  | Min_real | Min_int | Max_real | Max_int | Integer_log2
  | Pow | Integer_round
  | Constr of Hstring.t (* enums, adts *)
  | Destruct of bool * Hstring.t
  | Tite
[@@deriving compare, equal]

type lit =
  (* literals *)
  | L_eq
  | L_built of builtin
  | L_neg_eq
  | L_neg_built of builtin
  | L_neg_pred
[@@deriving compare, equal]

type form =
  (* formulas *)
  | F_Unit of bool
  | F_Clause of bool
  | F_Iff
  | F_Xor
  | F_Lemma
  | F_Skolem
[@@deriving compare, equal]

type name_kind =
  | Ac
  | Other
[@@deriving compare, equal]

type bound_kind = VarBnd of Var.t | ValBnd of Numbers.Q.t
[@@deriving compare, equal]

type bound = {
  sort: Ty.t;
  is_open: Bool.t;
  is_lower: Bool.t;
  kind: bound_kind;
} [@@deriving compare, equal]

type t =
  | True
  | False
  | Void
  | Int of Hstring.t
  | Real of Hstring.t
  | Var of Var.t
  | Name of Hstring.t * name_kind
  | Bitv of string
  | Op of operator
  | Lit of lit
  | Form of form
  | In of bound * bound
  | MapsTo of Var.t
  | Let
[@@deriving_inline compare, equal]
let _ = fun (_ : t) -> ()
let compare =
  (fun a__073_ ->
     fun b__074_ ->
       if Ppx_compare_lib.phys_equal a__073_ b__074_
       then 0
       else
         (match (a__073_, b__074_) with
          | (True, True) -> 0
          | (True, _) -> (-1)
          | (_, True) -> 1
          | (False, False) -> 0
          | (False, _) -> (-1)
          | (_, False) -> 1
          | (Void, Void) -> 0
          | (Void, _) -> (-1)
          | (_, Void) -> 1
          | (Int _a__075_, Int _b__076_) -> Hstring.compare _a__075_ _b__076_
          | (Int _, _) -> (-1)
          | (_, Int _) -> 1
          | (Real _a__077_, Real _b__078_) ->
            Hstring.compare _a__077_ _b__078_
          | (Real _, _) -> (-1)
          | (_, Real _) -> 1
          | (Var _a__079_, Var _b__080_) -> Var.compare _a__079_ _b__080_
          | (Var _, _) -> (-1)
          | (_, Var _) -> 1
          | (Name (_a__081_, _a__083_), Name (_b__082_, _b__084_)) ->
            (match Hstring.compare _a__081_ _b__082_ with
             | 0 -> compare_name_kind _a__083_ _b__084_
             | n -> n)
          | (Name _, _) -> (-1)
          | (_, Name _) -> 1
          | (Bitv _a__085_, Bitv _b__086_) ->
            compare_string _a__085_ _b__086_
          | (Bitv _, _) -> (-1)
          | (_, Bitv _) -> 1
          | (Op _a__087_, Op _b__088_) -> compare_operator _a__087_ _b__088_
          | (Op _, _) -> (-1)
          | (_, Op _) -> 1
          | (Lit _a__089_, Lit _b__090_) -> compare_lit _a__089_ _b__090_
          | (Lit _, _) -> (-1)
          | (_, Lit _) -> 1
          | (Form _a__091_, Form _b__092_) -> compare_form _a__091_ _b__092_
          | (Form _, _) -> (-1)
          | (_, Form _) -> 1
          | (In (_a__093_, _a__095_), In (_b__094_, _b__096_)) ->
            (match compare_bound _a__093_ _b__094_ with
             | 0 -> compare_bound _a__095_ _b__096_
             | n -> n)
          | (In _, _) -> (-1)
          | (_, In _) -> 1
          | (MapsTo _a__097_, MapsTo _b__098_) ->
            Var.compare _a__097_ _b__098_
          | (MapsTo _, _) -> (-1)
          | (_, MapsTo _) -> 1
          | (Let, Let) -> 0) : t -> t -> int)
let _ = compare
let equal =
  (fun a__099_ ->
     fun b__100_ ->
       if Ppx_compare_lib.phys_equal a__099_ b__100_
       then true
       else
         (match (a__099_, b__100_) with
          | (True, True) -> true
          | (True, _) -> false
          | (_, True) -> false
          | (False, False) -> true
          | (False, _) -> false
          | (_, False) -> false
          | (Void, Void) -> true
          | (Void, _) -> false
          | (_, Void) -> false
          | (Int _a__101_, Int _b__102_) -> Hstring.equal _a__101_ _b__102_
          | (Int _, _) -> false
          | (_, Int _) -> false
          | (Real _a__103_, Real _b__104_) -> Hstring.equal _a__103_ _b__104_
          | (Real _, _) -> false
          | (_, Real _) -> false
          | (Var _a__105_, Var _b__106_) -> Var.equal _a__105_ _b__106_
          | (Var _, _) -> false
          | (_, Var _) -> false
          | (Name (_a__107_, _a__109_), Name (_b__108_, _b__110_)) ->
            Ppx_compare_lib.(&&) (Hstring.equal _a__107_ _b__108_)
              (equal_name_kind _a__109_ _b__110_)
          | (Name _, _) -> false
          | (_, Name _) -> false
          | (Bitv _a__111_, Bitv _b__112_) -> equal_string _a__111_ _b__112_
          | (Bitv _, _) -> false
          | (_, Bitv _) -> false
          | (Op _a__113_, Op _b__114_) -> equal_operator _a__113_ _b__114_
          | (Op _, _) -> false
          | (_, Op _) -> false
          | (Lit _a__115_, Lit _b__116_) -> equal_lit _a__115_ _b__116_
          | (Lit _, _) -> false
          | (_, Lit _) -> false
          | (Form _a__117_, Form _b__118_) -> equal_form _a__117_ _b__118_
          | (Form _, _) -> false
          | (_, Form _) -> false
          | (In (_a__119_, _a__121_), In (_b__120_, _b__122_)) ->
            Ppx_compare_lib.(&&) (equal_bound _a__119_ _b__120_)
              (equal_bound _a__121_ _b__122_)
          | (In _, _) -> false
          | (_, In _) -> false
          | (MapsTo _a__123_, MapsTo _b__124_) -> Var.equal _a__123_ _b__124_
          | (MapsTo _, _) -> false
          | (_, MapsTo _) -> false
          | (Let, Let) -> true) : t -> t -> bool)
let _ = equal
[@@@end]

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
    )

  let equal s1 s2 = compare s1 s2 = 0*)

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
    type nonrec t = t
    let equal = equal
    let hash = hash
  end)

let labels = Labels.create 107

let add_label lbl t = Labels.replace labels t lbl

let label t = try Labels.find labels t with Not_found -> Hstring.empty

let clear_labels () = Labels.clear labels

module Set : Set.S with type elt = t =
  Set.Make (struct type nonrec t = t let compare=compare end)

module Map : sig
  include Map.S with type key = t
  val print :
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end = struct
  include Map.Make (struct type nonrec t = t let compare = compare end)
  let print pr_elt fmt sbt =
    iter (fun k v -> Format.fprintf fmt "%a -> %a  " print k pr_elt v) sbt
end

