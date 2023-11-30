(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type builtin =
    LE | LT (* arithmetic *)
  | IsConstr of Hstring.t (* ADT tester *)

type operator =
  | Tite
  (* Arithmetic *)
  | Plus | Minus | Mult | Div | Modulo | Pow
  (* ADTs *)
  | Access of Hstring.t | Record
  | Constr of Hstring.t (* enums, adts *)
  | Destruct of Hstring.t * bool
  (* Arrays *)
  | Get | Set
  (* BV *)
  | Concat
  | Extract of int * int (* lower bound * upper bound *)
  | BVnot | BVand | BVor | BVxor | Int2BV of int | BV2Nat
  (* FP *)
  | Float
  | Integer_round
  | Sqrt_real | Sqrt_real_default | Sqrt_real_excess
  | Abs_int | Abs_real | Real_of_int | Real_is_int
  | Int_floor | Int_ceil | Integer_log2
  | Max_real | Max_int | Min_real | Min_int
  | Not_theory_constant | Is_theory_constant | Linear_dependency
  | Optimize of {order : int; is_max : bool}

type lit =
  (* literals *)
  | L_eq
  | L_built of builtin
  | L_neg_eq
  | L_neg_built of builtin
  | L_neg_pred

type form =
  (* formulas *)
  | F_Unit of bool
  | F_Clause of bool
  | F_Iff
  | F_Xor
  | F_Lemma
  | F_Skolem

type name_kind = Ac | Other

type bound_kind = Unbounded | VarBnd of Var.t | ValBnd of Numbers.Q.t

type bound = (* private *)
  { kind : bound_kind; sort : Ty.t; is_open : bool; is_lower : bool }


type t =
  | True
  | False
  | Void
  | Name of { hs : Hstring.t ; kind : name_kind ; defined : bool }
  | Int of Z.t
  | Real of Q.t
  | Bitv of int * Z.t
  | Op of operator
  | Lit of lit
  | Form of form
  | Var of Var.t
  | In of bound * bound
  | MapsTo of Var.t
  | Let

type s = t

let name ?(kind=Other) ?(defined=false) s =
  Name { hs = Hstring.make s ; kind ; defined }

let var s = Var s
let int i = Int (Z.of_string i)
let bitv s =
  let biv =
    Stdcompat.String.fold_left (fun n c ->
        match c with
        | '0' -> Z.(n lsl 1)
        | '1' -> Z.((n lsl 1) lor ~$1)
        | _ -> assert false) Z.zero s
  in Bitv (String.length s, biv)
let real r = Real (Q.of_string r)
let constr s = Op (Constr (Hstring.make s))
let destruct ~guarded s = Op (Destruct (Hstring.make s, guarded))

let mk_bound kind sort ~is_open ~is_lower =
  {kind; sort; is_open; is_lower}

let mk_in b1 b2 =
  assert (b1.is_lower);
  assert (not b2.is_lower);
  In (b1, b2)

let mk_maps_to x = MapsTo x

let is_ac x = match x with
  | Name { kind = Ac; _ } -> true
  | _           -> false

let is_internal sy =
  match sy with
  | Name { hs; _ } ->
    let s = Hstring.view hs in
    Stdcompat.String.starts_with ~prefix:"." s ||
    Stdcompat.String.starts_with ~prefix:"@" s
  | _ -> false

let compare_kinds k1 k2 =
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
      | Extract (i1, j1), Extract (i2, j2) ->
        let r = Int.compare i1 i2 in
        if r = 0 then Int.compare j1 j2 else r
      | Int2BV n1, Int2BV n2 -> Int.compare n1 n2
      | Optimize {order=o1; is_max=b1}, Optimize {order=o2; is_max=b2} ->
        let c = o1 - o2 in
        if c <> 0 then c
        else Stdlib.compare b1 b2
      | _ , (Plus | Minus | Mult | Div | Modulo | Real_is_int
            | Concat | Extract _ | Get | Set | Float
            | Access _ | Record | Sqrt_real | Abs_int | Abs_real
            | Real_of_int | Int_floor | Int_ceil | Sqrt_real_default
            | Sqrt_real_excess | Min_real | Min_int | Max_real | Max_int
            | Integer_log2 | Pow | Integer_round
            | BVnot | BVand | BVor | BVxor | Int2BV _ | BV2Nat
            | Not_theory_constant | Is_theory_constant | Linear_dependency
            | Constr _ | Destruct _ | Tite | Optimize _) -> assert false
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

let compare_bounds_kind a b =
  Util.compare_algebraic a b
    (function
      | VarBnd h1, VarBnd h2 -> Var.compare h1 h2
      | ValBnd q1, ValBnd q2 -> Numbers.Q.compare q1 q2
      | _, (VarBnd _ | ValBnd _ | Unbounded) -> assert false
    )

let compare_bounds a b =
  let c = Ty.compare a.sort b.sort in
  if c <> 0 then c
  else
    let c = Stdlib.compare a.is_open b.is_open in
    if c <> 0 then c
    else
      let c = Stdlib.compare a.is_lower b.is_lower in
      if c <> 0 then c
      else compare_bounds_kind a.kind b.kind

let compare s1 s2 =
  Util.compare_algebraic s1 s2
    (function
      | Int z1, Int z2 -> Z.compare z1 z2
      | Real h1, Real h2 -> Q.compare h1 h2
      | Var v1, Var v2 | MapsTo v1, MapsTo v2 -> Var.compare v1 v2
      | Name { hs = h1; kind = k1; _ }, Name { hs = h2; kind = k2; _ } ->
        let c = Hstring.compare h1 h2 in
        if c <> 0 then c else compare_kinds k1 k2
      | Bitv (n1, s1), Bitv (n2, s2) ->
        let c = Int.compare n1 n2 in
        if c <> 0 then c else Z.compare s1 s2
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

let equal s1 s2 = compare s1 s2 = 0

let hash x =
  abs @@
  match x with
  | Void -> 0
  | True -> 1
  | False -> 2
  | Let -> 3
  | Bitv (n, s) -> 19 * (Hashtbl.hash n + Hashtbl.hash s) + 3
  | In (b1, b2) -> 19 * (Hashtbl.hash b1 + Hashtbl.hash b2) + 4
  | Name { hs = n; kind = Ac; _ } -> 19 * Hstring.hash n + 5
  | Name { hs = n; kind = Other; _ } -> 19 * Hstring.hash n + 6
  | Int z -> 19 * Z.hash z + 7
  | Real n -> 19 * Hashtbl.hash n + 7
  | Var v -> 19 * Var.hash v + 8
  | MapsTo v -> 19 * Var.hash v + 9
  | Op op -> 19 * Hashtbl.hash op + 10
  | Lit lit -> 19 * Hashtbl.hash lit + 11
  | Form x -> 19 * Hashtbl.hash x + 12

let string_of_bound_kind x = match x with
  | Unbounded -> "?"
  | VarBnd v -> Var.to_string v
  | ValBnd v -> Numbers.Q.to_string v

let string_of_bound b =
  let kd = string_of_bound_kind b.kind in
  if b.is_lower then
    Format.sprintf "%s %s" (if b.is_open then "]" else "[") kd
  else
    Format.sprintf "%s %s" kd (if b.is_open then "[" else "]")

let print_bound fmt b = Format.fprintf fmt "%s" (string_of_bound b)

let pp_name ppf s =
  Dolmen.Smtlib2.Script.Poly.Print.id ppf (Dolmen.Std.Name.simple s)

module AEPrinter = struct
  let pp_operator ppf op =
    match op with
    (* Core theory *)
    | Tite -> Fmt.pf ppf "ite"

    (* Reals and Ints theories *)
    | Plus -> Fmt.pf ppf "+"
    | Minus -> Fmt.pf ppf "-"
    | Mult -> Fmt.pf ppf "*"
    | Div -> Fmt.pf ppf "/"
    | Modulo -> Fmt.pf ppf "%%"
    | Pow -> Fmt.pf ppf "**"
    | Sqrt_real -> Fmt.pf ppf "sqrt_real"
    | Sqrt_real_default -> Fmt.pf ppf "sqrt_real_default"
    | Sqrt_real_excess -> Fmt.pf ppf "sqrt_real_excess"
    | Int_floor -> Fmt.pf ppf "int_floor"
    | Int_ceil -> Fmt.pf ppf "int_ceil"
    | Max_real -> Fmt.pf ppf "max_real"
    | Max_int -> Fmt.pf ppf "max_int"
    | Min_real -> Fmt.pf ppf "min_real"
    | Min_int -> Fmt.pf ppf "min_int"
    | Integer_log2 -> Fmt.pf ppf "integer_log2"
    | Integer_round -> Fmt.pf ppf "integer_round"

    (* Reals_Ints theory *)
    | Abs_int -> Fmt.pf ppf "abs_int"
    | Abs_real -> Fmt.pf ppf "abs_real"
    | Real_of_int -> Fmt.pf ppf "real_of_int"
    | Real_is_int -> Fmt.pf ppf "real_is_int"

    (* FixedSizedBitVectors theory *)
    | Extract (i, j) -> Fmt.pf ppf "^{%d; %d}" i j
    | Concat -> Fmt.pf ppf "@"
    | BV2Nat -> Fmt.pf ppf "bv2nat"
    | Int2BV n -> Fmt.pf ppf "int2bv[%d]" n
    | BVnot -> Fmt.pf ppf "bvnot"
    | BVand -> Fmt.pf ppf "bvand"
    | BVor -> Fmt.pf ppf "bvor"
    | BVxor -> Fmt.pf ppf "bvxor"

    (* ArraysEx theory *)
    | Get -> Fmt.pf ppf "get"
    | Set -> Fmt.pf ppf "set"

    (* DT theory *)
    | Record -> Fmt.pf ppf "@Record"
    | Access s -> Fmt.pf ppf "@Access_%a" Hstring.print s
    | Constr s -> Hstring.print ppf s
    | Destruct (s, g) ->
      Fmt.pf ppf "%s%a" (if g then "" else "!") Hstring.print s

    (* Float theory *)
    | Float -> Fmt.pf ppf "float"

    | Not_theory_constant -> Fmt.pf ppf "not_theory_constant"
    | Is_theory_constant -> Fmt.pf ppf "is_theory_constant"
    | Linear_dependency -> Fmt.pf ppf "linear_dependency"

    | Optimize {order; is_max=true} ->
      Fmt.pf ppf "maximize(-,%d)" order
    | Optimize {order; is_max=false} ->
      Fmt.pf ppf "minimize(-,%d)" order

  let pp_lit ppf lit =
    match lit with
    | L_eq -> Fmt.pf ppf "="
    | L_neg_eq -> Fmt.pf ppf "distinct"
    | L_built LE -> Fmt.pf ppf "<="
    | L_built LT -> Fmt.pf ppf "<"
    | L_neg_built LE -> Fmt.pf ppf ">"
    | L_neg_built LT -> Fmt.pf ppf ">="
    | L_neg_pred -> Fmt.pf ppf "not "
    | L_built (IsConstr h) ->
      Fmt.pf ppf "? %a" Hstring.print h
    | L_neg_built (IsConstr h) ->
      Fmt.pf ppf "?not? %a" Hstring.print h

  let pp_form ppf f =
    match f with
    | F_Unit _ -> Fmt.pf ppf "/\\"
    | F_Clause _ -> Fmt.pf ppf "\\/"
    | F_Lemma -> Fmt.pf ppf "Lemma"
    | F_Skolem -> Fmt.pf ppf "Skolem"
    | F_Iff -> Fmt.pf ppf "<->"
    | F_Xor -> Fmt.pf ppf "xor"

  let pp ?(show_vars = true) ppf sy =
    match sy with
    | Lit lit -> pp_lit ppf lit
    | Form form -> pp_form ppf form
    | Let -> Fmt.pf ppf "let"
    | Op op -> pp_operator ppf op

    (* Core theory *)
    | True -> Fmt.pf ppf "true"
    | False -> Fmt.pf ppf "false"
    | Void -> Fmt.pf ppf "void"
    | Name { hs = n; _ } -> pp_name ppf (Hstring.view n)
    | Var v when show_vars -> Fmt.pf ppf "'%s'" (Var.to_string v)
    | Var v -> Fmt.string ppf (Var.to_string v)

    (* Reals and Ints theories *)
    | Int i -> Z.pp_print ppf i
    | Real q -> Q.pp_print ppf q

    (* FixedSizedBitVectors theory *)
    | Bitv (n, s) ->
      Fmt.pf ppf "[|%s|]" (Z.format (Fmt.str "%%0%db" n) s)

    (* Symbols used in semantic triggers *)
    | In (lb, rb) ->
      Fmt.pf ppf "%s, %s" (string_of_bound lb) (string_of_bound rb)
    | MapsTo v -> Fmt.pf ppf "%a |->" Var.print v
end

module SmtPrinter = struct
  let pp_operator ppf op =
    match op with
    (* Core theory *)
    |Tite -> Fmt.pf ppf "ite"

    (* Reals and Ints theories *)
    | Plus -> Fmt.pf ppf "+"
    | Minus -> Fmt.pf ppf "-"
    | Mult -> Fmt.pf ppf "*"
    | Div -> Fmt.pf ppf "/"
    | Modulo -> Fmt.pf ppf "%%"

    (* Reals_Ints theory *)
    | Abs_int | Abs_real -> Fmt.pf ppf "abs"
    | Real_of_int -> Fmt.pf ppf "to_real"
    | Real_is_int -> Fmt.pf ppf "is_int"
    | Int_floor -> Fmt.pf ppf "to_int"

    (* FixedSizedBitVectors theory *)
    | Extract (i, j) -> Fmt.pf ppf "(_ extract %d %d)" j i
    | Concat -> Fmt.pf ppf "concat"
    | BV2Nat -> Fmt.pf ppf "bv2nat"
    | BVnot -> Fmt.pf ppf "bvnot"
    | BVand -> Fmt.pf ppf "bvand"
    | BVor -> Fmt.pf ppf "bvor"
    | BVxor -> Fmt.pf ppf "bvxor"

    (* ArraysEx theory *)
    | Get -> Fmt.pf ppf "select"
    | Set -> Fmt.pf ppf "store"

    (* DT theory *)
    | Record -> ()
    | Access s | Constr s | Destruct (s, _) -> Hstring.print ppf s

    (* Float theory *)
    | Float -> Fmt.pf ppf "ae.round"

    (* Not in the SMT-LIB standard *)
    | Int2BV n -> Fmt.pf ppf "(_ int2bv %d)" n
    | Not_theory_constant -> Fmt.pf ppf "ae.not_theory_constant"
    | Is_theory_constant -> Fmt.pf ppf "ae.is_theory_constant"
    | Linear_dependency -> Fmt.pf ppf "ae.linear_dependency"
    | Sqrt_real -> Fmt.pf ppf "ae.sqrt_real"
    | Sqrt_real_default -> Fmt.pf ppf "ae.sqrt_real_default"
    | Sqrt_real_excess -> Fmt.pf ppf "ae.sqrt_real_excess"
    | Int_ceil -> Fmt.pf ppf "ae.int_ceil"
    | Max_real -> Fmt.pf ppf "ae.max_real"
    | Max_int -> Fmt.pf ppf "ae.max_int"
    | Min_real -> Fmt.pf ppf "ae.min_real"
    | Min_int -> Fmt.pf ppf "ae.min_int"
    | Integer_log2 -> Fmt.pf ppf "ae.integer_log2"
    | Integer_round -> Fmt.pf ppf "ae.integer_round"
    | Pow -> Fmt.pf ppf "ae.pow"

    | Optimize _ ->
      (* TODO: this case will be removed in the PR #921. *)
      assert false

end

let pp_ae_operator = AEPrinter.pp_operator
let pp_smtlib_operator = SmtPrinter.pp_operator

let print_clean = AEPrinter.pp ~show_vars:false
let print = AEPrinter.pp ~show_vars:true

let to_string_clean sy =
  Fmt.str "%a" (AEPrinter.pp ~show_vars:false) sy

let to_string sy =
  Fmt.str "%a" (AEPrinter.pp ~show_vars:true) sy


module type Id = sig
  val fresh : ?base:string -> unit -> string
  val reset_fresh_cpt : unit -> unit
  val is_id : string -> bool
  val make_as_fresh : string -> string
end

module MakeId(S : sig val prefix : string end) : Id = struct

  let make_as_fresh = (^) S.prefix

  let fresh, reset_fresh_cpt =
    let cpt = ref 0 in
    let fresh_string ?(base = "") () =
      incr cpt;
      make_as_fresh (base ^ (string_of_int !cpt))
    in
    let reset_fresh_string_cpt () =
      cpt := 0
    in
    fresh_string, reset_fresh_string_cpt

  let is_id = Stdcompat.String.starts_with ~prefix:S.prefix
end

module InternalId = MakeId(struct let prefix = ".k" end)
module SkolemId = MakeId(struct let prefix = ".?__" end)
(* garder le suffixe "__" car cela influence l'ordre *)

let fresh_internal_string () = InternalId.fresh ()
let fresh_internal_name () = name (fresh_internal_string ())

let fresh_skolem_string base = SkolemId.fresh ~base ()
let fresh_skolem_name base = name (fresh_skolem_string base)

let make_as_fresh_skolem str = name (SkolemId.make_as_fresh str)

let is_fresh_internal_name = function
  | Name { hs = hd; _ } -> InternalId.is_id (Hstring.view hd)
  | _ -> false

let is_fresh_skolem = function
  | Name { hs = hd; _ } -> SkolemId.is_id (Hstring.view hd)
  | _ -> false

let is_get f = equal f (Op Get)
let is_set f = equal f (Op Set)

module Labels = Hashtbl.Make(struct
    type t = s
    let equal = equal
    let hash = hash
  end)

let labels = Labels.create 107

let add_label lbl t = Labels.replace labels t lbl

let label t = try Labels.find labels t with Not_found -> Hstring.empty

let clear_labels () = Labels.clear labels

let reset_id_builders () =
  InternalId.reset_fresh_cpt ();
  SkolemId.reset_fresh_cpt ()

module Set : Set.S with type elt = t =
  Set.Make (struct type t=s let compare=compare end)

module Map : Map.S with type key = t =
  Map.Make (struct type t = s let compare = compare end)
