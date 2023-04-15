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

open Types

type t = Types.symbol

let name ?(kind=Other) s = Name (Hstring.make s, kind)
let var s = Var s
let int i = Int (Hstring.make i)
let real r = Real (Hstring.make r)
let constr s = Op (Constr (Hstring.make s))
let destruct ~guarded s = Op (Destruct (Hstring.make s, guarded))

let mk_bound bkind sort ~is_open ~is_lower =
  {bkind; sort; is_open; is_lower}

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

let equal s1 s2 = Types.SYMBOL.compare s1 s2 = 0

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
  let kd = string_of_bound_kind b.bkind in
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
  | Bitv s -> "[|"^s^"|]"
  | Op Plus -> "+"
  | Op Minus -> "-"
  | Op Mult -> "*"
  | Op Div -> "/"
  | Op Modulo -> "%"
  | Op (Access s) ->
    if Options.get_output_smtlib () then
      (Hstring.view s)
    else
      "@Access_"^(Hstring.view s)
  | Op (Constr s) -> (Hstring.view s)
  | Op (Destruct (s,g)) ->
    Format.sprintf "%s%s" (if g then "" else "!") (Hstring.view s)

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
    type t = Types.symbol
    let equal = equal
    let hash = hash
  end)

let labels = Labels.create 107

let add_label lbl t = Labels.replace labels t lbl

let label t = try Labels.find labels t with Not_found -> Hstring.empty

let clear_labels () = Labels.clear labels

module Set = Types.SYMBOL.Set

module Map = Types.SYMBOL.Map

let print_map pr_elt fmt sbt =
  Map.iter (fun k v -> Format.fprintf fmt "%a -> %a  " print k pr_elt v) sbt

let compare = Types.SYMBOL.compare
let compare_bounds = Types.SYMBOL.compare_bounds
