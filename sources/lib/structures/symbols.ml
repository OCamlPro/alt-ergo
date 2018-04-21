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
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Options

type operator =
    Plus | Minus | Mult | Div | Modulo
  | Concat | Extract | Get | Set | Fixed | Float
  | Reach | Access of Hstring.t | Record
  | Sqrt_real | Abs_int | Abs_real | Real_of_int | Int_floor | Int_ceil
  | Sqrt_real_default | Sqrt_real_excess
  | Min_real | Min_int | Max_real | Max_int | Integer_log2 | Pow_real_int
  | Pow_real_real | Integer_round

type name_kind = Ac | Constructor | Other

type bound_kind = VarBnd of Hstring.t | ValBnd of Numbers.Q.t

type bound =
  { kind : bound_kind; sort : Ty.t; is_open : bool; is_lower : bool }

type t =
  | True
  | False
  | Void
  | Name of Hstring.t * name_kind
  | Int of Hstring.t
  | Real of Hstring.t
  | Bitv of string
  | Op of operator
  | Var of Hstring.t
  | In of bound * bound
  | MapsTo of Hstring.t

type s = t

let name ?(kind=Other) s = Name (Hstring.make s, kind)
let var s = Var (Hstring.make s)
let int i = Int (Hstring.make i)
let real r = Real (Hstring.make r)


let mk_bound name sort ~is_open ~is_lower =
  let kind =
    try ValBnd (Numbers.Q.from_string (Hstring.view name))
    with _ -> VarBnd name
  in
  {kind; sort; is_open; is_lower}

let mk_in b1 b2 =
  assert (b1.is_lower);
  assert (not b2.is_lower);
  In (b1, b2)

let mk_maps_to x = MapsTo x

let is_ac = function
  | Name(_, Ac) -> true
  | _           -> false

let underscoring = function
Var s -> Var (Hstring.make ("$"^Hstring.view s))
  | _ -> assert false

let compare_kind k1 k2 = match k1, k2 with
  | Ac   , Ac    -> 0
  | Ac   , _     -> 1
  | _    , Ac    -> -1
  | Other, Other -> 0
  | Other, _     -> 1
  | _    , Other -> -1
  | Constructor, Constructor -> 0

let compare s1 s2 =  match s1, s2 with
  | Name (n1,k1), Name (n2,k2) ->
    let c = compare_kind k1 k2 in
    if c = 0 then Hstring.compare n1 n2 else c
  | Name _, _ ->  -1
  | _, Name _ -> 1
  | Var n1, Var n2 -> Hstring.compare n1 n2
  | Var _, _ -> -1
  | _ ,Var _ -> 1
  | Int i1, Int i2 -> Hstring.compare i1 i2
  | Int _, _ -> -1
  | _ ,Int _ -> 1
  | MapsTo i1, MapsTo i2 -> Hstring.compare i1 i2
  | MapsTo _, _ -> -1
  | _ ,MapsTo _ -> 1
  | Op(Access s1), Op(Access s2) -> Hstring.compare s1 s2
  | Op(Access _), _ -> -1
  | _, Op(Access _) -> 1
  | _  -> Pervasives.compare s1 s2

let equal s1 s2 = compare s1 s2 = 0

let hash = function
  | Name (n,Ac) -> Hstring.hash n * 19 + 1
  | Name (n,_) -> Hstring.hash n * 19
  | Var n (*| Int n*) -> Hstring.hash n * 19 + 1
  | Op (Access s) -> Hstring.hash s + 19
  | MapsTo hs -> Hstring.hash hs * 37
  | s -> Hashtbl.hash s

let string_of_bound_kind = function
  | VarBnd h -> Hstring.view h
  | ValBnd v -> Numbers.Q.to_string v

let string_of_bound b =
  let kd = string_of_bound_kind b.kind in
  if b.is_lower then
    Format.sprintf "%s %s" (if b.is_open then "]" else "[") kd
  else
    Format.sprintf "%s %s" kd (if b.is_open then "[" else "]")

let print_bound fmt b = Format.fprintf fmt "%s" (string_of_bound b)

let to_string ?(show_vars=true) =  function
  | Name (n,_) -> Hstring.view n
  | Var x when show_vars -> Format.sprintf "'%s'" (Hstring.view x)
  | Var x -> Hstring.view x
  | Int n -> Hstring.view n
  | Real n -> Hstring.view n
  | Bitv s -> "[|"^s^"|]"
  | Op Plus -> "+"
  | Op Minus -> "-"
  | Op Mult -> "*"
  | Op Div -> "/"
  | Op Modulo -> "%"
  | Op (Access s) -> "@Access_"^(Hstring.view s)
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
  | Op Pow_real_int -> "pow_real_int"
  | Op Pow_real_real -> "pow_real_real"
  | Op Integer_round -> "integer_round"
  | True -> "true"
  | False -> "false"
  | Void -> "void"
  | In (lb, rb) ->
    Format.sprintf "%s , %s" (string_of_bound lb) (string_of_bound rb)

  | MapsTo x ->
    Format.sprintf "%s |->" (Hstring.view x)

  | _ -> "" (*assert false*)

let to_string_clean s = to_string ~show_vars:false s
let to_string s = to_string ~show_vars:true s

let print_clean fmt s = Format.fprintf fmt "%s" (to_string_clean s)
let print fmt s = Format.fprintf fmt "%s" (to_string s)



let dummy = Name (Hstring.make "_one", Other)

let fresh =
  let cpt = ref 0 in
  fun ?(mk_var=false) s ->
    incr cpt;
    (* garder le suffixe "__" car cela influence l'ordre *)
    let s = (Format.sprintf "!?__%s%i" s (!cpt)) in
    if mk_var then var s else name s

let is_get f = equal f (Op Get)
let is_set f = equal f (Op Set)

let fake_eq  =  name "@eq"
let fake_neq =  name "@neq"
let fake_lt  =  name "@lt"
let fake_le  =  name "@le"

module Map =
  Map.Make(struct type t' = t type t=t' let compare=compare end)

module Set =
  Set.Make(struct type t' = t type t=t' let compare=compare end)



module Labels = Hashtbl.Make(struct
  type t = s
  let equal = equal
  let hash = hash
end)

let labels = Labels.create 100007

let add_label lbl t = Labels.replace labels t lbl

let label t = try Labels.find labels t with Not_found -> Hstring.empty
