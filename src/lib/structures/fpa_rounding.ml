(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
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
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module DStd = Dolmen.Std
module DE = DStd.Expr
module Q = Numbers.Q
module Z = Numbers.Z

(** The five standard rounding modes of the SMTLIB.
    Note that the SMTLIB defines these rounding modes to be the only
    possible modes. *)
type rounding_mode =
  | NearestTiesToEven
  | ToZero
  | Up
  | Down
  | NearestTiesToAway
[@@deriving ord]

let constrs =
  [
    NearestTiesToEven;
    ToZero;
    Up;
    Down;
    NearestTiesToAway;
  ]

let to_smt_string =
  function
  | NearestTiesToEven -> "RNE"
  | ToZero -> "RTZ"
  | Up -> "RTP"
  | Down -> "RTN"
  | NearestTiesToAway -> "RNA"

let pp_rounding_mode = Fmt.of_to_string to_smt_string

let to_ae_string = function
  | NearestTiesToEven -> "NearestTiesToEven"
  | ToZero -> "ToZero"
  | Up -> "Up"
  | Down -> "Down"
  | NearestTiesToAway -> "NearestTiesToAway"

let fpa_rounding_mode_ae_type_name = "fpa_rounding_mode"

let fpa_rounding_mode_type_name = "RoundingMode"

(* The exported 'to string' function is the SMT one. *)
let string_of_rounding_mode = to_smt_string

let string_smt_reprs =
  List.map
    (fun c -> to_smt_string c, [])
    constrs

let string_ae_reprs =
  List.map
    (fun c -> to_ae_string c)
    constrs

(* The rounding mode is the enum with the SMT values.
   The Alt-Ergo values are injected in this type. *)
let fpa_rounding_mode_dty, d_constrs, fpa_rounding_mode =
  (* We may use the builtin type `DStd.Expr.Ty.roundingMode` here. *)
  let ty_cst = DE.Ty.Const.mk (DStd.Path.global "RoundingMode") 0 in
  let constrs =
    List.map (fun c -> DStd.Path.global @@ to_smt_string c, []) constrs
  in
  let def, d_constrs =
    let def, l = DE.Term.define_adt ty_cst [] constrs in
    let constrs = List.map (fun (c, _) -> c) l in
    def, constrs
  in
  Nest.attach_orders [def];
  let body = List.map (fun c -> c, []) d_constrs in
  let ty = Ty.t_adt ~body:(Some body) ty_cst [] in
  DE.Ty.apply ty_cst [], d_constrs, ty

let tcst_of_rounding_mode =
  let table = Hashtbl.create 5 in
  List.iter2 (
    fun key bnd ->
      Hashtbl.add table key bnd
  ) constrs d_constrs;
  fun key ->
    try Hashtbl.find table key with
    | Not_found ->
      Fmt.failwith
        "Error while searching for mode %a."
        pp_rounding_mode key

let rounding_mode_of_smt =
  let table = Hashtbl.create 5 in
  List.iter2 (
    fun (key, _) bnd ->
      Hashtbl.add table key bnd
  ) string_smt_reprs constrs;
  fun key ->
    try Hashtbl.find table key with
    | Not_found ->
      Fmt.failwith
        "Error while searching for SMT2 FPA value %s."
        key
        fpa_rounding_mode_type_name

let rounding_mode_of_ae =
  let table = Hashtbl.create 5 in
  List.iter2 (
    fun key bnd ->
      Hashtbl.add table key bnd
  ) string_ae_reprs constrs;
  fun (key : string) ->
    try Hashtbl.find table key with
    | Not_found ->
      Fmt.failwith
        "Error while searching for Legacy FPA value %s."
        key
        fpa_rounding_mode_type_name

let translate_smt_rounding_mode hs =
  match rounding_mode_of_smt hs with
  | res -> Some (to_ae_string res)
  | exception (Failure _) -> None

(** Helper functions **)

let mult_x_by_2_pow_n x n =
  (* Q.mul_2exp does not support negative i according to Cody ? *)
  let res1 = if n >= 0 then Q.mult_2exp x n else Q.div_2exp x (-n) in
  let res2 = Q.mult res1 Q.one in (* Bug in Zarith according to Cody ? *)
  assert (Q.equal res1 res2);
  res2

let div_x_by_2_pow_n x n = mult_x_by_2_pow_n x (-n)

let two = Q.from_int 2

let half = Q.div Q.one two

(* Integer part of binary logarithm for NON-ZERO POSITIVE number *)
let integer_log_2 =
  let rec aux m e =
    if Q.compare m two >= 0 then aux (div_x_by_2_pow_n m 1) (e+1)
    else
    if Q.compare m Q.one >= 0 then e
    else
      let () = assert (Q.compare_to_0 m > 0) in
      aux (mult_x_by_2_pow_n m 1) (e - 1)
  in
  fun m ->
    if Q.compare_to_0 m <= 0 then
      begin
        Printer.print_err
          "integer_log_2 not defined for input (%a)" Q.print m;
        assert false
      end;
    let res = aux m 0 in
    (* Printer.print_dbg
       "found that integer_log_2 of %a is %d" Q.print m res;*)
    assert (Q.compare (mult_x_by_2_pow_n Q.one res) m <= 0);
    assert (Q.compare (mult_x_by_2_pow_n Q.one (res+1)) m > 0);
    res

let signed_one y =
  let tmp = Q.sign y in
  assert (tmp <> 0);
  if tmp > 0 then Z.one else Z.m_one


let round_big_int (mode : rounding_mode) y =
  match mode with
  | Up     -> Q.num (Q.ceiling y)
  | Down   -> Q.num (Q.floor y)
  | ToZero -> Q.truncate y

  | NearestTiesToEven ->
    let z = Q.truncate y in
    let diff = Q.abs (Q.sub y (Q.from_z z)) in
    if Q.sign diff = 0 then z
    else
      let tmp = Q.compare diff half in
      if tmp < 0 then z
      else if tmp > 0 then Z.add z (signed_one y)
      else if Z.testbit z 0 then Z.add z (signed_one y)
      else z

  | NearestTiesToAway ->
    let z = Q.truncate y in
    let diff = Q.abs (Q.sub y (Q.from_z z)) in
    if Q.sign diff = 0 then z
    else if Q.compare diff half < 0 then z else Z.add z (signed_one y)

let to_mantissa_exp prec exp mode x =
  let sign_x = Q.sign x in
  assert ((sign_x = 0) == Q.equal x Q.zero);
  if sign_x = 0 then Z.zero, 1
  else
    let abs_x = Q.abs x in
    let e = integer_log_2 abs_x in
    let e' = max (e + 1 - prec) (- exp) in
    let y = mult_x_by_2_pow_n x (-e') in
    let r_y = round_big_int mode y in
    r_y, e'

module MQ =
  Map.Make (struct
    type t = int * int * rounding_mode * Q.t
    let compare (prec1, exp1, mode1, x1) (prec2, exp2, mode2, x2) =
      let c = Q.compare x1 x2 in
      if c <> 0 then c
      else
        let c = prec1 - prec2 in
        if c <> 0 then c
        else
          let c = exp1 - exp2 in
          if c <> 0 then c
          else compare_rounding_mode mode1 mode2
  end)

let cache = ref MQ.empty

(* Compute the floating-point approximation of a rational number *)
let float_of_rational prec exp mode x =
  (* prec = 24 and exp = 149 for 32 bits (or exp = -149 ???) *)
  let input = (prec, exp, mode, x) in
  try MQ.find input !cache
  with Not_found ->
    let m, e = to_mantissa_exp prec exp mode x in
    let res = mult_x_by_2_pow_n (Q.from_z m) e in
    cache := MQ.add input (res, m, e) !cache;
    res, m, e

let round_to_integer mode q =
  Q.from_z (round_big_int mode q)

let empty_cache () =
  cache := MQ.empty
