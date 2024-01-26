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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module Ex = Explanation

exception Inconsistent of Ex.t

(** A bitlist representing the known bits of a bit-vector of width [width].

    Active bits in [bits_set] are necessarily equal to [1].
    Active bits in [bits_clr] are necessarily equal to [0].

    The explanation [ex] justifies that the bitlist applies. *)
type t = { width: int ; bits_set : Z.t ; bits_clr : Z.t ; ex : Ex.t }

let unknown width ex =
  { width ; bits_set = Z.zero ; bits_clr = Z.zero ; ex }

let empty =
  { width = 0 ; bits_set = Z.zero ; bits_clr = Z.zero ; ex = Ex.empty }

let width { width; _ } = width

let explanation { ex; _ } = ex

let exact width value ex =
  { width
  ; bits_set = value
  ; bits_clr = Z.extract (Z.lognot value) 0 width
  ; ex }

let equal b1 b2 =
  b1.width = b2.width &&
  Z.equal b1.bits_set b2.bits_set &&
  Z.equal b1.bits_clr b2.bits_clr

let ones b = { b with bits_clr = Z.zero }

let zeroes b = { b with bits_set = Z.zero }

let add_explanation ~ex b = { b with ex = Ex.union b.ex ex }

let pp ppf { width; bits_set; bits_clr; ex } =
  for i = width - 1 downto 0 do
    if Z.testbit bits_set i then
      Fmt.pf ppf "1"
    else if Z.testbit bits_clr i then
      Fmt.pf ppf "0"
    else
      Fmt.pf ppf "?"
  done;
  if Options.(get_verbose () || get_unsat_core ()) then
    Fmt.pf ppf " %a" (Fmt.box Ex.print) ex

let bitlist ~width ~bits_set ~bits_clr ex =
  if not (Z.equal (Z.logand bits_set bits_clr) Z.zero) then
    raise @@ Inconsistent ex;

  { width; bits_set; bits_clr ; ex }

let bits_known b = Z.logor b.bits_set b.bits_clr

let num_unknown b = b.width - Z.popcount (bits_known b)

let value b = b.bits_set

let is_fully_known b =
  Z.(equal (shift_right (bits_known b + ~$1) b.width) ~$1)

let intersect ~ex b1 b2 =
  let width = b1.width in
  let bits_set = Z.logor b1.bits_set b2.bits_set in
  let bits_clr = Z.logor b1.bits_clr b2.bits_clr in
  bitlist ~width ~bits_set ~bits_clr
    (Ex.union b1.ex (Ex.union ex b2.ex))

let concat b1 b2 =
  let bits_set = Z.(logor (b1.bits_set lsl b2.width) b2.bits_set)
  and bits_clr = Z.(logor (b1.bits_clr lsl b2.width) b2.bits_clr)
  in
  (* Always consistent *)
  { width = b1.width + b2.width
  ; bits_set
  ; bits_clr
  ; ex = Ex.union b1.ex b2.ex
  }

let ( @ ) = concat

let extract b i j =
  (* Always consistent *)
  { width = j - i + 1
  ; bits_set = Z.extract b.bits_set i (j - i + 1)
  ; bits_clr = Z.extract b.bits_clr i (j - i + 1)
  ; ex = b.ex
  }

let lognot b =
  (* Always consistent *)
  { b with bits_set = b.bits_clr; bits_clr = b.bits_set }

let logand b1 b2 =
  let width = b1.width in
  let bits_set = Z.logand b1.bits_set b2.bits_set in
  let bits_clr = Z.logor b1.bits_clr b2.bits_clr in
  (* Always consistent *)
  { width
  ; bits_set
  ; bits_clr
  ; ex = Ex.union b1.ex b2.ex
  }

let logor b1 b2 =
  let width = b1.width in
  let bits_set = Z.logor b1.bits_set b2.bits_set in
  let bits_clr = Z.logand b1.bits_clr b2.bits_clr in
  (* Always consistent *)
  { width
  ; bits_set
  ; bits_clr
  ; ex = Ex.union b1.ex b2.ex
  }

let logxor b1 b2 =
  let width = b1.width in
  let bits_set =
    Z.logor
      (Z.logand b1.bits_set b2.bits_clr)
      (Z.logand b1.bits_clr b2.bits_set)
  and bits_clr =
    Z.logor
      (Z.logand b1.bits_set b2.bits_set)
      (Z.logand b1.bits_clr b2.bits_clr)
  in
  (* Always consistent *)
  { width
  ; bits_set
  ; bits_clr
  ; ex = Ex.union b1.ex b2.ex
  }
