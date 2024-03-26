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

(* The logic for the [increase_lower_bound] function below is described in
   section 4.1 of

   Sharpening Constraint Programming approaches for Bit-Vector Theory.
   Zakaria Chihani, Bruno Marre, François Bobot, Sébastien Bardin.
   CPAIOR 2017. International Conference on AI and OR Techniques in
   Constraint Programming for Combinatorial Optimization Problems, Jun
   2017, Padova, Italy.
   https://cea.hal.science/cea-01795779/document *)

(* [left_cl_can_set highest_cleared cleared_can_set] returns the
   least-significant bit that is:
   - More significant than [highest_cleared], strictly;
   - Set in [cleared_can_set] *)
let left_cl_can_set highest_cleared cleared_can_set =
  let can_set = Z.(cleared_can_set asr highest_cleared) in
  highest_cleared + Z.trailing_zeros can_set

let increase_lower_bound b lb =
  (* [r] is the new candidate lower bound; we only keep the *unknown* bits of
     [lb] and otherwise use the known bits from the domain [b].

     [cleared_bits] contains the bits that were set in [lb] and got cleared in
     [r]; conversely, [set_bits] contains the bits that were cleared in [lb] and
     got set in [r]. *)
  let r = Z.logor b.bits_set (Z.logand lb (Z.lognot b.bits_clr)) in
  let cleared_bits = Z.logand lb (Z.lognot r) in
  let set_bits = Z.logand (Z.lognot lb) r in

  (* We now look at the most-significant bit that was changed (since [set_bits]
     and [cleared_bits] have disjoint bits set, comparing them is equivalent to
     comparing their most significant bit). *)
  let c = Z.compare set_bits cleared_bits in
  if c > 0 then (
    (* [set_bits > cleared_bits] means that the most-significant changed bit
       was 0, and is now 1.

       Any higher bits are unchanged, but all lower bits that are not forced
       must be cleared (for instance we can only increase 0b010 to 0b100;
       increasing it to 0b110 would be incorrect).

       The following clears any lower bits ([Z.numbits set_bits] is the
       most-significant bit that was set), unless they are forced to 1. *)
    let bit_to_set = Z.numbits set_bits in
    let mask = Z.(minus_one lsl bit_to_set) in
    Z.logand r @@ Z.logor mask b.bits_set
  ) else if c = 0 then (
    (* [set_bits] and [cleared_bits] can only be equal if they are both zero,
       because no bit can go from 0 to 1 *and* from 1 to 0 at the same time. *)
    assert (Z.equal set_bits Z.zero);
    assert (Z.equal r lb);
    lb
  ) else (
    (* [cleared_bits > set_bits] means that the most-significant changed bit was
       1, and is now 0. To achieve this while increasing the value, we need to
       set a higher bit from 0 to 1, and it needs to be the *lowest* bit that is
       higher than the most-significant changed bit.

       For instance to clear 0b01[1]011 we need to go to 0b100000.

       Once we found that bit (done by [left_cl_can_set]), we do the same thing
       as when the most-significant changed bit was 0 and is now 1 (see [if]
       case above). *)
    let bit_to_clear = Z.numbits cleared_bits in
    let cleared_can_set = Z.lognot @@ Z.logor r b.bits_clr in
    let bit_to_set = left_cl_can_set bit_to_clear cleared_can_set in
    if bit_to_set >= b.width then
      raise Not_found;
    let r = Z.logor r Z.(~$1 lsl bit_to_set) in
    let mask  = Z.(minus_one lsl bit_to_set) in
    Z.logand r @@ Z.logor mask b.bits_set
  )

let decrease_upper_bound b ub =
  (* x <= ub <-> ~ub <= ~x *)
  let sz = width b in
  let nub =
    increase_lower_bound (lognot b) (Z.extract (Z.lognot ub) 0 sz)
  in
  Z.extract (Z.lognot nub) 0 sz

let fold_domain f b acc =
  if b.width <= 0 then
    invalid_arg "Bitlist.fold_domain";
  let rec fold_domain_aux ofs b acc =
    if ofs >= b.width then (
      assert (is_fully_known b);
      f (value b) acc
    ) else if Z.testbit b.bits_clr ofs || Z.testbit b.bits_set ofs then
      fold_domain_aux (ofs + 1) b acc
    else
      let mask = Z.(one lsl ofs) in
      let acc =
        fold_domain_aux
          (ofs + 1) { b with bits_clr = Z.logor b.bits_clr mask } acc
      in
      fold_domain_aux
        (ofs + 1) { b with bits_set = Z.logor b.bits_set mask } acc
  in
  fold_domain_aux 0 b acc
