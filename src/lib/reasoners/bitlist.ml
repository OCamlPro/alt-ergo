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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module Ex = Explanation

exception Inconsistent of Ex.t

(** A bitlist representing the known bits of an infinite-width bit-vector.
    Negative numbers are represented in two's complement.

    Active bits in [bits_set] are necessarily equal to [1].
    Active bits in [bits_unk] are not known and may be either [0] or [1].
    Bits that are active in neither [bits_set] nor [bits_unk] are equal to [0].

    The sign is known (and equal to the sign of [bits_set]) if [bits_unk] is
    positive, and the sign is unknown if [bits_unk] is negative.

    An integer [x] is represented by the bitlist iff the following equality
    holds: [x & ~bits_unk = bits_set].

    The explanation [ex] justifies that the bitlist applies. *)
type t = { bits_set : Z.t ; bits_unk : Z.t ; ex : Ex.t }

let constant n ex =
  { bits_set = n ; bits_unk = Z.zero ; ex }

let zero ex = constant Z.zero ex

let empty = zero Ex.empty

let unknown = { bits_set = Z.zero ; bits_unk = Z.minus_one ; ex = Ex.empty }

let explanation { ex; _ } = ex

let exact value ex =
  { bits_set = value
  ; bits_unk = Z.zero
  ; ex }

let equal b1 b2 =
  Z.equal b1.bits_set b2.bits_set &&
  Z.equal b1.bits_unk b2.bits_unk

let ones b = { b with bits_unk = Z.(b.bits_unk lor ~!(b.bits_set)) }

let zeroes b =
  { b with bits_set = Z.zero ; bits_unk = Z.logor b.bits_unk b.bits_set }

let add_explanation ~ex b = { b with ex = Ex.union b.ex ex }

let pp ppf { bits_set; bits_unk; ex } =
  begin if Z.sign bits_unk < 0 then
      (* Sign is not known *)
      Fmt.pf ppf "(?)"
    else if Z.sign bits_set < 0 then
      Fmt.pf ppf "(1)"
    else
      Fmt.pf ppf "(0)"
  end;
  let width = max (Z.numbits bits_set) (Z.numbits bits_unk) in
  for i = width - 1 downto 0 do
    if Z.testbit bits_set i then
      Fmt.pf ppf "1"
    else if Z.testbit bits_unk i then
      Fmt.pf ppf "?"
    else
      Fmt.pf ppf "0"
  done;
  if Options.(get_verbose () || get_unsat_core ()) then
    Fmt.pf ppf " %a" (Fmt.box Ex.print) ex

let unknown_bits b = b.bits_unk

let value b = b.bits_set

let is_fully_known b = Z.equal b.bits_unk Z.zero

let intersect b1 b2 =
  let bits_set = Z.logor b1.bits_set b2.bits_set in
  let bits_unk = Z.logand b1.bits_unk b2.bits_unk in
  (* If there is a bit that is known in both bitlists with different values,
     the intersection is empty. *)
  let distinct = Z.logxor b1.bits_set b2.bits_set in
  let known = Z.lognot (Z.logor b1.bits_unk b2.bits_unk) in
  if not (Z.equal (Z.logand distinct known) Z.zero) then
    raise @@ Inconsistent (Ex.union b1.ex b2.ex);

  { bits_set ; bits_unk ; ex = Ex.union b1.ex b2.ex }

let extract b ofs len =
  if len = 0 then empty
  else
    (* Always consistent *)
    { bits_set = Z.extract b.bits_set ofs len
    ; bits_unk = Z.extract b.bits_unk ofs len
    ; ex = b.ex
    }

let lognot b =
  (* Always consistent *)
  { b with bits_set = Z.(~!(b.bits_set lor b.bits_unk))}

let ( ~! ) = lognot

let logor b1 b2 =
  (* A bit is set in [b1 | b2] if it is set in either [b1] or [b2]. *)
  let bits_set = Z.logor b1.bits_set b2.bits_set in
  (* A bit is unknown in [b1 | b2] if it is unknown in either [b1] or [b2],
     unless is set to [1] in either [b1] or [b2]. *)
  let bits_unk =
    Z.logand (Z.logor b1.bits_unk b2.bits_unk)
      (Z.lognot bits_set)
  in
  (* Always consistent *)
  { bits_set
  ; bits_unk
  ; ex = Ex.union b1.ex b2.ex
  }

let ( lor ) = logor

let logand b1 b2 =
  let bits_set = Z.logand b1.bits_set b2.bits_set in
  (* A bit is unknown in [b1 & b2] if it is unknown in both [b1] and [b2], or if
     it is equal to [1] in either side and unknown in the other. *)
  let bits_unk =
    Z.logor (Z.logand b1.bits_set b2.bits_unk) @@
    Z.logor (Z.logand b1.bits_unk b2.bits_set) @@
    Z.logand b1.bits_unk b2.bits_unk
  in
  (* Always consistent *)
  { bits_set
  ; bits_unk
  ; ex = Ex.union b1.ex b2.ex
  }

let ( land ) = logand

let logxor b1 b2 =
  (* A bit is unknown in [b1 ^ b2] if it is unknown in either [b1] or [b2]. *)
  let bits_unk = Z.logor b1.bits_unk b2.bits_unk in
  (* Need to mask because [Z.logxor] will compute a bogus value for unknown
     bits. *)
  let bits_set =
    Z.logand
      (Z.logxor b1.bits_set b2.bits_set)
      (Z.lognot bits_unk)
  in
  (* Always consistent *)
  { bits_set
  ; bits_unk
  ; ex = Ex.union b1.ex b2.ex
  }

let ( lxor ) = logxor

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
   - Set in [cleared_can_set]

   Raises [Not_found] if there are no such bit. *)
let left_cl_can_set highest_cleared cleared_can_set =
  let can_set = Z.(cleared_can_set asr highest_cleared) in
  if Z.equal can_set Z.zero then raise Not_found;
  highest_cleared + Z.trailing_zeros can_set

let increase_lower_bound b lb =
  (* [r] is the new candidate lower bound; we only keep the *unknown* bits of
     [lb] and otherwise use the known bits from the domain [b].

     [cleared_bits] contains the bits that were set in [lb] and got cleared in
     [r]; conversely, [set_bits] contains the bits that were cleared in [lb] and
     got set in [r]. *)
  let r = Z.logor b.bits_set (Z.logand lb b.bits_unk) in
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
    let cleared_can_set =
      Z.logand (Z.lognot r) (Z.logor b.bits_set b.bits_unk)
    in
    let bit_to_set = left_cl_can_set bit_to_clear cleared_can_set in
    let r = Z.logor r Z.(~$1 lsl bit_to_set) in
    let mask  = Z.(minus_one lsl bit_to_set) in
    Z.logand r @@ Z.logor mask b.bits_set
  )

let decrease_upper_bound b ub =
  (* x <= ub <-> ~ub <= ~x *)
  Z.lognot @@ increase_lower_bound (lognot b) (Z.lognot ub)

let fold_domain f b acc =
  (* If [bits_unk] is negative, the domain is infinite. *)
  if Z.sign b.bits_unk < 0 then
    invalid_arg "Bitlist.fold_domain";
  let width = Z.numbits b.bits_unk in
  let rec fold_domain_aux ofs b acc =
    if ofs >= width then (
      assert (is_fully_known b);
      f (value b) acc
    ) else if not (Z.testbit b.bits_unk ofs) then
      fold_domain_aux (ofs + 1) b acc
    else
      let mask = Z.(one lsl ofs) in
      let bits_unk = Z.logand b.bits_unk (Z.lognot mask) in
      let acc =
        fold_domain_aux
          (ofs + 1) { b with bits_unk } acc
      in
      fold_domain_aux
        (ofs + 1) { b with bits_unk; bits_set = Z.logor b.bits_set mask } acc
  in
  fold_domain_aux 0 b acc

let shift_left a n =
  { bits_set = Z.(a.bits_set lsl n)
  ; bits_unk = Z.(a.bits_unk lsl n)
  ; ex = a.ex
  }

let ( lsl ) = shift_left

let shift_right a n =
  { bits_set = Z.(a.bits_set asr n)
  ; bits_unk = Z.(a.bits_unk asr n)
  ; ex = a.ex
  }

let ( asr ) = shift_right

(* simple propagator: only compute known low bits

   example: ???100 * ???000 = ?00000 (trailing zeroes accumulate)
            ???111 * ????11 = ????01 (min of low bits known) *)
let mul a b =
  let ex = Ex.union (explanation a) (explanation b) in

  (* (a * 2^n) * (b * 2^m) = (a * b) * 2^(n + m) *)
  let zeroes_a = Z.trailing_zeros @@ Z.logor a.bits_set a.bits_unk in
  let zeroes_b = Z.trailing_zeros @@ Z.logor b.bits_set b.bits_unk in
  if zeroes_a = max_int || zeroes_b = max_int then
    zero ex
  else
    let a = a asr zeroes_a in
    let b = b asr zeroes_b in
    let zeroes = zeroes_a + zeroes_b in
    (* a = ah * 2^n + al (0 <= al < 2^n)
       b = bh * 2^m + bl (0 <= bl < 2^m)

       ((ah * 2^n) + al) * ((bh * 2^m) + bl) =
        al * bl  (mod 2^(min n m)) *)
    let low_a_known = Z.trailing_zeros @@ a.bits_unk in
    let low_b_known = Z.trailing_zeros @@ b.bits_unk in
    let low_known = min low_a_known low_b_known in
    let mid_bits = Z.(value a * value b) in
    let mid_bits =
      if low_known = max_int then mid_bits
      else if low_known = 0 then Z.zero
      else Z.extract mid_bits 0 low_known
    in
    if low_known = max_int then
      exact Z.(mid_bits lsl zeroes) ex
    else
      (* High bits are unknown *)
      { bits_set = Z.(mid_bits lsl zeroes)
      ; bits_unk = Z.(minus_one lsl Stdlib.(low_known + zeroes))
      ; ex }

let bvshl ~size:sz a b =
  (* If the minimum value for [b] is larger than the bitwidth, the result is
     zero.

     Otherwise, any low zero bit in [a] is also a zero bit in the result, and
     the minimum value for [b] also accounts for that many minimum zeros (e.g.
     ?000 shifted by at least 2 has at least 5 low zeroes).

     NB: [increase_lower_bound b Z.zero] is the smallest positive integer that
     matches the bitlist pattern, and so is a lower bound. Ideally we would
     like to use the lower bound from the interval domain for [b] instead. *)
  match Z.to_int (increase_lower_bound b Z.zero) with
  | n when n < sz ->
    let low_zeros = Z.trailing_zeros @@ Z.logor a.bits_set a.bits_unk in
    if low_zeros + n >= sz then
      extract (exact Z.zero (Ex.union (explanation a) (explanation b))) 0 sz
    else if low_zeros + n > 0 then
      ((extract unknown 0 (sz - low_zeros - n)) lsl (low_zeros + n)) lor
      extract
        (exact Z.zero (Ex.union (explanation a) (explanation b)))
        0 (low_zeros + n)
    else
      extract unknown 0 sz
  | _ | exception Z.Overflow ->
    constant Z.zero (explanation b)

let bvlshr ~size:sz a b =
  (* If the minimum value for [b] is larger than the bitwidth, the result is
     zero.

     Otherwise, any high zero bit in [a] is also a zero bit in the result, and
     the minimum value for [b] also accounts for that many minimum zeros (e.g.
     000??? shifted by at least 2 is 00000?).

     NB: [increase_lower_bound b Z.zero] is the smallest positive integer that
     matches the bitlist pattern, and so is a lower bound. Ideally we would
     like to use the lower bound from the interval domain for [b] instead. *)
  match Z.to_int (increase_lower_bound b Z.zero) with
  | n when n < sz ->
    if not (Z.testbit a.bits_unk (sz - 1) || Z.testbit a.bits_set (sz - 1))
    then (* MSB is zero *)
      let low_msb_zero =
        Z.numbits @@ Z.extract (Z.logor a.bits_set a.bits_unk) 0 sz
      in
      let nb_msb_zeros = sz - low_msb_zero in
      assert (nb_msb_zeros > 0);
      let nb_zeros = nb_msb_zeros + n in
      if nb_zeros >= sz then
        constant Z.zero (Ex.union (explanation a) (explanation b))
      else
        (
          constant Z.zero (Ex.union (explanation a) (explanation b))
          lsl (sz - nb_zeros)
        ) lor (extract unknown 0 (sz - nb_zeros))
    else if n > 0 then
      (constant Z.zero (explanation b) lsl (sz - n)) lor
      extract unknown 0 (sz - n)
    else
      extract unknown 0 sz
  | _ | exception Z.Overflow ->
    constant Z.zero (explanation b)

let add a b =
  (* The implementation below is a bit magical, so let us draft a proof
     of correctness.

     Remark 1: A binary addition [x + y] has a carry at bit position [i] iff
       the addition of the lower bits of [x] and [y] overflows. In other words,
       addition [x + y] has a carry at bit position [i] iff:

         {math x \bmod 2^i + y \bmod 2^i > 2^i}

     Remark 2: Flipping bits from [0] to [1] in the operands of a binary
       addition can only introduce new carry positions but never remove them.
       This follows from Remark 1 since flipping bit [j] from [0] to [1] adds
       [2^j] to the value, and hence either increases or does not change the
       value of [x \bmod 2^i] in the inequality above, depending on whether
       [j < i] or [j >= i] holds.

     For a bitlist [b], let us write {m m_b} the value [a.bits_set] and {m M_b}
     the value [a.bits_set + a.bits_unk].

     Definition: We say that a bit position [i] is {e known} in a set {m S}
       (not necessarily a bitlist) if has the same value for all the integers
       in {m S}.

     Theorem: If [a] and [b] are bitlists, let us denote by [a + b] the set
       {m \{ x + y \mid x \in a, y \in b \}}. Then, a bit position [i] is known
       in [a + b] iff it is known in both [a] and [b], and the values
       {m m_a + m_b} and {M_a + M_b} agree on bit [i].

     Proof (implication): Consider a bit position [i] that is known in [a + b].
       It must be known in both [a] and [b], otherwise we could flip bit [i] and
       still obtain a value in [a + b]. Moreover, since {m m_a + m_b} and
       {m M_a + M_b} is in [a + b], they must agree on bit position [i].

     Proof (reverse implication): Consider a bit position [i] that is known in
       [a] and in [b], and where {m m_a + m_b} and {m M_a + M_b} agree.
       Assume that we have {m x \in a} and {m y \in b} such that {m x + y}
       disagree with {m M_a + M_b} on bit position [i].

       Since bit [i] is known in both [a] and [b], the only difference at bit
       position [i] between {m m_a + m_b} and {m x + y} can come from one
       having a carry and not the other.

       Since [a] and [b] are bitlists, we can obtain {m x \bmod 2^i} (resp.
       {m y \bmod 2^i}) by flipping bits from [0] to [1] in {m m_a} (resp.
       {m m_a}), and we can obtain {m M_a} (resp. {m M_B})by flipping bits from
       [0] to [1] in {m x \bmod 2^i} (resp. {m y \bmod 2^i}).

       Hence, by remark 2, if {m m_a + m_b} has a carry at position [i], then
       so do {m x + y} and {m M_a + M_b}; conversely, if {m M_a + M_b} has no
       carry at position [i], then neither do {m x + y} and {m m_a + m_b}. *)
  let min_add = Z.(a.bits_set + b.bits_set) in
  let max_add = Z.(min_add + a.bits_unk + b.bits_unk) in
  let bits_unk =
    Z.(a.bits_unk lor b.bits_unk lor (min_add lxor max_add))
  in
  let bits_set = Z.(min_add land ~!bits_unk) in
  { bits_unk ; bits_set ; ex = Ex.union a.ex b.ex }

let sub a b =
  (* We can prove the correctness of subtraction by re-using the proof of
     correctness for addition.

     Recall that [x - y] is [x + ~y + 1] and remark that:

       {math x + y + 1 = ((2x + 1) + (2y + 1)) / 2}

     From this last remark, we can apply the same reasoning for [a + b + 1] as
     for [a + b], and get that the unknown bits in [a + b + 1] are either
     unknown in [a], unknown in [b], or differ in [a.bits_set + b.bits_set + 1]
     and in [a.bits_set + a.bits_unk + b.bits_set + b.bits_unk + 1].

     Recalling [(~b).bits_set = ~(b.bits_set | b.bits_unk)], we get the formula
     below. *)
  let set_sub = Z.(a.bits_set - b.bits_set)in
  let min_sub = Z.(set_sub + a.bits_unk) in
  let max_sub = Z.(set_sub - b.bits_unk) in
  let bits_unk =
    Z.(a.bits_unk lor b.bits_unk lor (min_sub lxor max_sub))
  in
  let bits_set = Z.(set_sub land ~!bits_unk) in
  { bits_unk ; bits_set ; ex = Ex.union a.ex b.ex }
