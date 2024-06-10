open AltErgoLib
open QCheck2

module type FixedSizeBitVector = sig
  type t = Bitlist.t

  val shl : t -> t -> t

  val lshr : t -> t -> t

  val mul : t -> t -> t
end

let fixed_size_bit_vector n : (module FixedSizeBitVector) =
  let open Bitlist in
  let norm b = extract b 0 n in
  let binop op x y = norm (op x y) in
  (module struct
    type t = Bitlist.t

    let shl a b = bvshl ~size:n a b

    let lshr a b = bvlshr ~size:n a b

    let mul = binop mul
  end)

module IntSet : sig
  type t

  val subset : t -> t -> bool

  val of_fold : ((Z.t -> t -> t) -> 'a -> t -> t) -> 'a -> t

  val map : (Z.t -> Z.t) -> t -> t

  val map2 : (Z.t -> Z.t -> Z.t) -> t -> t -> t

  val mem : Z.t -> t -> bool
end = struct
  type t = Z.t

  let empty = Z.zero

  let is_empty n = Z.equal n empty

  let singleton n =
    match Z.to_int n with
    | exception Z.Overflow -> invalid_arg "IntSet.singleton"
    | n -> Z.(one lsl n)

  let union = Z.(lor)

  let add n = union (singleton n)

  let subtract big small = Z.(big land (lognot small))

  let subset small big = is_empty (subtract small big)

  let mem n t =
    match Z.to_int n with
    | exception Z.Overflow -> invalid_arg "IntSet.mem"
    | n -> Z.testbit t n

  let fold f =
    let rec aux ofs n acc =
      let tz = Z.trailing_zeros n in
      if tz <> max_int then
        aux (ofs + tz + 1) Z.(n asr Stdlib.(tz + 1))
          (f (Z.of_int (ofs + tz)) acc)
      else
        acc
    in
    aux 0

  let of_fold fold elt = fold add elt empty

  let map f t =
    fold (fun n -> add (f n)) t empty

  let map2 f s t =
    fold (fun n ->
        fold (fun m ->
            add (f n m)
          ) t
      ) s empty
end

let finite_bound = function
  | Intervals_intf.Unbounded | Open _ -> assert false
  | Closed n -> n

let fold_finite_domain f int acc =
  Intervals.Int.fold (fun acc i ->
      let { Intervals_intf.lb ; ub } = Intervals.Int.Interval.view i in
      let lb = finite_bound lb and ub = finite_bound ub in
      let maxi = Z.(to_int @@ ub - lb) in
      let acc = ref acc in
      for i = 0 to maxi do
        acc := f Z.(lb + ~$i) !acc
      done;
      !acc
    ) acc int

let of_interval =
  IntSet.of_fold fold_finite_domain

let of_bitlist =
  IntSet.of_fold Bitlist.fold_domain

(* Generator for bit-vectors of size sz *)
let bitvec sz = Gen.(int_bound sz >|= Z.of_int)

(* Generator for a single interval bound *)
let interval sz =
  assert (sz < Sys.int_size);
  Gen.(
    int_range 0 (1 lsl sz - 1) >>= fun lb ->
    int_range lb (1 lsl sz - 1) >>= fun ub ->
    return
    @@ Intervals.Int.interval_set
    @@ Intervals.Int.Interval.of_bounds
      (Closed (Z.of_int lb)) (Closed (Z.of_int ub))
  )

(* Generator for an union of (possibly overlapping) intervals *)
let intervals sz =
  let open Gen in
  let rec intervals n =
    if n <= 0 then
      interval sz
    else
      let* i1 = interval sz in
      let* i2 = intervals (n - 1) in
      return @@ Intervals.Int.union_set i1 i2
  in
  small_nat >>= intervals >|= Intervals.Int.of_set_nonempty

(* Generator for a bitlist *)
let bitlist sz =
  assert (sz < Sys.int_size);
  let open Gen in
  let rec bitlist sz =
    if sz <= 0 then
      return (Z.zero, Z.zero)
    else
      let* known = bool in
      if known then
        let* (set_bits, clr_bits) = bitlist (sz - 1) in
        let mask = Z.shift_left Z.one (sz - 1) in
        let* is_set = bool in
        if is_set then
          return (Z.logor set_bits mask, clr_bits)
        else
          return (set_bits, Z.logor clr_bits mask)
      else
        bitlist (sz - 1)
  in
  let* (set_bits, clr_bits) = bitlist sz in
  let set_bits =
    Bitlist.extract (
      Bitlist.ones @@
      Bitlist.exact set_bits Explanation.empty
    ) 0 sz
  in
  let clr_bits =
    Bitlist.extract (
      Bitlist.zeroes @@
      Bitlist.exact (Z.extract (Z.lognot clr_bits) 0 sz) Explanation.empty
    ) 0 sz
  in
  return @@ Bitlist.intersect set_bits clr_bits

(* Generator for extraction indices *)
let subvec sz = Gen.(
    int_range 0 (sz - 1) >>= fun i ->
    int_range i (sz - 1) >>= fun j ->
    return (i, j)
  )

(* Check that [Intervals.extract] computes a correct overapproximation of
    the set of values obtained by the [extract] smt-lib function. *)
let test_extract sz =
  Test.make ~count:1_000
    ~print:Print.(pair (Fmt.to_to_string Intervals.Int.pp) (pair int int))
    Gen.(pair (intervals sz) (subvec sz))
    (fun (t, (i, j)) ->
       IntSet.subset
         (IntSet.map (fun n -> Z.extract n i (j - i + 1)) (of_interval t))
         (of_interval (Intervals.Int.extract t ~ofs:i ~len:(j - i + 1))))

let () =
  Test.check_exn (test_extract 3)

(* Check that [shared_msb w z1 z2] returns exactly the number of most
    significant bits that are shared between [z1] and [z2]. *)
let test_shared_msb sz =
  Test.make ~count:1_000
    ~print:Print.(
        pair (Fmt.to_to_string Z.pp_print) (Fmt.to_to_string Z.pp_print))
    Gen.(pair (bitvec sz) (bitvec sz))
    (fun (lb, ub) ->
       let lb, ub =
         if Z.compare lb ub > 0 then ub, lb else lb, ub
       in
       let shared = Bitv_rel.Test.shared_msb sz lb ub in
       Z.equal
         (Z.shift_right lb (sz - shared))
         (Z.shift_right ub (sz - shared)) &&
       (shared = sz || not @@ Z.equal
          (Z.shift_right lb (sz - shared - 1))
          (Z.shift_right ub (sz - shared - 1))))

let () =
  Test.check_exn (test_shared_msb 3)

let all_range start_ end_ f =
  try
    for i = start_ to end_ do
      if not (f i) then
        raise Exit
    done;
    true
  with Exit -> false

(* Check that [increase_lower_bound b n] returns the smallest value larger
   than [n] that matches [b]. Also check that if the [Not_found] exception is
   raised, no such value exists. *)
let test_increase_lower_bound sz =
  Test.make ~count:1_000
    ~print:Print.(
        pair (Fmt.to_to_string Bitlist.pp) (Fmt.to_to_string Z.pp_print))
    Gen.(pair (bitlist sz) (bitvec sz))
    (fun (bl, z) ->
       let set = of_bitlist bl in
       match Bitlist.increase_lower_bound bl z with
       | new_lb ->
         Z.numbits new_lb <= sz &&
         IntSet.mem new_lb set &&
         all_range (Z.to_int z) (Z.to_int new_lb - 1) @@ fun i ->
         not (IntSet.mem (Z.of_int i) set)
       | exception Not_found ->
         all_range (Z.to_int z) (sz - 1) @@ fun i ->
         not (IntSet.mem (Z.of_int i) set))

let () =
  Test.check_exn (test_increase_lower_bound 3)

(* Check that [decrease_upper_bound] returns the largest value smaller than [n]
   that matches [b]. Also check that if the [Not_found] exception is raised, no
   such value exists. *)
let test_decrease_upper_bound sz =
  Test.make ~count:1_000
    ~print:Print.(
        pair (Fmt.to_to_string Bitlist.pp) (Fmt.to_to_string Z.pp_print))
    Gen.(pair (bitlist sz) (bitvec sz))
    (fun (bl, z) ->
       let set = of_bitlist bl in
       match Bitlist.decrease_upper_bound bl z with
       | new_ub ->
         Z.numbits new_ub <= sz &&
         IntSet.mem new_ub set &&
         all_range (Z.to_int new_ub + 1) (Z.to_int z) @@ fun i ->
         not (IntSet.mem (Z.of_int i) set)
       | exception Not_found ->
         all_range 0 (Z.to_int z) @@ fun i ->
         not (IntSet.mem (Z.of_int i) set))

let () =
  Test.check_exn (test_decrease_upper_bound 3)

let test_bitlist_binop ~count sz zop bop =
  Test.make ~count
    ~print:Print.(
        pair
          (Fmt.to_to_string Bitlist.pp)
          (Fmt.to_to_string Bitlist.pp))
    Gen.(pair (bitlist sz) (bitlist sz))
    (fun (s, t) ->
       let u = bop (fixed_size_bit_vector sz) s t in
       IntSet.subset
         (IntSet.map2 zop (of_bitlist s) (of_bitlist t))
         (of_bitlist u))

let test_interval_binop ~count sz zop iop =
  Test.make ~count
    ~print:Print.(
        pair
          (Fmt.to_to_string Intervals.Int.pp)
          (Fmt.to_to_string Intervals.Int.pp))
    Gen.(pair (intervals sz) (intervals sz))
    (fun (s, t) ->
       IntSet.subset
         (IntSet.map2 zop (of_interval s) (of_interval t))
         (of_interval (iop s t)))

let zmul sz a b =
  Z.extract (Z.mul a b) 0 sz

let test_bitlist_mul sz =
  test_bitlist_binop ~count:1_000
    sz (zmul sz) (fun (module BV) -> BV.mul)

let () =
  Test.check_exn (test_bitlist_mul 3)

let zshl sz a b =
  match Z.to_int b with
  | b when b < sz -> Z.extract (Z.shift_left a b) 0 sz
  | _ | exception Z.Overflow -> Z.zero

let test_interval_shl sz =
  test_interval_binop ~count:1_000
    sz (zshl sz) (Intervals.Int.bvshl ~size:sz)

let () =
  Test.check_exn (test_interval_shl 3)

let test_bitlist_shl sz =
  test_bitlist_binop ~count:1_000
    sz (zshl sz) (fun (module BV) -> BV.shl)

let () =
  Test.check_exn (test_bitlist_shl 3)

let zlshr a b =
  match Z.to_int b with
  | b -> Z.shift_right a b
  | exception Z.Overflow -> Z.zero

let test_interval_lshr sz =
  test_interval_binop ~count:1_000
    sz zlshr Intervals.Int.lshr

let () =
  Test.check_exn (test_interval_lshr 3)

let test_bitlist_lshr sz =
  test_bitlist_binop ~count:1_000
    sz zlshr (fun (module BV) -> BV.lshr)

let () =
  Test.check_exn (test_bitlist_lshr 3)

let zudiv sz a b =
  if Z.equal b Z.zero then
    Z.extract Z.minus_one 0 sz
  else
    Z.div a b

let test_interval_bvudiv sz =
  test_interval_binop ~count:1_000
    sz (zudiv sz) (Intervals.Int.bvudiv ~size:sz)

let () =
  Test.check_exn (test_interval_bvudiv 3)

let zurem a b =
  if Z.equal b Z.zero then
    a
  else
    Z.rem a b

let test_interval_bvurem sz =
  test_interval_binop ~count:1_000
    sz zurem Intervals.Int.bvurem

let () =
  Test.check_exn (test_interval_bvurem 3)
