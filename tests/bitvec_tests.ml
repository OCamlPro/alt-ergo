open AltErgoLib
open QCheck2

module IntSet : sig
  type t

  val subset : t -> t -> bool

  val of_fold : ((Z.t -> t -> t) -> 'a -> t -> t) -> 'a -> t

  val map : (Z.t -> Z.t) -> t -> t

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
end

let of_interval =
  IntSet.of_fold Intervals.fold_finite_domain

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
    return @@
    Intervals.mk_closed
      (Q.of_int lb) (Q.of_int ub)
      true true
      Explanation.empty Explanation.empty
      Tint
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
      return @@ Intervals.merge i1 i2
  in
  small_nat >>= intervals

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
    Bitlist.ones @@ Bitlist.exact sz set_bits Explanation.empty
  in
  let clr_bits =
    Bitlist.zeroes @@ Bitlist.exact sz (Z.lognot clr_bits) Explanation.empty
  in
  return @@ Bitlist.intersect ~ex:Explanation.empty set_bits clr_bits

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
    ~print:Print.(pair (Fmt.to_to_string Intervals.pretty_print) (pair int int))
    Gen.(pair (intervals sz) (subvec sz))
    (fun (t, (i, j)) ->
       IntSet.subset
         (IntSet.map (fun n -> Z.extract n i (j - i + 1)) (of_interval t))
         (of_interval (Intervals.extract t i j)))

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
