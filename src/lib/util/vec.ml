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

type 'a t =
  { mutable data : 'a array;
    mutable sz : int;
    dummy : 'a
  }

let[@inline] size vec = vec.sz

let make n ~dummy = { data = Array.make n dummy; sz = 0; dummy }

let[@inline] create ~dummy = { data = [||]; sz = 0; dummy }

let[@inline] clear vec =
  for i = 0 to size vec - 1 do
    Array.unsafe_set vec.data i vec.dummy
  done;
  vec.sz <- 0

let[@inline] shrink vec i =
  assert (i >= 0);
  assert (i <= vec.sz);
  for j = i to vec.sz - 1 do
    Array.unsafe_set vec.data j vec.dummy
  done;
  vec.sz <- i

let[@inline] pop vec =
  assert (vec.sz > 0);
  let x = Array.unsafe_get vec.data (vec.sz - 1) in
  Array.unsafe_set vec.data (vec.sz - 1) vec.dummy;
  vec.sz <- vec.sz - 1;
  x

let[@inline] last vec =
  assert (vec.sz > 0);
  Array.unsafe_get vec.data (vec.sz - 1)

let[@inline] is_empty vec = vec.sz = 0

let[@inline] is_full vec = Array.length vec.data = vec.sz

let[@inline] copy vec : _ t =
  let data = Array.copy vec.data in
  { vec with data }

(* grow the array *)

let[@inline never] grow_to vec cap : unit =
  assert (Array.length vec.data < Sys.max_array_length);
  let cap = min Sys.max_array_length (max 4 cap) in
  assert (cap > vec.sz);
  let arr' = Array.make cap vec.dummy in
  assert (Array.length arr' > vec.sz);
  Array.blit vec.data 0 arr' 0 (Array.length vec.data);
  vec.data <- arr'

let[@inline never] grow_to_double_size vec : unit =
  grow_to vec (2 * Array.length vec.data)

let[@inline never] grow_to_by_double vec cap =
  let len = Array.length vec.data in
  if cap > len
  then begin
    let c = ref (max 1 len) in
    while !c < cap do
      c := 2 * !c
    done;
    grow_to vec !c
  end

let[@inline] push vec x : unit =
  if is_full vec then grow_to_double_size vec;
  Array.unsafe_set vec.data vec.sz x;
  vec.sz <- vec.sz + 1

let[@inline] get vec i =
  assert (0 <= i && i < vec.sz);
  Array.unsafe_get vec.data i

let[@inline] set vec i elt =
  vec.data.(i) <- elt;
  vec.sz <- max vec.sz (i + 1)

let[@inline] replace f vec i =
  assert (0 <= i && i < vec.sz);
  let n = Array.unsafe_get vec.data i in
  Array.unsafe_set vec.data i (f n)

let[@inline] fast_remove vec i =
  assert (i >= 0 && i < vec.sz);
  Array.unsafe_set vec.data i @@ Array.unsafe_get vec.data (vec.sz - 1);
  Array.unsafe_set vec.data (vec.sz - 1) vec.dummy;
  vec.sz <- vec.sz - 1

let filter_in_place f vec =
  let i = ref 0 in
  while !i < size vec do
    if f (Array.unsafe_get vec.data !i) then incr i else fast_remove vec !i
  done

let[@inline] iteri f vec =
  for i = 0 to size vec - 1 do
    f i @@ Array.unsafe_get vec.data i
  done

let[@inline] iter f vec =
  for i = 0 to vec.sz - 1 do
    f (Array.unsafe_get vec.data i)
  done

let exists p { data; sz; _ } =
  let rec aux i = i < sz && (p (Array.unsafe_get data i) || aux (i + 1)) in
  aux 0

let for_all p { data; sz; _ } =
  let rec aux i = i >= sz || (p (Array.unsafe_get data i) && aux (i + 1)) in
  aux 0

let fold f acc vec =
  let acc = ref acc in
  iter (fun elt -> acc := f !acc elt) vec;
  !acc

let to_array a = Array.sub a.data 0 a.sz

let to_list { data; sz; _ } =
  let l = ref [] in
  for i = sz - 1 downto 0 do
    l := Array.unsafe_get data i :: !l
  done;
  !l

let to_rev_list { data; sz; _ } =
  let l = ref [] in
  for i = 0 to sz - 1 do
    l := Array.unsafe_get data i :: !l
  done;
  !l

let of_list l ~dummy : _ t =
  let data = Array.of_list l in
  { data; sz = Array.length data; dummy }

let sort vec f : unit =
  let arr = to_array vec in
  Array.fast_sort f arr;
  vec.data <- arr

let pp pp_elt = Fmt.iter ~sep:Fmt.comma iter pp_elt |> Fmt.box
