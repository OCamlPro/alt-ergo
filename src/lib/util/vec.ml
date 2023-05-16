(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

type 'a t = {
  mutable data : 'a array;
  mutable sz : int;
  dummy: 'a;
}

let make n ~dummy = {data = Array.make n dummy; sz = 0; dummy}

let[@inline] create ~dummy = {data = [||]; sz = 0; dummy}

let[@inline] clear vec = vec.sz <- 0

let[@inline] shrink vec i =
  assert (i >= 0);
  assert (i <= vec.sz);
  for j = vec.sz - i to vec.sz - 1 do
    Array.unsafe_set vec.data j vec.dummy
  done;
  vec.sz <- vec.sz - i

let[@inline] pop vec =
  assert (vec.sz > 0);
  let x = Array.unsafe_get vec.data (vec.sz - 1) in
  Array.unsafe_set vec.data (vec.sz - 1) vec.dummy;
  vec.sz <- vec.sz - 1;
  x

let[@inline] last vec =
  assert (vec.sz > 0);
  Array.unsafe_get vec.data (vec.sz - 1)

let[@inline] size vec = vec.sz

let[@inline] is_empty vec = vec.sz = 0

let[@inline] is_full vec = Array.length vec.data = vec.sz

let[@inline] copy vec : _ t =
  let data = Array.copy vec.data in
  {vec with data}

(* grow the array *)

let[@inline never] grow_to vec cap : unit =
  assert (Array.length vec.data < Sys.max_array_length);
  let cap =
    min Sys.max_array_length (max 4 cap)
  in
  let arr' = Array.make cap vec.dummy in
  Array.blit vec.data 0 arr' 0 (Array.length vec.data);
  vec.data <- arr';
  assert (Array.length vec.data > vec.sz);
  ()

let[@inline never] grow_to_double_size vec : unit =
  grow_to vec (2 * Array.length vec.data)

let[@inline never] grow_to_by_double vec cap =
  let cap = max 1 cap in
  let c = ref (max 1 (Array.length vec.data)) in
  while !c < cap do c := 2 * !c done;
  grow_to vec !c

let[@inline] push vec x : unit =
  if is_full vec then grow_to_double_size vec;
  Array.unsafe_set vec.data vec.sz x;
  vec.sz <- vec.sz + 1

let[@inline] get vec i =
  assert (0 <= i && i < vec.sz);
  let res = Array.unsafe_get vec.data i  in
  if res == vec.dummy then raise Not_found;
  res

let[@inline] set vec i elt =
  assert (not (elt == vec.dummy));
  vec.data.(i) <- elt;
  vec.sz <- max vec.sz (i+1)

let[@inline] fast_remove vec i =
  assert (i>= 0 && i < vec.sz);
  Array.unsafe_set vec.data i @@ Array.unsafe_get vec.data (vec.sz - 1);
  vec.sz <- vec.sz - 1

let filter_in_place f vec =
  let i = ref 0 in
  while !i < size vec do
    if f (Array.unsafe_get vec.data !i) then incr i else fast_remove vec !i
  done

let sort vec f : unit =
  let sub_arr =
    if is_full vec then vec.data else Array.sub vec.data 0 vec.sz
  in
  Array.fast_sort f sub_arr;
  vec.data <- sub_arr

let[@inline] iteri f vec =
  for i = 0 to size vec - 1 do
    let elt = Array.unsafe_get vec.data i in
    if not (elt == vec.dummy) then
      f i elt
  done

let[@inline] iter f = iteri (fun _ elt -> f elt)

let exists p vec =
  let exception Terminate in
  try
    for i = 0 to size vec - 1 do
      let elt = Array.unsafe_get vec.data i in
      if p elt && not (elt == vec.dummy) then raise Terminate
    done;
    false
  with Terminate -> true

let for_all p vec = not @@ exists (fun x -> not @@ p x) vec

let fold f acc vec =
  let acc = ref acc in
  for i = 0 to size vec - 1 do
    let elt = Array.unsafe_get vec.data i in
    if not (elt == vec.dummy) then
      acc := f !acc elt
  done;
  !acc

let to_list a = Array.to_seq a.data |> List.of_seq
let to_array a = Array.sub a.data 0 a.sz

let of_list l ~dummy : _ t =
  match l with
  | [] -> create ~dummy
  | _ :: tl ->
    let v = make (List.length tl+1) ~dummy in
    List.iter (push v) l;
    v

let pp ?(sep=", ") pp fmt a =
  let pp_sep fmt () = Format.fprintf fmt "%s@," sep in
  Format.pp_print_list ~pp_sep pp fmt (to_list a)
