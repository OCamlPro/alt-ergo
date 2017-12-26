(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Options

type 'a t = { mutable dummy: 'a; mutable data : 'a array; mutable sz : int }

let make capa d = {data = Array.make capa d; sz = 0; dummy = d}

let init capa f d =
  {data = Array.init capa (fun i -> f i); sz = capa; dummy = d}

let from_array data sz d = {data = data; sz = sz; dummy = d}

let from_list l sz d =
  let l = ref l in
  let f_init i = match !l with [] -> assert false | e::r -> l := r; e in
  {data = Array.init sz f_init; sz = sz; dummy = d}

let clear s = s.sz <- 0

let shrink t i fill_with_dummy =
  assert (i >= 0 && i<=t.sz);
  if fill_with_dummy then
    for i = t.sz - i to t.sz - 1 do
      t.data.(i) <- t.dummy
    done;
  t.sz <- t.sz - i

let pop t = assert (t.sz >=1); t.sz <- t.sz - 1

let size t = t.sz

let is_empty t = t.sz = 0

let grow_to t new_capa =
  let data = t.data in
  let capa = Array.length data in
  if new_capa > capa then
    t.data <-
      Array.init new_capa
      (fun i -> if i < capa then data.(i) else t.dummy)

let grow_to_double_size t =
  let n = max 1 (Array.length t.data) in grow_to t (2 * n)

let grow_to_by_double t new_capa =
  let new_capa = max 1 new_capa in
  let data = t.data in
  let capa = ref (max 1 (Array.length data)) in
  while !capa < new_capa do capa := 2 * !capa done;
  grow_to t !capa


let is_full t = Array.length t.data = t.sz

let push t e =
  (*Format.eprintf "push; sz = %d et capa=%d@." t.sz (Array.length t.data);*)
  if is_full t then grow_to_double_size t;
  t.data.(t.sz) <- e;
  t.sz <- t.sz + 1

let push_none t =
  if is_full t then grow_to_double_size t;
  t.data.(t.sz) <- t.dummy;
  t.sz <- t.sz + 1

let last t =
  let e = t.data.(t.sz - 1) in
  assert (not (e == t.dummy));
  e

let get t i =
  assert (i < t.sz);
  let e = t.data.(i) in
  if e == t.dummy then raise Not_found
  else e

let set t i v =
  t.data.(i) <- v;
  t.sz <- max t.sz (i + 1)

let set_size t sz = t.sz <- sz

let copy t =
  let data = t.data in
  let len = Array.length data in
  let data = Array.init len (fun i -> data.(i)) in
  { data=data; sz=t.sz; dummy = t.dummy }

let move_to t t' =
  let data = t.data in
  let len = Array.length data in
  let data = Array.init len (fun i -> data.(i)) in
  t'.data <- data;
  t'.sz <- t.sz


let remove t e =
  let j = ref 0 in
  while (!j < t.sz && not (t.data.(!j) == e)) do incr j done;
  assert (!j < t.sz);
  for i = !j to t.sz - 2 do t.data.(i) <- t.data.(i+1) done;
  pop t


let fast_remove t e =
  let j = ref 0 in
  while (!j < t.sz && not (t.data.(!j) == e)) do incr j done;
  assert (!j < t.sz);
  t.data.(!j) <- last t;
  pop t


let sort t f =
  let sub_arr = Array.sub t.data 0 t.sz in
  Array.fast_sort f sub_arr;
  t.data <- sub_arr

let iter vec f =
  for i = 0 to size vec - 1 do
    f (get vec i)
  done
(*
template<class V, class T>
static inline void remove(V& ts, const T& t)
{
    int j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    assert(j < ts.size());
    ts[j] = ts.last();
    ts.pop();
}
#endif

template<class V, class T>
static inline bool find(V& ts, const T& t)
{
    int j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    return j < ts.size();
}

#endif
*)
