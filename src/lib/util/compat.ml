(* Locally restore the default polymorphic operators of the Stdlib, to make it
   easier to copy code from there without modifications. *)
open Stdlib

module String = struct
  open Stdlib.String

  let starts_with ~prefix s =
    (* Copied from stdlib/string.ml in OCaml 5.0 *)
    let len_s = length s
    and len_pre = length prefix in
    let rec aux i =
      if i = len_pre then true
      else if unsafe_get s i <> unsafe_get prefix i then false
      else aux (i + 1)
    in len_s >= len_pre && aux 0

  let fold_left f x a =
    (* Copied from stdlib/bytes.ml in OCaml 5.0 *)
    let r = ref x in
    for i = 0 to length a - 1 do
      r := f !r (unsafe_get a i)
    done;
    !r
end

module Seq = struct
  type 'a t = 'a Stdlib.Seq.t

  open Stdlib.Seq

  let rec append xs ys () =
    match xs () with
    | Nil -> ys ()
    | Cons (x, xs) -> Cons (x, append xs ys)
end
