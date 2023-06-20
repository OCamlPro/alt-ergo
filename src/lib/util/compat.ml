module String = struct
  open Stdlib.String

  let starts_with ~prefix s =
    length s >= length prefix &&
    equal (sub s 0 (length prefix)) prefix
end

module Seq = struct
  type 'a t = 'a Stdlib.Seq.t

  open Stdlib.Seq

  let rec append xs ys () =
    match xs () with
    | Nil -> ys ()
    | Cons (x, xs) -> Cons (x, append xs ys)
end
