(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(* From stdlib Stack Module  *)
type 'a stackt = { mutable c : 'a list; mutable len : int; }

let create () = { c = []; len = 0; }

let iter f s = List.iter f s.c

let push x s = s.c <- x :: s.c; s.len <- s.len + 1



type exn_printer = Format.formatter -> exn -> unit

let exn_printers =
  (create () : (Format.formatter -> exn -> unit) stackt)

let register exn_printer = push exn_printer exn_printers

let () =
  let all_exn_printer fmt exn =
    Format.fprintf fmt "anomaly: %s" (Printexc.to_string exn) in
  register all_exn_printer

exception Exit_loop

let exn_printer fmt exn =
  let test f =
    try
      Format.fprintf fmt "@[%a@]" f exn;
      raise Exit_loop
    with
      | Exit_loop -> raise Exit_loop
      | _ -> ()
  in
  try iter test exn_printers
  with Exit_loop -> ()

