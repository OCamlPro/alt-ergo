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

type exn_printer = Format.formatter -> exn -> unit
(* an [exn_printer] is a formatter of exception which prints on the
   given formatter a message for the user if it knows the given
   exception. Otherwise it raises the exception *)

val register : exn_printer -> unit
(* Register a formatter of exception *)

val exn_printer : exn_printer
(* [exn_printer fmt exn] prints exception [exn] using all previously
   registered printers and returns *)
