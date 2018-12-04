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

type t

type view = {hs : Hstring.t ; id : int}

val of_hstring : Hstring.t -> t
val of_string  : string -> t

val view : t -> view

val compare : t -> t -> int

val equal : t -> t -> bool

val hash : t -> int

val print : Format.formatter -> t -> unit

val to_string : t -> string

module Map : Map.S with type key = t

module Set : Set.S with type elt = t

