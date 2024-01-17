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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type t = Hstring.t [@@deriving ord]
val equal : t -> t -> bool
val show : t -> string
val pp : t Fmt.t

module Namespace : sig
  module type S = sig
    val fresh : ?base:string -> unit -> string
  end

  module Internal : S
  module Skolem : S
  module Abstract : S
  module GetValue : S

  val reinit : unit -> unit
  (** Resets the [fresh_internal_name], [fresh_skolem] and [fresh_abstract]
      counters. *)
end
