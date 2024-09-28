(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2022-2024 --- OCamlPro SAS                           *)
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

type t
(** Type of model. *)

type profile = Uid.term_cst * Ty.t list * Ty.t
(** Typed identifier of function. In order:
    - The identifier.
    - Types of its arguments.
    - The returned type. *)

val add : profile -> Expr.t list -> Expr.t -> t -> t
(** [add sy args ret mdl] adds the binding [args -> ret] to the partial graph
    associated with the symbol [sy]. *)

val empty : suspicious:bool -> profile list -> t
(** An empty model. The [suspicious] flag is used to remember that this
    model may be wrong as it involves symbols from theories for which the
    model generation is known to be incomplete. *)

val subst : profile -> Expr.t -> t -> t
(** [subst id e mdl] substitutes all the occurrences of the identifier [id]
    in the model [mdl] by the model term [e].

    @Raise Error if the expression [e] is not a model term or the type of
           [e] doesn't agree with some occurrence of [id] in the model. *)

val pp : t Fmt.t
(** [pp ppf mdl] prints the model [mdl] on the formatter [ppf] using the
    SMT-LIB format. *)
