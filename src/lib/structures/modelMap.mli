(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type t
(** Type of model. *)

module Graph : sig
  type t

  val is_constant : t -> bool
  val iter : (Expr.t list -> Expr.t -> unit) -> t -> unit
  val pp : t Fmt.t
end

val add : Symbols.typed_name -> Expr.t list -> Expr.t -> t -> t
(** [add sy args ret mdl] adds the binding [args -> ret] to the partial graph
    associated with the symbol [sy]. *)

val iter : (Symbols.typed_name -> Graph.t -> unit) -> t -> unit
(** [iter f mdl] iterates over all the graphs of the model [mdl]. *)

val get_value : Symbols.typed_name -> Expr.t list -> t -> Expr.t option
(** [get_value f args mdl] returns the value of the declared name [f]
    evaluates to the arguments [args] in the model [mdl].

    @return [None] if the model [mdl] doesn't contain a definition for the
            name [f]. *)

val empty : suspicious:bool -> Symbols.typed_name list -> t
(** An empty model. The [suspicious] flag is used to remember that this
    model may be wrong as it involves symbols from theories for which the
    model generation is known to be incomplete. *)

val subst : Symbols.Name.t -> Expr.t -> t -> t
(** [subst id e mdl] substitutes all the occurrences of the identifier [id]
    in the model [mdl] by the model term [e].

    @Raise Error if the expression [e] is not a model term or the type of
           [e] doesn't agree with some occurrence of [id] in the model. *)

val pp : t Fmt.t
(** [pp ppf mdl] prints the model [mdl] on the formatter [ppf] using the
    SMT-LIB format. *)
