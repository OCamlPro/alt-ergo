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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

val src : Logs.src

type t

type r = Shostak.Combine.r

val print : t Fmt.t

val empty : t

type parents
(** Collect the parent terms and literals of a term, represented by its
    [Uf.make]. *)

val no_parents : parents

val congr_close_up : t -> r -> parents -> parents
(** [congr_close_up t r up] adds the parents of [r], if any, to [up]. *)

val up_close_up :
  t -> Uf.t -> parents -> t * Expr.t Expr.Map.t * Explanation.t Expr.Map.t
(** [up_close_up t uf up] returns [t', up_eqs, up_lits] where:

    - [t'] is [t] after normalizing the terms in [up] with respect to [uf];

    - [up_eqs] contains bindings [e -> e'] if [e] and [e'] were tracked with the
      same head symbol and type and have now become congruent. [e] is no longer
      tracked.

    - [up_lits] contains all the literals added through [add_literal], along
      with their explanation, that appear in [up]. *)

val add_term : t -> Uf.t -> Expr.t -> Expr.t Expr.Map.t -> t * Expr.t Expr.Map.t
(** [add_term t uf e eqs] returns [t', new_eqs] where:

    - If there is already a term [e'], added to [t] earlier, that is congruent
      to [e] according to [uf], then [t'] is [t] and [new_eqs] is
      [Expr.Map.add e e' eqs].

    - Otherwise, [new_eqs] is [eqs] and [t'] tracks congruence changes to [e]
      when its arguments change representative ([e] will appear in the
      [congr_close_up] of any of its arguments). *)

val add_literal : t -> Uf.t -> Expr.t -> Explanation.t -> t
(** [add_literal t uf a ex] tracks the change of representatives for the
    arguments of literal [a] ([a] will appear in the [congr_close_up] of any of
    its arguments).

    {b Precondition}: [a] must be a literal. *)

val remove_literal : t -> Uf.t -> Expr.t -> t
(** [remove_literal t uf a] stops tracking change of representatives for the
    arguments of literal [a].

    {b Precondition}: [a] must be a literal. *)
