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

type 'a record_def = (Hstring.t * 'a) list
(* A record definition. More precisely, the list [[(lb; r); ...]] corresponds
   to the record definition { lb = x; ... } where [r] are the alien semantic
   values associated with [x]. *)

type 'a abstract = private
  | Constr of
      { c_name : Hstring.t ; c_ty : Ty.t ; c_args : 'a record_def }
  (** [Constr (name, ty, args)] corresponds to an application of the constructor
      [name] of type [ty] on the arguments [args]. *)

  | Select of { d_name : Hstring.t ; d_ty : Ty.t ; d_arg : 'a }
  (** [Select (name, ty, arg)] corresponds to a projection of the adt [arg]
      of type [ty] along the destructor [name]. *)

  | Tester of { t_name : Hstring.t ; t_arg : 'a }
  (** [Tester (name, arg)] corresponds to a tester of the presence of
      the constructor [name] in the adt [arg]. Tester is currently not used to
      build semantic values. *)

  | Alien of 'a
  (** [Alien r] corresponds to an uninterpreted term of type adt. *)
(** Type of the ADT semantic values.
    The type parameter 'a denotes the type of alien semantic values. *)

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak
    (X : ALIEN) : Sig.SHOSTAK with type r = X.r and type t = X.r abstract
