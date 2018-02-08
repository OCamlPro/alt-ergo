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

(** Logic Why3_declarations *)
(*
open Why3_ident
open Ty
open Term

(** {2 Type declaration} *)

type constructor = lsymbol * lsymbol option list
(** constructor symbol with the list of projections *)

type data_decl = tysymbol * constructor list

(** {2 Logic symbols declaration} *)

type ls_defn

type logic_decl = lsymbol * ls_defn

val make_ls_defn : lsymbol -> vsymbol list -> term -> logic_decl

val open_ls_defn : ls_defn -> vsymbol list * term

val open_ls_defn_cb : ls_defn -> vsymbol list * term *
                    (lsymbol -> vsymbol list -> term -> logic_decl)

val ls_defn_axiom : ls_defn -> term

val ls_defn_of_axiom : term -> logic_decl option
(** tries to reconstruct a definition from a defining axiom. Do not apply
    this to recursive definitions: it may successfully build a logic_decl,
    which will fail later because of non-assured termination *)

val ls_defn_decrease : ls_defn -> int list
(** [ls_defn_decrease ld] returns a list of argument positions
    (numbered from 0) that ensures a lexicographical structural
    descent for every recursive call. Triggers are ignored.

    NOTE: This is only meaningful if the [ls_defn] comes
    from a declaration; on the result of [make_ls_defn],
    [ls_defn_decrease] will always return an empty list. *)

(** {2 Proposition names} *)

type prsymbol = private {
  pr_name : ident;
}

module Mpr : Extmap.S with type key = prsymbol
module Spr : Extset.S with module M = Mpr
module Hpr : Exthtbl.S with type key = prsymbol
module Wpr : Weakhtbl.S with type key = prsymbol

val create_prsymbol : preid -> prsymbol

val pr_equal : prsymbol -> prsymbol -> bool

val pr_hash : prsymbol -> int

(** {2 Inductive predicate declaration} *)

type ind_decl = lsymbol * (prsymbol * term) list
 *)
type ind_sign = Ind | Coind
(*
type ind_list = ind_sign * ind_decl list
 *)
(** {2 Proposition declaration} *)

type prop_kind =
  | Plemma    (** prove, use as a premise *)
  | Paxiom    (** do not prove, use as a premise *)
  | Pgoal     (** prove, do not use as a premise *)
  | Pskip     (** do not prove, do not use as a premise *)
(*
type prop_decl = prop_kind * prsymbol * term

(** {2 Why3_declaration type} *)

type decl = private {
  d_node : decl_node;
  d_syms : Sid.t;         (** idents used in declaration *)
  d_news : Sid.t;         (** idents introduced in declaration *)
  d_tag  : Weakhtbl.tag;  (** unique magical tag *)
}

and decl_node = private
  | Dtype  of tysymbol          (** abstract types and aliases *)
  | Ddata  of data_decl list    (** recursive algebraic types *)
  | Dparam of lsymbol           (** abstract functions and predicates *)
  | Dlogic of logic_decl list   (** defined functions and predicates (possibly recursively) *)
  | Dind   of ind_list          (** (co)inductive predicates *)
  | Dprop  of prop_decl         (** axiom / lemma / goal *)

module Mdecl : Extmap.S with type key = decl
module Sdecl : Extset.S with module M = Mdecl
module Wdecl : Weakhtbl.S with type key = decl
module Hdecl : Exthtbl.S with type key = decl

val d_equal : decl -> decl -> bool
val d_hash : decl -> int

(** {2 Why3_declaration constructors} *)

val create_ty_decl : tysymbol -> decl
val create_data_decl : data_decl list -> decl
val create_param_decl : lsymbol -> decl
val create_logic_decl : logic_decl list -> decl
val create_ind_decl : ind_sign -> ind_decl list -> decl
val create_prop_decl : prop_kind -> prsymbol -> term -> decl

(* {2 Exceptions} *)

exception IllegalTypeAlias of tysymbol
exception NonPositiveTypeWhy3_decl of tysymbol * lsymbol * ty

exception InvalidIndWhy3_decl of lsymbol * prsymbol
exception NonPositiveIndWhy3_decl of lsymbol * prsymbol * lsymbol

exception NoTerminationProof of lsymbol
exception BadLogicWhy3_decl of lsymbol * lsymbol
exception UnboundVar of vsymbol
exception ClashWhy3_ident of ident

exception EmptyWhy3_decl
exception EmptyAlgWhy3_decl of tysymbol
exception EmptyIndWhy3_decl of lsymbol

exception BadConstructor of lsymbol
exception BadRecordField of lsymbol
exception RecordFieldMissing of lsymbol * lsymbol
exception DuplicateRecordField of lsymbol * lsymbol

(** {2 Utilities} *)

val decl_map : (term -> term) -> decl -> decl

val decl_fold : ('a -> term -> 'a) -> 'a -> decl -> 'a

val decl_map_fold : ('a -> term -> 'a * term) -> 'a -> decl -> 'a * decl

module Why3_declTF : sig

  val decl_map : (term -> term) -> (term -> term) -> decl -> decl

  val decl_fold : ('a -> term -> 'a) -> ('a -> term -> 'a) -> 'a -> decl -> 'a

  val decl_map_fold : ('a -> term -> 'a * term) ->
                      ('a -> term -> 'a * term) -> 'a -> decl -> 'a * decl
end

(** {2 Known identifiers} *)

type known_map = decl Mid.t

val known_id : known_map -> ident -> unit
val known_add_decl : known_map -> decl -> known_map
val merge_known : known_map -> known_map -> known_map

exception KnownWhy3_ident of ident
exception UnknownWhy3_ident of ident
exception RedeclaredWhy3_ident of ident
exception NonFoundedTypeWhy3_decl of tysymbol

val find_constructors : known_map -> tysymbol -> constructor list
val find_inductive_cases : known_map -> lsymbol -> (prsymbol * term) list
val find_logic_definition : known_map -> lsymbol -> ls_defn option
val find_prop : known_map -> prsymbol -> term
val find_prop_decl : known_map -> prsymbol -> prop_kind * term

(** {2 Records} *)

exception EmptyRecord

val parse_record :
  known_map -> (lsymbol * 'a) list -> lsymbol * lsymbol list * 'a Mls.t
(** [parse_record kn field_list] takes a list of record field assignments,
    checks it for well-formedness and returns the corresponding constructor,
    the full list of projection symbols, and the map from projection symbols
    to assigned values. *)

val make_record :
  known_map -> (lsymbol * term) list -> ty -> term

val make_record_update :
  known_map -> term -> (lsymbol * term) list -> ty -> term

val make_record_pattern :
  known_map -> (lsymbol * pattern) list -> ty -> pattern*)
