(*******************************************************************************)
(*                                                                             *)
(*   W34AE: A parser of Why3 logic for Alt-Ergo                                *)
(*                                                                             *)
(*   Copyright 2011-2017 OCamlPro SAS                                          *)
(*                                                                             *)
(*   All rights reserved.  This file is distributed under the terms of         *)
(*   the GNU Lesser General Public License version 2.1, with the               *)
(*   special exception on linking described in the file LICENSE.               *)
(*                                                                             *)
(*******************************************************************************)

type loc = Why3_loc.position
type integer_constant = Why3_number.integer_constant
type real_constant = Why3_number.real_constant
type constant = Why3_number.constant
type label = Lstr of Why3_ident.label | Lpos of Why3_loc.position
type quant = Tforall | Texists | Tlambda
type binop = Tand | Tand_asym | Tor | Tor_asym | Timplies | Tiff | Tby | Tso
type unop = Tnot
type ident = { id_str : string; id_lab : label list; id_loc : loc; }
type qualid = Qident of ident | Qdot of qualid * ident
type opacity = bool
type pty =
    PTtyvar of ident * opacity
  | PTtyapp of qualid * pty list
  | PTtuple of pty list
  | PTarrow of pty * pty
  | PTparen of pty
type ghost = bool
type binder = loc * ident option * ghost * pty option
type param = loc * ident option * ghost * pty
type pattern = { pat_desc : pat_desc; pat_loc : loc; }
and pat_desc =
    Pwild
  | Pvar of ident
  | Papp of qualid * pattern list
  | Prec of (qualid * pattern) list
  | Ptuple of pattern list
  | Por of pattern * pattern
  | Pas of pattern * ident
  | Pcast of pattern * pty
type term = { term_desc : term_desc; term_loc : loc; }
and term_desc =
    Ttrue
  | Tfalse
  | Tconst of constant
  | Tident of qualid
  | Tidapp of qualid * term list
  | Tapply of term * term
  | Tinfix of term * ident * term
  | Tinnfix of term * ident * term
  | Tbinop of term * binop * term
  | Tunop of unop * term
  | Tif of term * term * term
  | Tquant of quant * binder list * term list list * term
  | Tnamed of label * term
  | Tlet of ident * term * term
  | Tmatch of term * (pattern * term) list
  | Tcast of term * pty
  | Ttuple of term list
  | Trecord of (qualid * term) list
  | Tupdate of term * (qualid * term) list
type use = { use_theory : qualid; use_import : (bool * string) option; }
type clone_subst =
    CSns of loc * qualid option * qualid option
  | CStsym of loc * qualid * ident list * pty
  | CSfsym of loc * qualid * qualid
  | CSpsym of loc * qualid * qualid
  | CSvsym of loc * qualid * qualid
  | CSlemma of loc * qualid
  | CSgoal of loc * qualid
type field = {
  f_loc : loc;
  f_ident : ident;
  f_pty : pty;
  f_mutable : bool;
  f_ghost : bool;
}
type type_def =
    TDabstract
  | TDalias of pty
  | TDalgebraic of (loc * ident * param list) list
  | TDrecord of field list
  | TDrange of Why3_bigInt.t * Why3_bigInt.t
  | TDfloat of int * int
type visibility = Public | Private | Abstract
type invariant = term list
type type_decl = {
  td_loc : loc;
  td_ident : ident;
  td_params : ident list;
  td_model : bool;
  td_vis : visibility;
  td_def : type_def;
  td_inv : invariant;
}
type logic_decl = {
  ld_loc : loc;
  ld_ident : ident;
  ld_params : param list;
  ld_type : pty option;
  ld_def : term option;
}
type ind_decl = {
  in_loc : loc;
  in_ident : ident;
  in_params : param list;
  in_def : (loc * ident * term) list;
}
type metarg =
    Mty of pty
  | Mfs of qualid
  | Mps of qualid
  | Mpr of qualid
  | Mstr of string
  | Mint of int
type use_clone = use * clone_subst list option
type decl =
    Dtype of type_decl list
  | Dlogic of logic_decl list
  | Dind of Why3_decl.ind_sign * ind_decl list
  | Dprop of Why3_decl.prop_kind * ident * term
  | Dmeta of ident * metarg list
type assertion_kind = Aassert | Aassume | Acheck
type lazy_op = LazyAnd | LazyOr
type variant = term * qualid option
type loop_annotation = {
  loop_invariant : invariant;
  loop_variant : variant list;
}
type for_direction = To | Downto
type pre = term
type post = loc * (pattern * term) list
type xpost = loc * (qualid * pattern * term) list
type spec = {
  sp_pre : pre list;
  sp_post : post list;
  sp_xpost : xpost list;
  sp_reads : qualid list;
  sp_writes : term list;
  sp_variant : variant list;
  sp_checkrw : bool;
  sp_diverge : bool;
}
type type_v = PTpure of pty | PTfunc of param list * type_c
and type_c = type_v * spec
type top_ghost = Gnone | Gghost | Glemma
type expr = { expr_desc : expr_desc; expr_loc : loc; }
and expr_desc =
    Etrue
  | Efalse
  | Econst of constant
  | Eident of qualid
  | Eidapp of qualid * expr list
  | Eapply of expr * expr
  | Einfix of expr * ident * expr
  | Einnfix of expr * ident * expr
  | Elet of ident * top_ghost * expr * expr
  | Efun of ident * top_ghost * lambda * expr
  | Erec of fundef list * expr
  | Elam of lambda
  | Etuple of expr list
  | Erecord of (qualid * expr) list
  | Eupdate of expr * (qualid * expr) list
  | Eassign of expr * qualid * expr
  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Eloop of loop_annotation * expr
  | Ewhile of expr * loop_annotation * expr
  | Elazy of expr * lazy_op * expr
  | Enot of expr
  | Ematch of expr * (pattern * expr) list
  | Eabsurd
  | Eraise of qualid * expr option
  | Etry of expr * (qualid * pattern option * expr) list
  | Efor of ident * expr * for_direction * expr * invariant * expr
  | Eassert of assertion_kind * term
  | Emark of ident * expr
  | Ecast of expr * pty
  | Eany of type_c
  | Eghost of expr
  | Eabstract of expr * spec
  | Enamed of label * expr
and fundef = ident * top_ghost * lambda
and lambda = binder list * pty option * expr * spec
type pdecl =
    Dval of ident * top_ghost * type_v
  | Dlet of ident * top_ghost * expr
  | Dfun of ident * top_ghost * lambda
  | Drec of fundef list
  | Dexn of ident * pty
