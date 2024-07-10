(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
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

module DStd = Dolmen.Std
module DE = Dolmen.Std.Expr

type _ t =
  | Hstring : Hstring.t -> 'a t
  | Term_cst : DE.term_cst -> DE.term_cst t
  | Ty_cst : DE.ty_cst -> DE.ty_cst t
  | Ty_var : DE.ty_var -> DE.ty_var t

type term_cst = DE.term_cst t
type ty_cst = DE.ty_cst t
type ty_var = DE.ty_var t

let[@inline always] of_term_cst id = Term_cst id
let[@inline always] of_ty_cst id = Ty_cst id
let[@inline always] of_ty_var id = Ty_var id
let[@inline always] of_hstring hs = Hstring hs
let[@inline always] of_string s = of_hstring @@ Hstring.make s

let[@inline always] to_term_cst id =
  match id with
  | Term_cst t -> t
  | _ -> invalid_arg "to_term_cst"

let hash (type a) (u : a t) =
  match u with
  | Hstring hs -> Hstring.hash hs
  | Term_cst id -> DE.Id.hash id
  | Ty_cst id -> DE.Id.hash id
  | Ty_var id -> DE.Id.hash id

let pp (type a) ppf (u : a t) =
  match u with
  | Hstring hs -> Hstring.print ppf hs
  | Term_cst id -> DE.Id.print ppf id
  | Ty_cst id -> DE.Id.print ppf id
  | Ty_var id -> DE.Id.print ppf id

let show (type a) (u : a t) = Fmt.to_to_string pp u

let equal (type a b) (u1 : a t) (u2 : b t) =
  match u1, u2 with
  | Hstring hs1, Hstring hs2 -> Hstring.equal hs1 hs2
  | Term_cst id1, Term_cst id2 -> DE.Id.equal id1 id2
  | Ty_cst id1, Ty_cst id2 -> DE.Id.equal id1 id2
  | Ty_var id1, Ty_var id2 -> DE.Id.equal id1 id2
  | _ -> String.equal (show u1) (show u2)

let compare (type a b) (u1 : a t) (u2 : b t) =
  match u1, u2 with
  | Hstring hs1, Hstring hs2 -> Hstring.compare hs1 hs2
  | Term_cst id1, Term_cst id2 -> DE.Id.compare id1 id2
  | Ty_cst id1, Ty_cst id2 -> DE.Id.compare id1 id2
  | Ty_var id1, Ty_var id2 -> DE.Id.compare id1 id2
  | _ -> String.compare (show u1) (show u2)

let order_tag : int DStd.Tag.t = DStd.Tag.create ()

let perfect_hash id =
  match id with
  | Term_cst id ->
    Option.get @@ DE.Term.Const.get_tag id order_tag
  | Hstring hs ->
    Hstring.hash hs
  | _ -> .

module Term_set = Set.Make
    (struct
      type nonrec t = term_cst
      let compare = compare
    end)

module Ty_map = Map.Make
    (struct
      type nonrec t = ty_cst
      let compare = compare
    end)
