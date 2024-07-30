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

type 'a view = LTerm of Expr.t | LSem of 'a
(** Literals are represented using either a syntaxic expression or a semantic
    literal. *)

let pp_view pp ppf = function
  | LTerm e -> Expr.print ppf e
  | LSem a -> pp ppf a

let hash_view hash = function
  | LTerm e -> 2 * Expr.hash e
  | LSem a -> 2 * hash a + 1

let equal_view equal l1 l2 =
  match l1, l2 with
  | LTerm e1, LTerm e2 -> Expr.equal e1 e2
  | LSem a1, LSem a2 -> equal a1 a2
  | LTerm _, LSem _ | LSem _, LTerm _ -> false

let compare_view compare l1 l2 =
  match l1, l2 with
  | LTerm e1, LTerm e2 -> Expr.compare e1 e2
  | LTerm _, _ -> -1
  | _, LTerm _ -> 1

  | LSem a1, LSem a2 -> compare a1 a2

let neg_view neg = function
  | LTerm e -> LTerm (Expr.neg e)
  | LSem a -> LSem (neg a)

module type S = sig
  type elt
  type t

  val make : elt view -> t

  val view : t -> elt view

  val pp : t Fmt.t

  val hash : t -> int

  val equal : t -> t -> bool

  val compare : t -> t -> int

  val neg : t -> t

  val normal_form : t -> t * bool

  val is_ground : t -> bool

  module Table : Hashtbl.S with type key = t

  module Set : Set.S with type elt = t

  module Map : Map.S with type key = t
end

module Make(Sem : Xliteral.S) : S with type elt = Sem.t = struct
  type elt = Sem.t
  type t = Sem.t view

  let make = Fun.id
  let view = Fun.id
  let pp = pp_view Sem.print
  let hash = hash_view Sem.hash
  let equal = equal_view Sem.equal
  let compare = compare_view Sem.compare
  let neg = neg_view Sem.neg

  let normal_form = function
    | LTerm e ->
      (* XXX do better *)
      (* Note: I don't know what "better" is. *)
      let is_pos = Expr.is_positive e in
      LTerm (if is_pos then e else Expr.neg e), not is_pos
    | LSem a ->
      let _, is_neg = Sem.atom_view a in
      LSem (if is_neg then Sem.neg a else a), is_neg

  let is_ground = function
    | LTerm e -> Expr.is_ground e
    | LSem _ -> true

  module Table = Hashtbl.Make(struct
      type t = Sem.t view
      let hash = hash
      let equal = equal
    end)

  module Set = Set.Make(struct
      type t = Sem.t view
      let compare = compare
    end)

  module Map = Map.Make(struct
      type t = Sem.t view
      let compare = compare
    end)
end
