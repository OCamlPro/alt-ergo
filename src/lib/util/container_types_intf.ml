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

(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2016 OCamlPro SAS                                    *)
(*   Copyright 2014--2016 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module type Thing = sig
  type t

  include Hashtbl.HashedType with type t := t

  include Map.OrderedType with type t := t

  val print : t Fmt.t
end

module type Set = sig
  type elt

  type t

  val print : t Fmt.t

  val get_singleton_exn : t -> elt

  val get_singleton : t -> elt option
end

module type Map = sig
  type key

  module Set : Set with type elt = key

  type +!'a t

  val print : 'a Fmt.t -> 'a t Fmt.t

  val get_singleton_exn : 'a t -> key * 'a

  val get_singleton : 'a t -> (key * 'a) option

  val keys : _ t -> Set.t

  val of_set : (key -> 'a) -> Set.t -> 'a t
end

module type Tbl = sig
  type key

  type !'a t

  val print : 'a Fmt.t -> 'a t Fmt.t
end

module type S = sig
  type t

  module T : Thing with type t = t

  include Thing with type t := T.t

  module Set : Set with type elt = t

  module Map : Map with type key = t and module Set = Set

  module Tbl : Tbl with type key = t
end

module type Set_plus_stdlib = sig
  include Set

  include Stdlib.Set.S with type elt := elt and type t := t
end

module type Map_plus_stdlib = sig
  include Map

  include Stdlib.Map.S with type key := key and type 'a t := 'a t
end

module type Tbl_plus_stdlib = sig
  include Tbl

  include Stdlib.Hashtbl.S with type key := key and type 'a t := 'a t
end

module type S_plus_stdlib = sig
  type t

  module T : Thing with type t = t

  include Thing with type t := T.t

  module Set : Set_plus_stdlib with type elt = t

  module Map : Map_plus_stdlib with type key = t and module Set = Set

  module Tbl : Tbl_plus_stdlib with type key = t
end
