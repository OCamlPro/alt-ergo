(******************************************************************************)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2015 --- OCamlPro                                   *)
(*     This file is distributed under the terms of the CeCILL-C licence       *)
(******************************************************************************)


type 'a abstract

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak
  (X : ALIEN) : Sig.SHOSTAK with type r = X.r and type t = X.r abstract

module Relation
  (X : ALIEN) (Uf : Uf.S) : Sig.RELATION
  with type r = X.r and type uf = Uf.t
