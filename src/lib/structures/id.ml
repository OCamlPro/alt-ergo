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

type t = Hstring.t [@@deriving ord]

let pp ppf id =
  Dolmen.Smtlib2.Script.Poly.Print.id ppf
    (Dolmen.Std.Name.simple (Hstring.view id))

let show id = Fmt.str "%a" pp id

module Namespace = struct
  module type S = sig
    val fresh : ?base:string -> unit -> string
    val is_id : string -> bool
  end

  module Make (S : sig val prefix : string end) = struct
    let make_as_fresh = (^) S.prefix

    let fresh, reset_fresh_cpt =
      let cpt = ref 0 in
      let fresh_string ?(base = "") () =
        let res = make_as_fresh (base ^ (string_of_int !cpt)) in
        incr cpt;
        res
      in
      let reset_fresh_string_cpt () =
        cpt := 0
      in
      fresh_string, reset_fresh_string_cpt

    let is_id = Stdcompat.String.starts_with ~prefix:S.prefix
  end

  module Internal = Make (struct let prefix = ".k" end)

  module Skolem = Make
      (struct
        (* garder le suffixe "__" car cela influence l'ordre *)
        let prefix = ".?__"
      end)

  let make_as_fresh_skolem = Skolem.make_as_fresh

  module Abstract = Make (struct let prefix = "@a" end)

  let reinit () =
    Internal.reset_fresh_cpt ();
    Skolem.reset_fresh_cpt ();
    Abstract.reset_fresh_cpt ()
end
