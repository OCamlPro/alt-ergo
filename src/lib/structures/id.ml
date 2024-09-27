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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

type t = Hstring.t [@@deriving ord]

let equal = Hstring.equal

let pp ppf id =
  Dolmen.Smtlib2.Script.Poly.Print.id ppf
    (Dolmen.Std.Name.simple (Hstring.view id))

let show id = Fmt.to_to_string pp id

module Namespace = struct
  module type S = sig
    val fresh : ?base:string -> unit -> string
  end

  module Make () = struct
    let fresh, reset_fresh_cpt =
      let cpt = ref 0 in
      let fresh_string ?(base = "") () =
        let res = base ^ (string_of_int !cpt) in
        incr cpt;
        res
      in
      let reset_fresh_string_cpt () =
        cpt := 0
      in
      fresh_string, reset_fresh_string_cpt
  end

  module Internal = Make ()

  module Skolem = Make ()

  module Abstract = Make ()

  module GetValue = Make ()

  let reinit () =
    Internal.reset_fresh_cpt ();
    Skolem.reset_fresh_cpt ();
    Abstract.reset_fresh_cpt ();
    GetValue.reset_fresh_cpt ()
end
