(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format

module type S = sig

  module P : Polynome.EXTENDED_Polynome

  (* Raises Intervals.NotConsistent expl if it manages to prove that
     the semi-algebraic set defined by polynomial inequalities in
     [env] is empty. *)
  val test_polynomes : (P.t * Intervals.t) list -> unit
end

module type Container_SIG = sig
  module Make
    (X : Sig.X)
    (Uf : Uf.S with type r = X.r)
    (P : Polynome.EXTENDED_Polynome with type r = X.r)
    : S with module P = P
end

module Container : Container_SIG = struct
  module Make
    (X : Sig.X)
    (Uf : Uf.S with type r = X.r)
    (P : Polynome.EXTENDED_Polynome with type r = X.r)
    : S with module P = P = struct

      module P = P

      let test_polynomes polys = ()
    end
end

let current = ref (module Container : Container_SIG)

let initialized = ref false

let set_current mdl = current := mdl

let load_current_polynomial_inequalities_reasoner () =
  match Options.polynomial_inequalities_plugin () with
  | "" ->
    if Options.debug_sdp () then
      eprintf "[Dynlink] Using the default do-nothing module for \
polynomial inequalities@."

  | path ->
    if Options.debug_sdp () then
      eprintf "[Dynlink] Loading the 'polynomial inequalities' \
reasoner in %s ...@." path;
    try
      MyDynlink.loadfile path;
      if Options.debug_sdp () then  eprintf "Success !@.@."
    with
    | MyDynlink.Error m1 ->
      if Options.debug_sdp() then begin
        eprintf
          "[Dynlink] Loading the 'polynomial inequalities' reasoner \
in \"%s\" failed!@."
          path;
        Format.eprintf ">> Failure message: %s@.@."
          (MyDynlink.error_message m1);
      end;
      let prefixed_path = sprintf "%s/%s" Config.pluginsdir path in
      if Options.debug_sdp () then
        eprintf
          "[Dynlink] Loading the 'polynomial inequalities' reasoner \
in %s with prefix %s@."
          path Config.pluginsdir;
      try
        MyDynlink.loadfile prefixed_path;
        if Options.debug_sdp () then  eprintf "Success !@.@."
      with
      | MyDynlink.Error m2 ->
        if not (Options.debug_sdp()) then begin
          eprintf
            "[Dynlink] Loading the 'polynomial inequalities' reasoner \
in \"%s\" failed!@."
            path;
          Format.eprintf ">> Failure message: %s@.@."
            (MyDynlink.error_message m1);
        end;
        eprintf
          "[Dynlink] Trying to load the plugin from \"%s\" failed too!@."
          prefixed_path;
        Format.eprintf ">> Failure message: %s@.@."
          (MyDynlink.error_message m2);
        exit 1

let get_current () =
  if not !initialized then
    begin
      load_current_polynomial_inequalities_reasoner ();
      initialized := true;
    end;
  !current
