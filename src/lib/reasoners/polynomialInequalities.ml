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

module P = Shostak.Polynome

module type S = sig
  (* Raises Intervals.NotConsistent expl if it manages to prove that
     the semi-algebraic set defined by polynomial inequalities in
     [env] is empty. *)
  val test_polynomes : (P.t * Intervals.t) list -> unit
end

let test_polynomes_ref = ref (fun _ -> ())
let set_test_polynomes myfun = test_polynomes_ref := myfun

module Container : S = struct
  let test_polynomes poly = !test_polynomes_ref poly
end

let refresh () =
  match Options.get_polynomial_plugin () with
  | "" ->
    if Options.get_debug_sdp () then
      eprintf "[Dynlink] Using the default do-nothing module for polynomial \
               inequalities@."
  | path ->
    if Options.get_debug_sdp () then
      eprintf "[Dynlink] Loading the 'polynomial inequalities' reasoner in \
               %s ...@." path;
    try
      MyDynlink.loadfile path;
      if Options.get_debug_sdp () then  eprintf "Success !@.@."
    with
    | MyDynlink.Error m1 ->
      if Options.get_debug_sdp() then begin
        eprintf
          "[Dynlink] Loading the 'polynomial inequalities' reasoner in \
           \"%s\" failed!@."
          path;
        Format.eprintf ">> Failure message: %s@.@."
          (MyDynlink.error_message m1);
      end;
      let prefixed_path = sprintf "%s/%s" Config.osdp_pluginsdir path in
      if Options.get_debug_sdp () then
        eprintf
          "[Dynlink] Loading the 'polynomial inequalities' reasoner in \
           %s with prefix %s@."
          path Config.osdp_pluginsdir;
      try
        MyDynlink.loadfile prefixed_path;
        if Options.get_debug_sdp () then  eprintf "Success !@.@."
      with
      | MyDynlink.Error m2 ->
        if not (Options.get_debug_sdp()) then begin
          eprintf
            "[Dynlink] Loading the 'polynomial inequalities' reasoner in \
             \"%s\" failed!@."
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
