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

(****
   Using Alt-Ergo's lib: minimal example

   compile & test with the following command if the lib is not installed:

   ocamlopt -o lib_usage \
   -I `ocamlfind query num` \
   -I `ocamlfind query zarith` \
   -I `ocamlfind query ocplib-simplex` \
   -I `ocamlfind query camlzip` \
   -I .. \
   nums.cmxa zarith.cmxa ocplibSimplex.cmxa \
   unix.cmxa str.cmxa zip.cmxa dynlink.cmxa \
   altErgoLib.cmxa lib_usage.ml && ./lib_usage

   or with the following command if the lib is installed:


   ocamlopt -o lib_usage \
   -I `ocamlfind query num` \
   -I `ocamlfind query zarith` \
   -I `ocamlfind query ocplib-simplex` \
   -I `ocamlfind query camlzip` \
   -I `ocamlfind query alt-ergo` \
   nums.cmxa zarith.cmxa ocplibSimplex.cmxa \
   unix.cmxa str.cmxa zip.cmxa dynlink.cmxa \
   altErgoLib.cmxa lib_usage.ml && ./lib_usage

 ****)

(* Format.eprintf
   "\n(* This minimal example shows how to use Alt-Ergo's lib *)\n@."

   open AltErgoLib *)

(* module PA = Parsed_interface

   let _x = PA.mk_var_type Loc.dummy "'a"

   let one = PA.mk_int_const Loc.dummy "1"
   let two = PA.mk_int_const Loc.dummy "2"
   let three = PA.mk_int_const Loc.dummy "3"
   let one_two = PA.mk_add Loc.dummy one two
   let eq1 = PA.mk_pred_eq Loc.dummy one_two three
   let eq2 = PA.mk_pred_eq Loc.dummy one three

   let goal_1 = PA.mk_goal Loc.dummy "toy_1" eq1
   let goal_2 = PA.mk_goal Loc.dummy "toy_2" eq2
   let goal_3 = PA.mk_goal Loc.dummy "toy_3" (PA.mk_not Loc.dummy eq1)

   let parsed = [goal_1; goal_2; goal_3]

   let typed, _env = Typechecker.type_file parsed

   let pbs = Typechecker.split_goals_and_cnf typed

   module SAT = Fun_sat_frontend.Make(Theory.Main_Default)
   module FE = Frontend.Make(SAT)

   let () =
   List.iter
    (fun (pb, _goal_name) ->
       let ctxt = Frontend.init_all_used_context () in
       let env = FE.init_env ctxt in
       List.iter (FE.process_decl env) pb;
       match env.res with
       | `Sat | `Unknown ->
         Format.printf "unknown@."
       | `Unsat ->
         Format.printf "unsat@."
    ) pbs *)
