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

Format.eprintf
  "\n(* This minimal example shows how to use Alt-Ergo's lib *)\n@."

open AltErgoLib

module PA = Parsed_interface

let () = Options.set_is_gui false

let x = PA.mk_var_type Loc.dummy "'a"

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

let typed, env = Typechecker.type_file parsed

let pbs = Typechecker.split_goals_and_cnf typed

module SAT = Fun_sat.Make(Theory.Main_Default)
module FE = Frontend.Make(SAT)

let () =
  List.iter
    (fun (pb, goal_name) ->
       let ctxt = FE.init_all_used_context () in
       let acc0 = SAT.empty (), true, Explanation.empty in
       let _, consistent, ex =
         List.fold_left
           (fun acc d ->
              FE.process_decl (fun _ _ -> ()) ctxt acc d
           )acc0 pb
       in
       Format.printf "%s@."
         (if consistent then "unknown" else "unsat")
    )pbs
