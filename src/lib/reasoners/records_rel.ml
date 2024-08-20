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

type t = unit

let src = Logs.Src.create ~doc:"Records" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

let timer = Timers.M_Records

let empty uf = (), Uf.domains uf
let assume _ uf _ =
  (), Uf.domains uf, { Sig_rel.assume = []; remove = [] }
let query _ _ _ = None
let case_split _env _uf ~for_model:_ = []
let optimizing_objective _env _uf _o = None
let add env uf _ _ = env, Uf.domains uf, []
let new_terms _ = Expr.Set.empty
let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Records ->
    failwith "This Theory does not support theories extension"
  | _ -> t
