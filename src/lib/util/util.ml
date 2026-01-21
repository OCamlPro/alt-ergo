(*********************************************************************************)
(*                                                                               *)
(*     Alt-Ergo: The SMT Solver For Software Verification                        *)
(*     Copyright (C) --- OCamlPro SAS                                            *)
(*                                                                               *)
(*     This software is governed by the CeCILL  license under French law and     *)
(*     abiding by the rules of distribution of free software.  You can  use,     *)
(*     modify and/ or redistribute the software under the terms of the CeCILL    *)
(*     license as circulated by CEA, CNRS and INRIA at the following URL         *)
(*     "http://www.cecill.info".                                                 *)
(*                                                                               *)
(*     As a counterpart to the access to the source code and  rights to copy,    *)
(*     modify and redistribute granted by the license, users are provided only   *)
(*     with a limited warranty  and the software's author,  the holder of the    *)
(*     economic rights,  and the successive licensors  have only  limited        *)
(*     liability.                                                                *)
(*                                                                               *)
(*     In this respect, the user's attention is drawn to the risks associated    *)
(*     with loading,  using,  modifying and/or developing or reproducing the     *)
(*     software by the user in light of its specific status of free software,    *)
(*     that may mean  that it is complicated to manipulate,  and  that  also     *)
(*     therefore means  that it is reserved for developers  and  experienced     *)
(*     professionals having in-depth computer knowledge. Users are therefore     *)
(*     encouraged to load and test the software's suitability as regards their   *)
(*     requirements in conditions enabling the security of their systems and/or  *)
(*     data to be ensured and,  more generally, to use and operate it in the     *)
(*     same conditions as regards security.                                      *)
(*                                                                               *)
(*     The fact that you are presently reading this means that you have had      *)
(*     knowledge of the CeCILL license and that you accept its terms.            *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     This is a free release of Alt-Ergo under the terms of CeCILL license.     *)
(*     The latest releases of Alt-Ergo are distributed under the terms of        *)
(*     OCamlPro Non-Commercial Purpose License, version 1.                       *)
(*                                                                               *)
(*     As an exception, Alt-Ergo Club members at the Gold level can              *)
(*     use this file under the terms of the Apache Software License              *)
(*     version 2.0.                                                              *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     The Alt-Ergo theorem prover                                               *)
(*                                                                               *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                        *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout                     *)
(*                                                                               *)
(*     CNRS - INRIA - Universite Paris Sud                                       *)
(*                                                                               *)
(*     ------------------------------------------------------------------------  *)
(*                                                                               *)
(*     More details can be found in the directory licenses/                      *)
(*                                                                               *)
(*********************************************************************************)

exception Timeout
exception Unsolvable

exception Cmp of int

module MI = Map.Make(struct type t = int
    let compare (x: int) y = Stdlib.compare x y end)

module SI = Set.Make(struct type t = int
    let compare (x: int) y = Stdlib.compare x y end)

module SS = Set.Make(String)


(** Different values for -case-split-policy option:
    -after-theory-assume (default value): after assuming facts in
    theory by the SAT
    -before-matching: just before performing a matching round
    -after-matching: just after performing a matching round **)
type case_split_policy =
  | AfterTheoryAssume (* default *)
  | BeforeMatching
  | AfterMatching


type inst_kind = Normal | Forward | Backward

type sat_solver =
  | Tableaux
  | Tableaux_CDCL
  | CDCL
  | CDCL_Tableaux

type theories_extensions =
  | Sum
  | Adt
  | Arrays
  | Records
  | Bitv
  | LIA
  | LRA
  | NRA
  | NIA
  | FPA

type axiom_kind = Default | Propagator

let th_ext_of_string ext =
  match ext with
  | "Sum" -> Some Sum
  | "Adt" -> Some Adt
  | "Arrays" -> Some Arrays
  | "Records" -> Some Records
  | "Bitv" -> Some Bitv
  | "LIA" -> Some LIA
  | "LRA" -> Some LRA
  | "NRA" -> Some NRA
  | "NIA" -> Some NIA
  | "FPA" -> Some FPA
  |  _ -> None

let string_of_th_ext ext =
  match ext with
  | Sum -> "Sum"
  | Adt -> "Adt"
  | Arrays -> "Arrays"
  | Records -> "Records"
  | Bitv -> "Bitv"
  | LIA -> "LIA"
  | LRA -> "LRA"
  | NRA -> "NRA"
  | NIA -> "NIA"
  | FPA -> "FPA"

let [@inline always] compare_algebraic s1 s2 f_same_constrs_with_args =
  let r1 = Obj.repr s1 in
  let r2 = Obj.repr s2 in
  match Obj.is_int r1, Obj.is_int r2 with
  | true, true -> Stdlib.compare s1 s2 (* both constructors without args *)
  | true, false -> -1
  | false, true -> 1
  | false, false ->
    let cmp_tags = Obj.tag r1 - Obj.tag r2 in
    if cmp_tags <> 0 then cmp_tags else f_same_constrs_with_args (s1, s2)

let [@inline always] cmp_lists l1 l2 cmp_elts =
  try
    List.iter2
      (fun a b ->
         let c = cmp_elts a b in
         if c <> 0 then raise (Cmp c)
      )l1 l2;
    0
  with
  | Cmp n -> n
  | Invalid_argument _ -> List.length l1 - List.length l2

type matching_env =
  {
    nb_triggers : int;
    triggers_var : bool;
    no_ematching: bool;
    greedy : bool;
    use_cs : bool;
    backward : inst_kind
  }

let loop
    ~(f : int -> 'a -> 'b -> 'b)
    ~(max : int)
    ~(elt : 'a)
    ~(init : 'b) : 'b
  =
  let rec loop_aux cpt acc =
    if cpt >= max then acc
    else
      loop_aux (cpt+1) (f cpt elt acc)
  in
  loop_aux 0 init

let print_list ~sep ~pp fmt l =
  match l with
    [] -> ()
  | e :: l ->
    Format.fprintf fmt "%a" pp e;
    List.iter (fun e -> Format.fprintf fmt "%s %a" sep pp e) l


let rec print_list_pp ~sep ~pp fmt = function
  | [] -> ()
  | [x] -> pp fmt x
  | x :: l ->
    Format.fprintf fmt "%a %a" pp x sep ();
    print_list_pp ~sep ~pp fmt l

