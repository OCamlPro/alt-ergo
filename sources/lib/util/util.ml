(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

exception Timeout
exception Unsolvable

exception Cmp of int

module MI = Map.Make(struct type t = int let compare a b = a - b end)

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
  | true, true -> Pervasives.compare s1 s2 (* both constructors without args *)
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

