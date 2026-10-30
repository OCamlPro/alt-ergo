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

exception Timeout

exception Step_limit_reached of int

exception Unsolvable

exception Cmp of int

exception Not_implemented of string

exception Internal_error of string

let () =
  Printexc.register_printer (function
    | Not_implemented s ->
      Some (Format.sprintf "Feature not implemented (%s)" s)
    | Internal_error s -> Some (Format.sprintf "Internal error: %s" s)
    | _ -> None)

module MI = Numbers.Int.Map
module SI = Numbers.Int.Set
module MS = Map.Make (String)
module SS = Set.Make (String)

(** Different values for -case-split-policy option: -after-theory-assume
    (default value): after assuming facts in theory by the SAT -before-matching:
    just before performing a matching round -after-matching: just after
    performing a matching round **)
type case_split_policy =
  | AfterTheoryAssume (* default *)
  | BeforeMatching
  | AfterMatching

type inst_kind =
  | Normal
  | Forward
  | Backward

type sat_solver =
  | Tableaux
  | CDCL
  | CDCL_Tableaux

let pp_sat_solver ppf = function
  | Tableaux -> Format.fprintf ppf "Tableaux"
  | CDCL -> Format.fprintf ppf "CDCL"
  | CDCL_Tableaux -> Format.fprintf ppf "CDCL-Tableaux"

type theories_extensions =
  | Adt
  | Arrays
  | Bitv
  | LIA
  | LRA
  | NRA
  | NIA
  | FPA
  | RIA

type axiom_kind =
  | Default
  | Propagator

type mode =
  | Start
  | Assert
  | Sat
  | Unsat

let pp_mode fmt m =
  Format.pp_print_string fmt
    begin match m with
    | Start -> "Start"
    | Assert -> "Assert"
    | Sat -> "Sat"
    | Unsat -> "Unsat"
    end

let equal_mode x y =
  match x, y with
  | Start, Start | Assert, Assert | Sat, Sat | Unsat, Unsat -> true
  | (Start | Assert | Sat | Unsat), (Start | Assert | Sat | Unsat) -> false

let th_ext_of_string ext =
  match ext with
  | "Adt" -> Some Adt
  | "Arrays" -> Some Arrays
  | "Bitv" -> Some Bitv
  | "LIA" -> Some LIA
  | "LRA" -> Some LRA
  | "NRA" -> Some NRA
  | "NIA" -> Some NIA
  | "FPA" -> Some FPA
  | "RIA" -> Some RIA
  | _ -> None

let string_of_th_ext ext =
  match ext with
  | Adt -> "Adt"
  | Arrays -> "Arrays"
  | Bitv -> "Bitv"
  | LIA -> "LIA"
  | LRA -> "LRA"
  | NRA -> "NRA"
  | NIA -> "NIA"
  | FPA -> "FPA"
  | RIA -> "RIA"

let[@inline always] compare_algebraic s1 s2 f_same_constrs_with_args =
  let r1 = Obj.repr s1 in
  let r2 = Obj.repr s2 in
  match Obj.is_int r1, Obj.is_int r2 with
  | true, true -> Stdlib.compare s1 s2 (* both constructors without args *)
  | true, false -> -1
  | false, true -> 1
  | false, false ->
    let cmp_tags = Obj.tag r1 - Obj.tag r2 in
    if cmp_tags <> 0 then cmp_tags else f_same_constrs_with_args (s1, s2)

let[@inline always] cmp_lists l1 l2 cmp_elts =
  try
    List.iter2
      (fun a b ->
        let c = cmp_elts a b in
        if c <> 0 then raise (Cmp c))
      l1 l2;
    0
  with
  | Cmp n -> n
  | Invalid_argument _ -> List.length l1 - List.length l2

type matching_env =
  { no_ematching : bool;
    use_cs : bool;
    backward : inst_kind
  }

type triggers_env =
  { nb_triggers : int;
    triggers_var : bool;
    greedy : bool
  }

let loop ~(f : int -> 'a -> 'b -> 'b) ~(max : int) ~(elt : 'a) ~(init : 'b) : 'b
    =
  let rec loop_aux cpt acc =
    if cpt >= max then acc else loop_aux (cpt + 1) (f cpt elt acc)
  in
  loop_aux 0 init

let print_list ~sep ~pp fmt l =
  match l with
  | [] -> ()
  | e :: l ->
    Format.fprintf fmt "%a" pp e;
    List.iter (fun e -> Format.fprintf fmt "%s %a" sep pp e) l

let rec print_list_pp ~sep ~pp fmt = function
  | [] -> ()
  | [x] -> pp fmt x
  | x :: l ->
    Format.fprintf fmt "%a %a" pp x sep ();
    print_list_pp ~sep ~pp fmt l

let internal_error msg =
  Format.kasprintf (fun s -> raise (Internal_error s)) msg

module Syntax = struct
  let ( let& ) f scope = f ~scope
end

module Extra_options = struct
  exception
    Bad_option of
      { name : string;
        actual : string;
        expected : string
      }

  type 'a descr =
    | Bool : bool descr
    | Int : int descr
    | String : string descr
    | Symbol : (string * 'a) list -> 'a descr

  let wrong opt arg expected =
    raise (Bad_option { name = arg; actual = opt; expected })

  let parse_bool arg opt =
    match opt with
    | "0" -> false
    | "1" -> true
    | _ -> wrong opt arg "'0' or '1'"

  let parse_int arg opt =
    match int_of_string_opt opt with
    | Some i -> i
    | None -> wrong opt arg "an integer"

  let parse_string _ opt = opt

  let make_symlist ~sep flags =
    match flags with
    | [] -> "<none>"
    | (h, _) :: t -> List.fold_left (fun x (y, _) -> x ^ sep ^ y) h t

  let parse_symbol symbols arg opt =
    try List.assoc opt symbols
    with Not_found ->
      wrong opt arg ("one of: " ^ make_symlist ~sep:" " symbols)

  type 'a parser = string -> string -> 'a

  let parser (type a) (descr : a descr) : a parser =
    match descr with
    | Bool -> parse_bool
    | Int -> parse_int
    | String -> parse_string
    | Symbol symbols -> parse_symbol symbols

  type extra_option = O : 'a ref * 'a descr * string -> extra_option

  let extra_params : (string, extra_option) Hashtbl.t = Hashtbl.create 17

  let register loc r descr kwd =
    (if Compat.String.starts_with ~prefix:"no-" kwd
     then (
       Printf.eprintf "Error: cannot define extra option '-X %s':\n" kwd;
       Printf.eprintf
         "  Names starting with 'no-' are reserved for boolean option\n";
       Printf.eprintf "  Option defined at: %s\n" loc)
     else
       match Hashtbl.find_opt extra_params kwd with
       | Some (O (_, _, loc2)) ->
         Printf.eprintf "Warning: extra option '-X %s' is already defined:\n"
           kwd;
         Printf.eprintf "  First definition: %s\n" loc2;
         Printf.eprintf "  New definition: %s\n" loc
       | None -> Hashtbl.replace extra_params kwd (O (r, descr, loc)));
    fun () -> !r

  let string loc kwd default = register loc (ref default) String kwd

  let int loc kwd default = register loc (ref default) Int kwd

  let bool loc kwd =
    if Compat.String.starts_with ~prefix:"no-" kwd
    then
      let kwd = String.sub kwd 3 (String.length kwd - 3) in
      let read = register loc (ref false) Bool kwd in
      fun () -> not (read ())
    else register loc (ref false) Bool kwd

  let symbol loc kwd default symbols =
    register loc (ref default) (Symbol symbols) kwd

  let cut_at s c =
    let pos = String.index s c in
    String.sub s 0 pos, String.sub s (pos + 1) (String.length s - pos - 1)

  let parse_and_set name =
    let unknown_option () =
      Error (Format.asprintf "unknown option '-X %s'" name)
    in
    let name, is_no_option =
      if Compat.String.starts_with ~prefix:"no-" name
      then String.sub name 3 (String.length name - 3), true
      else name, false
    in
    match cut_at name '=' with
    | exception Not_found -> (
      match Hashtbl.find_opt extra_params name with
      | Some (O (option, Bool, _loc)) ->
        option := not is_no_option;
        Ok ()
      | _ ->
        Error
          (Format.asprintf
             "wrong argument '%s'; option '-X' expects a name=value pair" name))
    | name, v -> (
      match Hashtbl.find_opt extra_params name with
      | Some (O (option, descr, _loc)) -> (
        match parser descr name v with
        | v ->
          if is_no_option
          then
            match descr with
            | Bool ->
              option := not v;
              Ok ()
            | _ -> unknown_option ()
          else (
            option := v;
            Ok ())
        | exception Bad_option { name; actual; expected } ->
          Error
            (Format.asprintf "wrong argument '%s'; option '-X %s' expects %s"
               actual name expected))
      | None -> unknown_option ())
end
