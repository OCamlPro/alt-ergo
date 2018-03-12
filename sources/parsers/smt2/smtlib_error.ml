(******************************************************************************)
(*                                                                            *)
(* An SMT-LIB 2 for the Alt-Ergo Theorem Prover                               *)
(*                                                                            *)
(******************************************************************************)

open Lexing
open Format

let status = ref "undef"
let logic = ref false
let is_qf = ref false
let is_uf = ref false
let is_real = ref false
let is_dt = ref false
let is_linear = ref false
let is_non_linear = ref false


let set_status s = status := s
let set_logic t = logic := t
let set_is_qf t = is_qf := t
let set_is_uf t = is_uf := t
let set_is_real t = is_real := t
let set_is_dt t = is_dt := t
let set_is_linear t = is_linear := t
let set_is_non_linear t = is_non_linear := t
let get_status () = !status
let get_logic () = !logic
let get_is_qf () = !is_qf
let get_is_uf () = !is_uf
let get_is_real () = !is_real
let get_is_dt () = !is_dt
let get_is_linear () = !is_linear
let get_is_non_linear () = !is_non_linear

type error =
| Lexical_error of string
| Syntax_error of string
| Typing_error of string
| Incremental_error of string
| Unknow_Type_error of string
| Missing_parameter_error of string
| Logic_declaration_error of string
| Sort_declaration_error of string
| Datatype_declaration_error of string
| Quantifier_error of string
| Fun_declaration_error of string
| Ambiguity_error of string
| No_match_error of string
| Type_clash_error of string * string

exception Error of error * (Lexing.position * Lexing.position)

let error e p = raise (Error (e,p))

let report_loc fmt file (b,e) =
  if b = dummy_pos || e = dummy_pos then
    fprintf fmt "File \"%s\"\nerror : " file
  else
    let l = b.pos_lnum in
    let fc = b.pos_cnum - b.pos_bol + 1 in
    let lc = e.pos_cnum - b.pos_bol + 1 in
    fprintf fmt "File \"%s\", line %d, characters %d-%d\n" file l fc lc


let print fmt f e p =
  report_loc fmt f p;
  begin match e with
  | Lexical_error s -> fprintf fmt "Lexical error : %s" s
  | Syntax_error s -> fprintf fmt "Syntax error : %s" s
  | Typing_error s -> fprintf fmt "Typing error : %s" s
  | Incremental_error s -> fprintf fmt "Incremental error : %s  \n" s
  | Unknow_Type_error s -> fprintf fmt "Unknown sort/type : %s \n" s
  | Missing_parameter_error s -> fprintf fmt "Missing parameter : %s \n" s
  | Logic_declaration_error s -> fprintf fmt "Logic declaration error : %s \n" s
  | Sort_declaration_error s -> fprintf fmt "Sort declaration error : %s \n" s
  | Fun_declaration_error s -> fprintf fmt "Fun declaration error : %s \n" s
  | Datatype_declaration_error s ->
    fprintf fmt "Datatypes declaration error : %s \n" s
  | Quantifier_error s -> fprintf fmt "Quantifier error : %s \n" s
  | Ambiguity_error s -> fprintf fmt "Ambiguity error : %s \n" s
  | No_match_error s -> fprintf fmt "No match for : %s\n" s
  | Type_clash_error(t1,t2) -> fprintf fmt "Clash type between : %s / %s \n" t1 t2
  end;
  fprintf fmt "\n@."


