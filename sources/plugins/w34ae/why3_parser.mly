(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

%{

open Lexing
open Why3_ptree
open Parsed_interface
open Parsed

  let infix  s = "infix "  ^ s
  let prefix s = "prefix " ^ s

  let floc s e = (s,e)

  let add_lab id l = { id with id_lab = l }

  let id_anonymous loc = { id_str = "_"; id_lab = []; id_loc = loc }

  let mk_id id s e = { id_str = id; id_lab = []; id_loc = floc s e }

  let mk_term d s e = d

  let error_param loc =
    Why3_loc.errorm ~loc "cannot determine the type of the parameter"

  let error_loc loc = Why3_loc.error ~loc Error

  (* Added  *)

 let str_of_labs labs =
  String.concat " " labs

 let dummy_loc = Loc.dummy

  let translate_param (loc, id_op, pty) =
    match id_op with
    | Some id -> (loc, id.id_str, pty)
    | None -> (loc, "",  pty)

  let mk_function t ty loc named_ident params =
    let expr = t in
    mk_function_def loc named_ident  (List.map translate_param params)ty expr

  let mk_pred term params loc named_ident =
    let expr = term in
    match params with
    | [] ->  mk_ground_predicate_def loc named_ident expr
    | _ -> mk_non_ground_predicate_def loc named_ident
             (List.map translate_param params) expr

  let mak_logic loc ssl pptyop params =
    let ppure_type_list =
      List.map (fun (_, _, pty) -> pty ) params in
    let logic_type =
      mk_logic_type ppure_type_list pptyop in
    mk_logic loc Symbols.Other ssl logic_type

  let mk_tuple pl loc =
    let length =  string_of_int (List.length pl) in
    let name = "tuple" ^ length in
    mk_external_type loc pl name

  let mk_tyapp q pl =
    match q with
    | {Parsed.pp_desc = PPvar "int"} -> int_type
    | {Parsed.pp_desc = PPvar "bool"} -> bool_type
    | {Parsed.pp_desc = PPvar "real"} -> real_type
    | {Parsed.pp_desc = PPvar s; pp_loc } ->  mk_external_type pp_loc pl s
    | _ -> Format.eprintf "TODO@."; assert false

  let mk_apply loc (f : Parsed.lexpr) a =
    match f with
    | { pp_desc = Parsed.PPapp ("mod", le) } ->
       mk_application loc "comp_mod" (le @ [a])
    | { pp_desc = Parsed.PPapp ("div", le) } ->
       mk_application loc "comp_div" (le @ [a])
    | { pp_desc = Parsed.PPapp ("domain_restriction", le) } ->
       mk_application loc "infix_lsbr" (le @ [a])
    | { pp_desc = Parsed.PPapp ("domain_substraction", le) } ->
       mk_application loc "infix_lslsbr" (le @ [a])
    | { pp_desc = Parsed.PPapp ("range_substraction", le) } ->
       mk_application loc "infix_brgtgt" (le @ [a])
    | { pp_desc = Parsed.PPapp ("range_restriction", le) } ->
       mk_application loc "infix_brgt" (le @ [a])
    | { pp_desc = PPvar "singleton" } ->
       let empty = mk_application loc "empty" [] in
       mk_application loc "add" [a; empty]
    | { pp_desc = PPvar s } -> mk_application loc s [a]
    | { pp_desc = PPapp (s, l) } -> mk_application loc s (l @ [a])
    | _ ->  Format.eprintf "TODO@."; assert false

  let mk_infix_ident id loc t1 t2 =
    let get_infix_ident i =
      List.hd (List.rev (String.split_on_char ' ' i.id_str)) in
    match get_infix_ident id with
      | "+" -> mk_add loc t1 t2
      | "-" -> mk_sub  loc t1 t2
      | "*" ->  mk_mul  loc t1 t2
      | "<" -> mk_pred_lt  loc t1 t2
      | "<=" -> mk_pred_le  loc t1 t2
      | ">" -> mk_pred_gt  loc t1 t2
      | ">=" -> mk_pred_gt  loc t1 t2
      | "=" -> mk_pred_eq loc t1 t2
      | "==" -> mk_application loc "infix_eqeq" [t1; t2]
      | "+->" -> mk_application loc "infix_plmngt" [t1; t2]
      | "-->" -> mk_application loc "infix_mnmngt" [t1; t2]
      | "<+" -> mk_application loc "infix_lspl" [t1; t2]
      | "-->>" -> mk_application loc "infix_mnmngtgt" [t1; t2]
      | ">->>" -> mk_application loc "infix_gtmngtgt" [t1; t2]
      | ">->" -> mk_application loc "infix_gtmngt" [t1; t2]
      | ">+>" -> mk_application loc "infix_gtplgt" [t1; t2]
      | s ->  Format.eprintf "TODO: translate symbols %S@." s; assert false

  let mk_tuple_record exp_list loc =
  let length = string_of_int (List.length exp_list) in
  let field_name = "Tuple" ^ length ^ "_proj_" in
  let rec trad l n =
    match l with
    | [] -> []
    | h::t ->
       let fn = field_name ^ string_of_int n in
       (fn ,h)::(trad t (n + 1))
  in
  let str_exp_list = trad exp_list 1 in
  mk_record loc str_exp_list

  let mk_qualid = function
  | { id_str = "True"; id_loc} -> mk_true_const id_loc
  | { id_str = "False"; id_loc} -> mk_false_const id_loc
  | { id_str; id_loc} -> mk_var id_loc id_str

%}

(* Tokens *)

%token <string> LIDENT LIDENT_QUOTE UIDENT UIDENT_QUOTE
%token <string> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF

%token <string> STRING
%token <string> QUOTE_UIDENT QUOTE_LIDENT

(* keywords *)

%token AS AXIOM CLONE CONSTANT
%token ELSE END EPSILON EXISTS EXPORT FALSE FORALL FUNCTION
%token GOAL IF IMPORT IN LEMMA
%token LET NAMESPACE NOT PREDICATE
%token THEN THEORY TRUE TYPE USE WITH

(* program keywords *)

%token GHOST INVARIANT MODEL
%token VAL

(* symbols *)

%token AND ARROW
%token BAR
%token COLON COMMA
%token DOT EQUAL LT GT LTGT
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LRARROW OR
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

(* program symbols *)

%token LEFTBRC RIGHTBRC SEMICOLON

(* Precedences *)

%nonassoc IN
%nonassoc DOT ELSE
%nonassoc prec_named
%nonassoc COLON
%right ARROW LRARROW
%right OR
%right AND
%nonassoc NOT
%left EQUAL LTGT LT GT OP1
%left OP2
%left OP3
%left OP4
%nonassoc prec_prefix_op
%nonassoc OPPREF

(* Entry points *)

%type <Parsed.lexpr list * bool> trigger_parser
%start trigger_parser

%type <Parsed.lexpr> lexpr_parser
%start lexpr_parser

%type <Parsed.file> file_parser
%start file_parser
%%

file_parser:
| logic_file { $1 }

lexpr_parser:
| logic_file { Format.eprintf "TODO@."; assert false }

trigger_parser:
| logic_file  { Format.eprintf "TODO@."; assert false }


(* Theories, modules, namespaces *)

logic_file:
| theory EOF   {  $1 }

theory:
| theory_head theory_decl* END
  { List.concat (List.map (function Some x -> x | _ -> assert false) (List.filter (fun x -> x <> None) $2)) }

theory_head:
| THEORY labels(uident_nq)  {  $2 }

theory_decl:
    | decl { Some $1 }
    | use_clone { None }


(* Use and clone *)

use_clone:
| USE use                                 { ($2, None) }
| CLONE use                               { ($2, Some []) }
| CLONE use WITH comma_list1(clone_subst) { ($2, Some $4) }

use:
| boption(IMPORT) tqualid
    { None }
| boption(IMPORT) tqualid AS uident
    { None }
| EXPORT tqualid
    { None }

clone_subst:
| NAMESPACE ns EQUAL ns         { None }
| TYPE qualid ty_var* EQUAL ty  { None }
| CONSTANT  qualid EQUAL qualid { None }
| FUNCTION  qualid EQUAL qualid { None }
| PREDICATE qualid EQUAL qualid { None }
| VAL       qualid EQUAL qualid { None }
| LEMMA     qualid              { None }
| GOAL      qualid              { None }

ns:
| uqualid { Some $1 }
| DOT     { None }

(* Theory declarations *)

decl:
| TYPE with_list1(type_decl)
    { $2 }
| TYPE late_invariant
    { [$2] }
| CONSTANT  constant_decl
    { [$2] }
| FUNCTION  function_decl  with_logic_decl*
    { ($2::$3) }
| PREDICATE predicate_decl with_logic_decl*
    { ($2::$3) }
| AXIOM labels(ident_nq) COLON term
    { [mk_generic_axiom  (floc $startpos $endpos) $2.id_str $4] }
| GOAL  labels(ident_nq) COLON term
    { [mk_goal (floc $startpos $endpos) $2.id_str $4] }

(* Type declarations *)

type_decl:
| labels(lident_nq) ty_var* typedefn
  { let model, def, inv = $3 in
    let loc = floc $startpos $endpos in
    let ty_vars = List.map (fun i -> i.id_str) $2 in
    match def with
    | None -> mk_abstract_type_decl loc ty_vars $1.id_str
    | Some l ->  mk_enum_type_decl loc ty_vars $1.id_str l
   }

late_invariant:
| labels(lident_nq) ty_var* invariant+
    { let loc = floc $startpos $endpos in
      let ty_vars = List.map (fun i -> i.id_str) $2 in
      mk_abstract_type_decl loc ty_vars $1.id_str }

ty_var:
| labels(quote_lident) { $1 }

typedefn:
| (* epsilon *)
    { false, None, [] }
| model bar_list1(type_case) invariant*
    { $1, Some $2, $3 }

model:
| EQUAL         { false }
| MODEL         { true }

type_case:
| labels(uident_nq) { $1.id_str }

(* Logic declarations *)

constant_decl:
| labels(lident_rich) cast preceded(EQUAL,term)?
    {
      let loc = floc $startpos $endpos in
      let named_ident =
        ($1.id_str, str_of_labs $1.id_lab) in
      match $3 with
      | None ->
         mak_logic loc [named_ident] (Some $2) []
      | Some t ->
         mk_function t $2 loc named_ident []
    }

function_decl:
| labels(lident_rich) params cast preceded(EQUAL,term)?
    {
      let loc = floc $startpos $endpos in
      let named_ident =
        ($1.id_str, str_of_labs $1.id_lab) in
      match $4 with
      | None ->
         mak_logic loc [named_ident] (Some $3) $2
      | Some t ->
         mk_function t $3 loc named_ident $2
    }

predicate_decl:
| labels(lident_rich) params preceded(EQUAL,term)?
    {
      let loc = floc $startpos $endpos in
      let named_ident =
        ($1.id_str, str_of_labs $1.id_lab) in
      match $3 with
      | None ->
         mak_logic loc [named_ident] None $2
      | Some t ->
         mk_pred t $2 loc named_ident
    }

with_logic_decl:
| WITH labels(lident_rich) params cast? preceded(EQUAL,term)?
    {
      let loc = floc $startpos $endpos in
      let named_ident =
        ($2.id_str, str_of_labs $2.id_lab) in
      match $4, $5 with
      | None, None ->
         mak_logic loc [named_ident] None $3
      | None, Some t ->
         mk_pred t $3 loc named_ident
      | Some t, None ->
         mak_logic loc [named_ident] (Some t) $3
      | Some t0, Some t1 ->
         mk_function t1 t0 loc
           named_ident $3
    }


(* Type expressions *)

ty:
| ty_arg          { $1 }
| lqualid ty_arg+ { mk_tyapp $1 $2 }


ty_arg:
| lqualid
    { mk_tyapp $1 [] }
| LEFTPAR comma_list2(ty) RIGHTPAR
    { mk_tuple $2 (floc $startpos $endpos) }
| LEFTPAR RIGHTPAR
    { mk_tuple [] (floc $startpos $endpos) }
| LEFTPAR ty RIGHTPAR               { $2 }

cast:
| COLON ty  { $2 }

(* Parameters and binders *)

(* [param] and [binder] below must have the same grammar
   and raise [Error] in the same cases. Interpretaion of
   single-standing untyped [Qident]'s is different: [param]
   treats them as type expressions, [binder], as parameter
   names, whose type must be inferred. *)

params:  param*  { List.concat $1 }

                   (*binders: binder+ { List.concat $1  }*)

param:
| anon_binder
    { error_param (floc $startpos $endpos) }
| ty_arg
    { [ floc $startpos $endpos, None, $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { [ floc $startpos $endpos, None, $3] }
| ty_arg label label*
    { error_loc (floc $startpos $endpos) }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match $2 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match $3 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { List.map (fun (l,i) ->  (l, i, $3)) $2 }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { List.map (fun (l,i) ->  (l, i, $4)) $3 }

binder_vars:
| binder_vars_head  { List.rev $1 }
| binder_vars_rest  { $1 }

binder_vars_rest:
| binder_vars_head label label* binder_var*
    { List.rev_append (match $1 with
        | (l, Some id) :: bl ->
            let l3 = floc $startpos($3) $endpos($3) in
            (Why3_loc.join l l3, Some (add_lab id ($2::$3))) :: bl
        | _ -> assert false) $4 }
| binder_vars_head anon_binder binder_var*
   { List.rev_append $1 ($2 :: $3) }
| anon_binder binder_var*
   { $1 :: $2 }

binder_vars_head:
| ty {
    let of_id id = id.id_loc, Some id in
    let push acc = function
      | Parsed.PPTexternal ([], s, _)
        -> (of_id (mk_id s $startpos $endpos)):: acc
      | _ -> Why3_loc.error ~loc:(floc $startpos $endpos) Error in
    match $1 with
    | Parsed.PPTexternal (l, s, _) ->
       List.fold_left push [of_id (mk_id s $startpos $endpos)] l
      | _ -> Why3_loc.error ~loc:(floc $startpos $endpos) Error }

binder_var:
| labels(lident_nq) { floc $startpos $endpos, Some $1 }
| anon_binder       { $1 }

anon_binder:
| UNDERSCORE        { floc $startpos $endpos, None }

(* Logical terms *)

mk_term(X): d = X { mk_term d $startpos $endpos }

term: t = mk_term(term_) { t }

term_:
| term_arg_
    { $1 }
| NOT term
    { mk_not (floc $startpos $endpos) $2 }
| prefix_op term %prec prec_prefix_op
                    { match $1 with
                      | {id_str = "prefix -"}
                      | {id_str = "infix -"} ->
                         mk_minus (floc $startpos $endpos) $2
                      | _ -> Format.eprintf "TODO@."; assert false
                    }
| l = term ; o = bin_op ; r = term
    { o (floc $startpos $endpos) l r }
| l = term ; o = infix_op ; r = term
    { mk_infix_ident o (floc $startpos $endpos) l r }
| term_arg located(term_arg)+ (* FIXME/TODO: "term term_arg" *)
    { let join f (a,_,e) =
        mk_term (mk_apply (floc $startpos $endpos) f a) $startpos e in
      (List.fold_left join $1 $2) }
| IF term THEN term ELSE term
    { mk_ite (floc $startpos $endpos) $2 $4 $6 }
| LET pattern EQUAL term IN term
    {
      let loc =  (floc $startpos $endpos) in
      match $2 with
      | Pvar id ->
         mk_let loc id.id_str $4 $6
      | Pwild ->
         mk_let  loc (id_anonymous loc).id_str $4 $6
      | Ptuple [] ->
         mk_let  loc (id_anonymous loc).id_str
           (mk_type_cast loc $4 (mk_tuple [] loc)) $6
      | Pcast (Pvar id, ty) ->
         mk_let loc id.id_str (mk_type_cast loc $4 ty) $6
      | Pcast (Pwild, ty) ->
         let id = id_anonymous loc in
         mk_let loc id.id_str (mk_type_cast loc $4 ty) $6
      | _ -> assert false
    }
| quant comma_list1(quant_vars) triggers DOT term
    {
      let vs_ty =
        List.map (function (_, Some i, Some pty) -> (i.id_str, "", pty
          ) | _ -> assert false) (List.concat $2) in
      let triggers =
        List.map (fun tl -> (tl, true)) $3 in
      $1 (floc $startpos $endpos) vs_ty triggers [] $5
    }
| EPSILON
    { Why3_loc.errorm "Epsilon terms are currently not supported in WhyML" }
| label term %prec prec_named
    { mk_named (floc $startpos $endpos) $1 $2 }
| term cast
    { mk_type_cast (floc $startpos $endpos) $1 $2 }

term_arg: mk_term(term_arg_) { $1 }
term_dot: mk_term(term_dot_) { $1 }

term_arg_:
| qualid
    { $1 }
| numeral
    {
         mk_int_const (floc $startpos $endpos) $1
    }
| TRUE                      { mk_true_const (floc $startpos $endpos) }
| FALSE                     { mk_false_const (floc $startpos $endpos) }
| quote_uident
    { mk_qualid $1 }
| o = oppref ; a = term_arg
                     { match o with
                      | {id_str = "prefix -"}
                      | {id_str = "infix -"} ->
                         mk_minus (floc $startpos $endpos) a
                      | _ -> Format.eprintf "TODO@."; assert false
                    }
| term_sub_                 { $1 }

term_dot_:
  | lqualid
      { $1 }
  | o = oppref ; a = term_dot
                       { match o with
                      | {id_str = "prefix -"}
                      | {id_str = "infix -"} ->
                         mk_minus (floc $startpos $endpos) a
                      | _ -> Format.eprintf "TODO@."; assert false
                    }
| term_sub_ { $1 }

term_sub_:
  | term_dot DOT lqualid_rich
        { match $3 with
                      | {Parsed.pp_desc = PPvar "prefix -"}
                      | {Parsed.pp_desc = PPvar "infix -"} ->
                         mk_minus (floc $startpos $endpos) $1
                      | _ -> Format.eprintf "TODO@."; assert false
                    }
| LEFTPAR term RIGHTPAR                             { $2 }
| LEFTPAR RIGHTPAR
    { mk_tuple_record [] (floc $startpos $endpos) }
| LEFTPAR comma_list2(term) RIGHTPAR
    { mk_tuple_record $2(floc $startpos $endpos) }


field_list1(X):
| fl = semicolon_list1(separated_pair(lqualid, EQUAL, X)) { fl }

match_cases(X):
| cl = bar_list1(separated_pair(pattern, ARROW, X)) { cl }

quant_vars:
| binder_var+ cast?
                {
                  List.map
                    (fun (l,i) ->
                      match $2 with
                      | Some pty -> l, i, Some pty
                      | _ -> l, i, None)
                  $1
                }

triggers:
| (* epsilon *)                                                 { [] }
| LEFTSQ separated_nonempty_list(BAR,comma_list1(term)) RIGHTSQ { $2 }

%inline bin_op:
| ARROW   { mk_implies }
| LRARROW { mk_iff }
| OR      { mk_or }
| AND     { mk_and }

quant:
| FORALL  { mk_forall }
| EXISTS  { mk_exists }

numeral:
| INTEGER { $1 }


invariant:
| INVARIANT LEFTBRC term RIGHTBRC { $3 }


(* Patterns *)

pattern: pattern_ { $1 }

pattern_:
| pat_conj_                             { $1 }

pat_conj_:
| pat_uni_                              { $1 }

pat_uni_:
| pat_arg_                              { $1 }
| pat_uni_ cast                 { Pcast($1,$2) }

pat_arg_:
| UNDERSCORE                            { Pwild }
| labels(lident_nq)                     { Pvar $1 }
| LEFTPAR RIGHTPAR                      { Ptuple [] }
| LEFTPAR pattern_ RIGHTPAR             { $2 }

(* Why3_idents *)

ident:
| uident { $1 }
| lident { $1 }

ident_nq:
| uident_nq { $1 }
| lident_nq { $1 }

uident:
| UIDENT          { mk_id $1 $startpos $endpos }
| UIDENT_QUOTE    { mk_id $1 $startpos $endpos }

uident_nq:
| UIDENT          { mk_id $1 $startpos $endpos }
| UIDENT_QUOTE    { let loc = floc $startpos($1) $endpos($1) in
                    Why3_loc.errorm ~loc "Symbol %s cannot be user-defined" $1 }

lident:
| LIDENT          { mk_id $1 $startpos $endpos }
| LIDENT_QUOTE    { mk_id $1 $startpos $endpos }

lident_nq:
| LIDENT          { mk_id $1 $startpos $endpos }
| LIDENT_QUOTE    { let loc = floc $startpos($1) $endpos($1) in
                    Why3_loc.errorm ~loc "Symbol %s cannot be user-defined" $1 }


quote_uident:
| QUOTE_UIDENT  { mk_id ("'" ^ $1) $startpos $endpos }

quote_lident:
| QUOTE_LIDENT  { mk_id $1 $startpos $endpos }

(* Why3_idents + symbolic operation names *)

lident_rich:
| lident_nq     { $1 }
| lident_op_id  { $1 }

lident_op_id:
| LEFTPAR lident_op RIGHTPAR  { mk_id $2 $startpos($2) $endpos($2) }
| LEFTPAR_STAR_RIGHTPAR
    { (* parentheses are removed from the location *)
      let s = let s = $startpos in { s with pos_cnum = s.pos_cnum + 1 } in
      let e = let e = $endpos   in { e with pos_cnum = e.pos_cnum - 1 } in
      mk_id (infix "*") s e }

lident_op:
| op_symbol               { infix $1 }
| op_symbol UNDERSCORE    { prefix $1 }
| EQUAL                   { infix "=" }
| OPPREF                  { prefix $1 }

op_symbol:
| OP1 { $1 }
| OP2 { $1 }
| OP3 { $1 }
| OP4 { $1 }
| LT  { "<" }
| GT  { ">" }

%inline oppref:
| o = OPPREF { mk_id (prefix o)  $startpos $endpos }

prefix_op:
| op_symbol { mk_id (prefix $1)  $startpos $endpos }

%inline infix_op:
| o = OP1   { mk_id (infix o)    $startpos $endpos }
| o = OP2   { mk_id (infix o)    $startpos $endpos }
| o = OP3   { mk_id (infix o)    $startpos $endpos }
| o = OP4   { mk_id (infix o)    $startpos $endpos }
| EQUAL     { mk_id (infix "=")  $startpos $endpos }
| LTGT      { mk_id (infix "<>") $startpos $endpos }
| LT        { mk_id (infix "<")  $startpos $endpos }
| GT        { mk_id (infix ">")  $startpos $endpos }

(* Qualified idents *)

qualid:
| uident                    { mk_qualid $1 }
| lident                    { mk_qualid $1 }
| lident_op_id              { mk_qualid $1 }
| uqualid DOT uident        { mk_qualid $3 }
| uqualid DOT lident        { mk_qualid $3 }
| uqualid DOT lident_op_id  { mk_qualid $3 }

lqualid_rich:
| lident                    { mk_qualid $1 }
| lident_op_id              { mk_qualid $1 }
| uqualid DOT lident        { mk_qualid $3 }
| uqualid DOT lident_op_id  { mk_qualid $3 }

lqualid:
| lident              { mk_qualid $1 }
| uqualid DOT lident  { mk_qualid $3 }

uqualid:
| uident              { mk_qualid $1 }
| uqualid DOT uident  { mk_qualid $3 }

(* Theory/Module names *)

tqualid:
| uident                { mk_qualid $1 }
| any_qualid DOT uident { mk_qualid $3 }

any_qualid:
| sident                { $1 }
| any_qualid DOT sident { $3 }

sident:
| ident   { mk_qualid $1 }
| STRING  { mk_qualid (mk_id $1 $startpos $endpos) }

(* Labels and position markers *)

labels(X): X label* { add_lab $1 $2 }

label:
| STRING    { $1 }

(* Miscellaneous *)

bar_list1(X):
| ioption(BAR) ; xl = separated_nonempty_list(BAR, X) { xl }

with_list1(X):
| separated_nonempty_list(WITH, X)  { $1 }

comma_list2(X):
| X COMMA comma_list1(X) { $1 :: $3 }

comma_list1(X):
| separated_nonempty_list(COMMA, X) { $1 }

comma_list0(X):
| xl = separated_list(COMMA, X) { xl }

semicolon_list1(X):
| x = X ; ioption(SEMICOLON)                  { [x] }
| x = X ; SEMICOLON ; xl = semicolon_list1(X) { x :: xl }

located(X): X { $1, $startpos, $endpos }
