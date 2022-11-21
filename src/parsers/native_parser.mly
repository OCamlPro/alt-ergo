/******************************************************************************/
/*                                                                            */
/*     The Alt-Ergo theorem prover                                            */
/*     Copyright (C) 2006-2013                                                */
/*                                                                            */
/*     Sylvain Conchon                                                        */
/*     Evelyne Contejean                                                      */
/*                                                                            */
/*     Francois Bobot                                                         */
/*     Mohamed Iguernelala                                                    */
/*     Stephane Lescuyer                                                      */
/*     Alain Mebsout                                                          */
/*                                                                            */
/*     CNRS - INRIA - Universite Paris Sud                                    */
/*                                                                            */
/*     This file is distributed under the terms of the Apache Software        */
/*     License version 2.0                                                    */
/*                                                                            */
/*  ------------------------------------------------------------------------  */
/*                                                                            */
/*     Alt-Ergo: The SMT Solver For Software Verification                     */
/*     Copyright (C) 2013-2017 --- OCamlPro SAS                               */
/*                                                                            */
/*     This file is distributed under the terms of the Apache Software        */
/*     License version 2.0                                                    */
/*                                                                            */
/******************************************************************************/

%{
  [@@@ocaml.warning "-33"]
  open AltErgoLib
  open Options
  open Parsed_interface
%}

/* Tokens */

%token <string> ID
%token <string> QM_ID
%token <string> INTEGER
%token <Num.num> NUM
%token <string> STRING
%token MATCH WITH THEORY EXTENDS END QM
%token AND LEFTARROW RIGHTARROW AC AT AXIOM CASESPLIT REWRITING
%token BAR HAT
%token BOOL COLON COMMA PV DISTINCT DOT SHARP ELSE OF EOF EQUAL
%token EXISTS FALSE VOID FORALL FUNC GE CHECK_VALID CHECK_SAT GT CHECK CUT
%token IF IN INT BITV MAPS_TO
%token LE LET LEFTPAR LEFTSQ LEFTBR LOGIC LRARROW XOR LT MINUS
%token NOT NOTEQ OR PERCENT PLUS PRED PROP
%token QUOTE REAL UNIT
%token RIGHTPAR RIGHTSQ RIGHTBR
%token SLASH POW POWDOT
%token THEN TIMES TRUE TYPE

/* Precedences */

%nonassoc IN
%nonassoc prec_forall prec_exists
%right RIGHTARROW LRARROW XOR
%right OR
%right AND
%nonassoc prec_ite
%left prec_relation EQUAL NOTEQ LT LE GT GE
%left PLUS MINUS
%left TIMES SLASH PERCENT POW POWDOT AT
%nonassoc HAT
%nonassoc uminus
%nonassoc NOT
%right prec_named
%nonassoc CHECK CUT


/* Entry points */

%type <AltErgoLib.Parsed.lexpr list * bool> trigger_parser
%start trigger_parser

%type <AltErgoLib.Parsed.lexpr> lexpr_parser
%start lexpr_parser

%type <AltErgoLib.Parsed.file> file_parser
%start file_parser
%%

file_parser:
| decls = list1_decl EOF { decls }
| EOF { [] }

trigger_parser:
| trigger = trigger EOF { trigger }

lexpr_parser:
| e = lexpr EOF { e }

list1_decl:
| decl = decl { [decl] }
| decl = decl decls = list1_decl { decl :: decls }

decl:
| THEORY th_id = ident EXTENDS th_ext = ident EQUAL th_body = theory_elts END
   { mk_theory ($startpos, $endpos) th_id th_ext th_body }

| TYPE ty_vars = type_vars ty = ident
    { mk_abstract_type_decl ($startpos, $endpos) ty_vars ty }

| TYPE ty_vars = type_vars ty = ident EQUAL enum = list1_constructors_sep_bar
   others = and_recursive_opt
    {
      match others with
        | [] ->
           mk_algebraic_type_decl ($startpos, $endpos) ty_vars ty enum
        | l ->
           let l = (($startpos, $endpos), ty_vars, ty, enum) :: l in
           let l =
             List.map
               (fun (a, b, c, d) ->
                 match mk_algebraic_type_decl a b c d with
                 | Parsed.TypeDecl [e] -> e
                 | _ -> assert false
               ) l
           in
           mk_rec_type_decl l
    }

| TYPE ty_vars = type_vars ty = ident EQUAL record = record_type
   { mk_record_type_decl ($startpos, $endpos) ty_vars ty record }

| LOGIC is_ac = ac_modifier ids = list1_named_ident_sep_comma COLON
   ty = logic_type
   { mk_logic ($startpos, $endpos) is_ac ids ty }

| FUNC app=named_ident LEFTPAR args=list0_logic_binder_sep_comma RIGHTPAR
   COLON ret_ty = primitive_type EQUAL body = lexpr
   { mk_function_def ($startpos, $endpos) app args ret_ty body }

| PRED app = named_ident EQUAL body = lexpr
   { mk_ground_predicate_def ($startpos, $endpos) app body }

| PRED app = named_ident LEFTPAR args = list0_logic_binder_sep_comma RIGHTPAR
   EQUAL body = lexpr
   { mk_non_ground_predicate_def ($startpos, $endpos) app args body }

| AXIOM name = ident COLON body = lexpr
   { mk_generic_axiom ($startpos, $endpos) name body }

| REWRITING name = ident COLON body = list1_lexpr_sep_pv
   { mk_rewriting ($startpos, $endpos) name body }

| CHECK_VALID name = ident COLON body = lexpr
   { mk_goal ($startpos, $endpos) name body }

| CHECK_SAT name = ident COLON body = lexpr
   { mk_check_sat ($startpos, $endpos) name body }

theory_elts:
| /* */  { [] }
| th_elt = theory_elt th_rest = theory_elts { th_elt :: th_rest }

theory_elt:
| AXIOM name = ident COLON body = lexpr
   { mk_theory_axiom ($startpos, $endpos) name body }

| CASESPLIT name = ident COLON body = lexpr
   { mk_theory_case_split ($startpos, $endpos) name body }


ac_modifier:
| /* */ { Symbols.Other }
| AC    { Symbols.Ac }

primitive_type:
| INT  { int_type }
| BOOL { bool_type }
| REAL { real_type }
| UNIT { unit_type }
| BITV LEFTSQ sz = INTEGER RIGHTSQ { mk_bitv_type sz }

| ext_ty = ident { mk_external_type ($startpos, $endpos) [] ext_ty }

| alpha = type_var { mk_var_type ($startpos, $endpos) alpha }

| par = primitive_type ext_ty = ident
   { mk_external_type ($startpos(ext_ty), $endpos(ext_ty)) [par] ext_ty }

| LEFTPAR pars = list1_primitive_type_sep_comma RIGHTPAR ext_ty = ident
   { mk_external_type ($startpos(ext_ty), $endpos(ext_ty)) pars ext_ty }

logic_type:
| ty_list = list0_primitive_type_sep_comma RIGHTARROW PROP
   { mk_logic_type ty_list None }

| PROP { mk_logic_type [] None }

| ty_list = list0_primitive_type_sep_comma RIGHTARROW ret_ty = primitive_type
   { mk_logic_type ty_list (Some ret_ty) }

| ret_ty = primitive_type
   { mk_logic_type [] (Some ret_ty) }

list1_primitive_type_sep_comma:
| ty = primitive_type                                      { [ty] }
| ty = primitive_type COMMA ty_l = list1_primitive_type_sep_comma { ty::ty_l }

list0_primitive_type_sep_comma:
|                                       { [] }
| ty_l = list1_primitive_type_sep_comma { ty_l }

list0_logic_binder_sep_comma:
|                                          { [] }
| binders_l = list1_logic_binder_sep_comma { binders_l }

list1_logic_binder_sep_comma:
| binder = logic_binder
   { [binder] }
| binder = logic_binder COMMA binders_list = list1_logic_binder_sep_comma
   { binder :: binders_list }

logic_binder:
| id = ident COLON ty = primitive_type
    { (($startpos(id), $endpos(id)), id, ty) }

list1_constructors_sep_bar:
| cons = ident algebraic_args { [cons, $2] }
| cons = ident algebraic_args BAR cons_l = list1_constructors_sep_bar
                                             { (cons, $2) :: cons_l }

algebraic_args:
| { [] }
| OF record_type { $2 }

and_recursive_opt:
  | { [] }
  | AND ty_vars = type_vars ty = ident EQUAL enum = list1_constructors_sep_bar
others = and_recursive_opt
    { (($startpos, $endpos), ty_vars, ty, enum) :: others}

lexpr:

| se = simple_expr { se }

/* binary operators */

| se1 = lexpr PLUS se2 = lexpr
   { mk_add ($startpos, $endpos) se1 se2 }

| se1 = lexpr MINUS se2 = lexpr
   { mk_sub ($startpos, $endpos) se1 se2 }

| se1 = lexpr TIMES se2 = lexpr
   { mk_mul ($startpos, $endpos) se1 se2 }

| se1 = lexpr SLASH se2 = lexpr
   { mk_div ($startpos, $endpos) se1 se2 }

| se1 = lexpr PERCENT se2 = lexpr
   { mk_mod ($startpos, $endpos) se1 se2 }

| se1 = lexpr POW se2 = lexpr
   { mk_pow_int ($startpos, $endpos) se1 se2 }

| se1 = lexpr POWDOT se2 = lexpr
   { mk_pow_real ($startpos, $endpos) se1 se2 }

| se1 = lexpr AND se2 = lexpr
   { mk_and ($startpos, $endpos) se1 se2 }

| se1 = lexpr OR se2 = lexpr
   { mk_or ($startpos, $endpos) se1 se2 }

| se1 = lexpr XOR se2 = lexpr
   { mk_xor ($startpos, $endpos) se1 se2 }

| se1 = lexpr LRARROW se2 = lexpr
   { mk_iff ($startpos, $endpos) se1 se2 }

| se1 = lexpr RIGHTARROW se2 = lexpr
   { mk_implies ($startpos, $endpos) se1 se2 }

| se1 = lexpr LT se2 = lexpr %prec prec_relation
   { mk_pred_lt ($startpos, $endpos) se1 se2 }

| se1 = lexpr LE se2 = lexpr %prec prec_relation
   { mk_pred_le ($startpos, $endpos) se1 se2 }

| se1 = lexpr GT se2 = lexpr %prec prec_relation
   { mk_pred_gt ($startpos, $endpos) se1 se2 }

| se1 = lexpr GE se2 = lexpr %prec prec_relation
   { mk_pred_ge ($startpos, $endpos) se1 se2 }

| se1 = lexpr EQUAL se2 = lexpr %prec prec_relation
   { mk_pred_eq ($startpos, $endpos) se1 se2 }

| se1 = lexpr NOTEQ se2 = lexpr %prec prec_relation
   { mk_pred_not_eq ($startpos, $endpos) se1 se2 }

| NOT se = lexpr
   { mk_not ($startpos, $endpos) se }

| MINUS se = lexpr %prec uminus
   { mk_minus ($startpos, $endpos) se }

/* bit vectors */

| LEFTSQ BAR bv_cst = INTEGER BAR RIGHTSQ
    { mk_bitv_const ($startpos, $endpos) bv_cst }

| e = lexpr HAT LEFTBR i = INTEGER COMMA j = INTEGER RIGHTBR
   { mk_bitv_extract ($startpos, $endpos) e i j }

| e1 = lexpr AT e2 = lexpr
   { mk_bitv_concat ($startpos, $endpos) e1 e2 }

/* predicate or function calls */

| DISTINCT LEFTPAR dist_l = list2_lexpr_sep_comma RIGHTPAR
   { mk_distinct ($startpos, $endpos) dist_l }

| IF cond = lexpr THEN br1 = lexpr ELSE br2 = lexpr %prec prec_ite
   { mk_ite ($startpos, $endpos) cond br1 br2 }

| FORALL quant_vars = list1_multi_logic_binder
   triggers = triggers filters = filters DOT body = lexpr %prec prec_forall
   {
     let vs_ty =
       List.map (fun (vs, ty) ->
         List.map (fun (v, name) -> v, name, ty) vs) quant_vars
     in
     let vs_ty = List.flatten vs_ty in
     mk_forall ($startpos, $endpos) vs_ty triggers filters body
   }

| EXISTS quant_vars = list1_multi_logic_binder
   triggers = triggers filters = filters DOT body = lexpr %prec prec_exists
   {
     let vs_ty =
       List.map (fun (vs, ty) ->
         List.map (fun (v, name) -> v, name, ty) vs) quant_vars
     in
     let vs_ty = List.flatten vs_ty in
     mk_exists ($startpos, $endpos) vs_ty triggers filters body
   }

| name = STRING COLON e = lexpr %prec prec_named
   { mk_named ($startpos, $endpos) name e }

| LET binders = let_binders IN e2 = lexpr
   { mk_let ($startpos, $endpos) binders e2 }

| CHECK e = lexpr
   { mk_check ($startpos, $endpos) e }

| CUT e = lexpr
   { mk_cut ($startpos, $endpos) e }

/* match */
| MATCH e = lexpr WITH cases = list1_match_cases END
    { mk_match ($startpos, $endpos) e (List.rev cases) }


list1_match_cases:
|     p = simple_pattern RIGHTARROW e = lexpr { [p, e]}
| BAR p = simple_pattern RIGHTARROW e = lexpr { [p, e]}
| l = list1_match_cases BAR p = simple_pattern RIGHTARROW e = lexpr
    { (p,e) :: l }

simple_pattern:
| id = ident { mk_pattern ($startpos, $endpos) id [] }
| app = ident LEFTPAR args = list1_string_sep_comma RIGHTPAR
   { mk_pattern ($startpos, $endpos) app args }


let_binders:
| binder = ident EQUAL e = lexpr { [binder, e] }
| binder = ident EQUAL e = lexpr COMMA l = let_binders { (binder, e) :: l }

simple_expr :
| i = INTEGER { mk_int_const ($startpos, $endpos) i }
| i = NUM     { mk_real_const ($startpos, $endpos) i }
| TRUE        { mk_true_const ($startpos, $endpos) }
| FALSE       { mk_false_const ($startpos, $endpos) }
| VOID        { mk_void ($startpos, $endpos) }
| var = ident { mk_var ($startpos, $endpos) var }

/* records */

| LEFTBR labels = list1_label_expr_sep_PV RIGHTBR
   { mk_record ($startpos, $endpos) labels }

| LEFTBR se = simple_expr WITH labels = list1_label_expr_sep_PV RIGHTBR
   { mk_with_record ($startpos, $endpos) se labels }

| se = simple_expr DOT label = ident
   { mk_dot_record ($startpos, $endpos) se label }

/* function or predicat calls */

| app = ident LEFTPAR args = list0_lexpr_sep_comma RIGHTPAR
   { mk_application ($startpos, $endpos) app args }

/* arrays */

| se = simple_expr LEFTSQ e = lexpr RIGHTSQ
   { mk_array_get ($startpos, $endpos) se e }

| se = simple_expr LEFTSQ assigns = array_assignements RIGHTSQ
    {
      let acc, l =
        match assigns with
	| [] -> assert false
	| (i, v)::l -> mk_array_set ($startpos, $endpos) se i v, l
      in
      List.fold_left (fun acc (i,v) ->
          mk_array_set ($startpos, $endpos) acc i v) acc l
    }

| LEFTPAR e = lexpr RIGHTPAR
   { e }

| se = simple_expr COLON ty = primitive_type
    {  mk_type_cast ($startpos, $endpos) se ty }

| se = simple_expr QM id = ident
    { mk_algebraic_test ($startpos, $endpos) se id }

| se = simple_expr id = QM_ID
    { mk_algebraic_test ($startpos, $endpos) se id }

| se = simple_expr SHARP label = ident
   { mk_algebraic_project ($startpos, $endpos) ~guarded:true se label }
array_assignements:
| assign = array_assignement
   { [assign] }
| assign = array_assignement COMMA assign_l = array_assignements
   { assign :: assign_l }

array_assignement:
|  e1 = lexpr LEFTARROW e2 = lexpr { e1, e2 }

triggers:
|                                       { [] }
| LEFTSQ trigs = list1_trigger_sep_bar RIGHTSQ  { trigs }


filters:
|
    { [] }
| LEFTBR filt = lexpr RIGHTBR
   { [filt] }
| LEFTBR filt = lexpr COMMA filt_l = list0_lexpr_sep_comma RIGHTBR
   { filt :: filt_l }

list1_trigger_sep_bar:
| trig = trigger { [trig] }
| trig = trigger BAR trigs = list1_trigger_sep_bar { trig :: trigs }

trigger:
|  terms = list1_lexpr_or_dom_sep_comma
   { terms, true (* true <-> user-given trigger *) }

list1_lexpr_sep_pv:
| e = lexpr                              { [e] }
| e = lexpr PV                           { [e] }
| e = lexpr PV e_l = list1_lexpr_sep_pv  { e :: e_l }

list0_lexpr_sep_comma:
|                       { [] }
| l = list1_lexpr_sep_comma { l }

list1_lexpr_sep_comma:
| e = lexpr                                 { [e] }
| e = lexpr COMMA l = list1_lexpr_sep_comma { e :: l }

list1_lexpr_or_dom_sep_comma:
| ed = lexpr_or_dom                             { [ed] }
| ed = lexpr_or_dom COMMA edl = list1_lexpr_or_dom_sep_comma { ed :: edl }

lexpr_or_dom:
| e = lexpr
   { e }
| e = lexpr IN lbr = sq lbnd = bound COMMA rbnd = bound rbr = sq
   { mk_in_interval ($startpos, $endpos) e lbr lbnd rbnd rbr }
| id = ident MAPS_TO e = lexpr
   { mk_maps_to ($startpos, $endpos) id e }


sq:
| LEFTSQ {true}
| RIGHTSQ {false}

bound:
| QM                 { mk_var ($startpos, $endpos) "?" }
| id = QM_ID         { mk_var ($startpos, $endpos) id }
| id = ID            { mk_var ($startpos, $endpos) id }
| i = INTEGER        { mk_int_const ($startpos, $endpos) i }
| i = NUM            { mk_real_const ($startpos, $endpos) i }
| MINUS i = INTEGER  { mk_int_const ($startpos, $endpos) i }
| MINUS i = NUM      { mk_real_const ($startpos, $endpos) i }

list2_lexpr_sep_comma:
| e1 = lexpr COMMA e2 = lexpr                 { [e1; e2] }
| e = lexpr COMMA el = list2_lexpr_sep_comma  { e :: el   }

record_type:
| LEFTBR labels = list1_label_sep_PV RIGHTBR { labels }

list1_label_sep_PV:
| label_typed = label_with_type                         { [label_typed] }
| lt = label_with_type PV list_lt = list1_label_sep_PV   { lt :: list_lt }

label_with_type:
| id = ident COLON ty = primitive_type { id, ty }


list1_label_expr_sep_PV:
| id = ident EQUAL e = lexpr
   { [id, e] }
| id = ident EQUAL e = lexpr PV l = list1_label_expr_sep_PV
   { (id, e) :: l }

type_var:
| QUOTE alpha = ident { alpha }

type_vars:
|           { [] }
| alpha = type_var  { [alpha] }
| LEFTPAR l = list1_type_var_sep_comma RIGHTPAR { l }

list1_type_var_sep_comma:
| alpha = type_var                                { [alpha] }
          | alpha = type_var COMMA l = list1_type_var_sep_comma { alpha :: l }

ident:
| id = ID { id }

multi_logic_binder:
| binders = list1_named_ident_sep_comma COLON ty = primitive_type
    { binders, ty }

list1_multi_logic_binder:
| binders = multi_logic_binder
   { [binders] }
| binders = multi_logic_binder COMMA l = list1_multi_logic_binder
   { binders :: l }

list1_named_ident_sep_comma:
| id = named_ident                                   { [id] }
       | id = named_ident COMMA l = list1_named_ident_sep_comma { id :: l }

list1_string_sep_comma:
| id = ident
    { [ id ] }
| id = ident COMMA l = list1_string_sep_comma { id :: l  }

named_ident:
| id = ID { id, "" }
| id = ID str = STRING { id, str }
