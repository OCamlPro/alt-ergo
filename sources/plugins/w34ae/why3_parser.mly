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
(*module Increment = struct
  let stack = Stack.create ()
  let open_file inc = Stack.push inc stack
  let close_file () = ignore (Stack.pop stack)
  let open_theory id = (Stack.top stack).Why3_ptree.open_theory id
  let close_theory () = (Stack.top stack).Why3_ptree.close_theory ()
  let open_module id = (Stack.top stack).Why3_ptree.open_module id
  let close_module () = (Stack.top stack).Why3_ptree.close_module ()
  let open_namespace n = (Stack.top stack).Why3_ptree.open_namespace n
  let close_namespace l b = (Stack.top stack).Why3_ptree.close_namespace l b
  let new_decl loc d = (Stack.top stack).Why3_ptree.new_decl loc d
  let new_pdecl loc d = (Stack.top stack).Why3_ptree.new_pdecl loc d
  let use_clone loc use = (Stack.top stack).Why3_ptree.use_clone loc use
end
 *)

open Lexing

module Increment = struct
  (*let stack = Stack.create ()*)
  let debug = false
  let open_file inc = if debug then print_string "open_file\n" else ()
  let close_file () = if debug then print_string "close_file\n" else ()
  let open_theory id = if debug then print_string "open_theory\n" else () 
  let close_theory () = if debug then print_string "close_theory\n" else ()
  let open_module id =  if debug then print_string "open_module\n" else ()
  let close_module () = if debug then print_string "close_module\n" else ()
  let open_namespace n = if debug then print_string "open_namespace\n" else ()
  let close_namespace l b = if debug then print_string "close_namespace\n" else ()
  let new_decl loc d = if debug then print_string "new_decl\n" else ()
  let new_pdecl loc d = if debug then print_string "new_pdecl\n" else ()
  let use_clone loc use = if debug then print_string "use_clone\n" else ()
end


  open Why3_ptree

  let infix  s = "infix "  ^ s
  let prefix s = "prefix " ^ s
  let mixfix s = "mixfix " ^ s

  let qualid_last = function Qident x | Qdot (_, x) -> x.id_str

  let floc s e = Why3_loc.extract (s,e)

  let model_label = Why3_ident.create_label "model"
  let model_projected = Why3_ident.create_label "model_projected"

  let is_model_label l =
    match l with
    | Lpos _ -> false
    | Lstr lab ->
      (lab = model_label) || (lab = model_projected)


  let model_lab_present labels =
    try
      ignore(List.find is_model_label labels);
      true
    with Not_found ->
      false

  let model_trace_regexp = Str.regexp "model_trace:"

  let is_model_trace_label l =
    match l with
    | Lpos _ -> false
    | Lstr lab ->
      try
	ignore(Str.search_forward model_trace_regexp lab.Why3_ident.lab_string 0);
	true
      with Not_found -> false

  let model_trace_lab_present labels =
    try
      ignore(List.find is_model_trace_label labels);
      true
    with Not_found ->
      false

  let add_model_trace name labels =
    if (model_lab_present labels) && (not (model_trace_lab_present labels)) then
      (Lstr (Why3_ident.create_label ("model_trace:" ^ name)))::labels
    else
      labels

  let add_lab id l =
    let l = add_model_trace id.id_str l in
    { id with id_lab = l }

  let id_anonymous loc = { id_str = "_"; id_lab = []; id_loc = loc }

  let mk_id id s e = { id_str = id; id_lab = []; id_loc = floc s e }

  let get_op s e = Qident (mk_id (mixfix "[]") s e)
  let set_op s e = Qident (mk_id (mixfix "[<-]") s e)
  let sub_op s e = Qident (mk_id (mixfix "[_.._]") s e)
  let above_op s e = Qident (mk_id (mixfix "[_..]") s e)
  let below_op s e = Qident (mk_id (mixfix "[.._]") s e)

  let mk_pat  d s e = { pat_desc  = d; pat_loc  = floc s e }
  let mk_term d s e = { term_desc = d; term_loc = floc s e }
  let mk_expr d s e = { expr_desc = d; expr_loc = floc s e }

  let variant_union v1 v2 = match v1, v2 with
    | _, [] -> v1
    | [], _ -> v2
    | _, ({term_loc = loc},_)::_ -> Why3_loc.errorm ~loc
        "multiple `variant' clauses are not allowed"

  let empty_spec = {
    sp_pre     = [];
    sp_post    = [];
    sp_xpost   = [];
    sp_reads   = [];
    sp_writes  = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
  }

  let spec_union s1 s2 = {
    sp_pre     = s1.sp_pre @ s2.sp_pre;
    sp_post    = s1.sp_post @ s2.sp_post;
    sp_xpost   = s1.sp_xpost @ s2.sp_xpost;
    sp_reads   = s1.sp_reads @ s2.sp_reads;
    sp_writes  = s1.sp_writes @ s2.sp_writes;
    sp_variant = variant_union s1.sp_variant s2.sp_variant;
    sp_checkrw = s1.sp_checkrw || s2.sp_checkrw;
    sp_diverge = s1.sp_diverge || s2.sp_diverge;
  }

(* dead code
  let add_init_mark e =
    let init = { id_str = "Init"; id_lab = []; id_loc = e.expr_loc } in
    { e with expr_desc = Emark (init, e) }
*)

  let small_integer i =
    try match i with
      | Why3_number.IConstDec s -> int_of_string s
      | Why3_number.IConstHex s -> int_of_string ("0x"^s)
      | Why3_number.IConstOct s -> int_of_string ("0o"^s)
      | Why3_number.IConstBin s -> int_of_string ("0b"^s)
    with Failure _ -> raise Error

  let error_param loc =
    Why3_loc.errorm ~loc "cannot determine the type of the parameter"

  let error_loc loc = Why3_loc.error ~loc Error

  let () = Why3_exn_printer.register (fun fmt exn -> match exn with
    | Error -> Format.fprintf fmt "syntax error"
    | _ -> raise exn)

%}

(* Tokens *)

%token <string> LIDENT LIDENT_QUOTE UIDENT UIDENT_QUOTE
%token <Why3_ptree.integer_constant> INTEGER
%token <string> OP1 OP2 OP3 OP4 OPPREF
%token <Why3_ptree.real_constant> REAL
%token <string> STRING
%token <Why3_loc.position> POSITION
%token <string> QUOTE_UIDENT QUOTE_LIDENT OPAQUE_QUOTE_LIDENT

(* keywords *)

%token AS AXIOM BY CLONE COINDUCTIVE CONSTANT
%token ELSE END EPSILON EXISTS EXPORT FALSE FLOAT FORALL FUNCTION
%token GOAL IF IMPORT IN INDUCTIVE LEMMA
%token LET MATCH META NAMESPACE NOT PROP PREDICATE RANGE
%token SO THEN THEORY TRUE TYPE USE WITH

(* program keywords *)

%token ABSTRACT ABSURD ANY ASSERT ASSUME BEGIN CHECK
%token DIVERGES DO DONE DOWNTO ENSURES EXCEPTION FOR
%token FUN GHOST INVARIANT LOOP MODEL MODULE MUTABLE
%token PRIVATE RAISE RAISES READS REC REQUIRES RETURNS
%token TO TRY VAL VARIANT WHILE WRITES

(* symbols *)

%token AND ARROW
%token BAR
%token COLON COMMA
%token DOT DOTDOT EQUAL LAMBDA LT GT LTGT
%token LEFTPAR LEFTPAR_STAR_RIGHTPAR LEFTSQ
%token LARROW LRARROW OR
%token RIGHTPAR RIGHTSQ
%token UNDERSCORE

%token EOF

(* program symbols *)

%token AMPAMP BARBAR LEFTBRC RIGHTBRC SEMICOLON

(* Precedences *)

%nonassoc IN
%nonassoc below_SEMI
%nonassoc SEMICOLON
%nonassoc LET VAL
%nonassoc prec_no_else
%nonassoc DOT ELSE GHOST
%nonassoc prec_named
%nonassoc COLON

%right ARROW LRARROW
%right BY SO
%right OR BARBAR
%right AND AMPAMP
%nonassoc NOT
%left EQUAL LTGT LT GT OP1
%nonassoc LARROW
%nonassoc RIGHTSQ    (* stronger than <- for e1[e2 <- e3] *)
%left OP2
%left OP3
%left OP4
%nonassoc prec_prefix_op
%nonassoc LEFTSQ
%nonassoc OPPREF

(* Entry points *)

(*%start <Why3_ptree.incremental -> unit> open_file
%start <unit> logic_file program_file*)
%start <(Why3_ptree.ident * (Why3_ptree.decl option * Why3_loc.position) list) list> logic_file

%type <Parsed.lexpr list * bool> trigger_parser
%start trigger_parser

%type <Parsed.lexpr> lexpr_parser
%start lexpr_parser

%type <Parsed.file> file_parser
%start file_parser
%%

file_parser:
| logic_file { AstConversion.file_parser $1 }

lexpr_parser:
| expr { AstConversion.lexpr_parser $1 }

trigger_parser:
| lexpr_parser {$1, true}

(* Theories, modules, namespaces *)

open_file:
(* Dummy token. Menhir does not accept epsilon. *)
| EOF { Increment.open_file }

logic_file:
(*| theory* EOF   { Increment.close_file () }*)
| theory* EOF   { Increment.close_file (); $1 }

program_file:
| theory_or_module* EOF { Increment.close_file () }

theory:
(*| theory_head theory_decl* END  { Increment.close_theory () }*)
| theory_head theory_decl* END  { Increment.close_theory (); ($1, $2) }

theory_or_module:
| theory                        { () }
| module_head module_decl* END  { Increment.close_module () }

theory_head:
(*| THEORY labels(uident_nq)  { Increment.open_theory $2 }*)
| THEORY labels(uident_nq)  { Increment.open_theory $2;  $2 }

module_head:
| MODULE labels(uident_nq)  { Increment.open_module $2 }

theory_decl:
(*| decl            { Increment.new_decl  (floc $startpos $endpos) $1 }
| use_clone       { Increment.use_clone (floc $startpos $endpos) $1 }
| namespace_head theory_decl* END
    { Increment.close_namespace (floc $startpos($1) $endpos($1)) $1 }
*)
    | decl { Increment.new_decl (floc $startpos $endpos) $1; (Some $1, (floc $startpos $endpos)) }
    | use_clone       { Increment.use_clone (floc $startpos $endpos) $1; (None, (floc $startpos $endpos)) }
| namespace_head theory_decl* END
    { Increment.close_namespace (floc $startpos($1) $endpos($1)) $1; (None, (floc $startpos($1) $endpos($1))) }


module_decl:
| decl            { Increment.new_decl  (floc $startpos $endpos) $1 }
| pdecl           { Increment.new_pdecl (floc $startpos $endpos) $1 }
| use_clone       { Increment.use_clone (floc $startpos $endpos) $1 }
| namespace_head module_decl* END
    { Increment.close_namespace (floc $startpos($1) $endpos($1)) $1 }

namespace_head:
| NAMESPACE boption(IMPORT) uident_nq
   { Increment.open_namespace $3.id_str; $2 }

(* Use and clone *)

use_clone:
| USE use                                 { ($2, None) }
| CLONE use                               { ($2, Some []) }
| CLONE use WITH comma_list1(clone_subst) { ($2, Some $4) }

use:
| boption(IMPORT) tqualid
    { { use_theory = $2; use_import = Some ($1, qualid_last $2) } }
| boption(IMPORT) tqualid AS uident
    { { use_theory = $2; use_import = Some ($1, $4.id_str) } }
| EXPORT tqualid
    { { use_theory = $2; use_import = None } }

clone_subst:
| NAMESPACE ns EQUAL ns         { CSns    (floc $startpos $endpos, $2,$4) }
| TYPE qualid ty_var* EQUAL ty  { CStsym  (floc $startpos $endpos, $2,$3,$5) }
| CONSTANT  qualid EQUAL qualid { CSfsym  (floc $startpos $endpos, $2,$4) }
| FUNCTION  qualid EQUAL qualid { CSfsym  (floc $startpos $endpos, $2,$4) }
| PREDICATE qualid EQUAL qualid { CSpsym  (floc $startpos $endpos, $2,$4) }
| VAL       qualid EQUAL qualid { CSvsym  (floc $startpos $endpos, $2,$4) }
| LEMMA     qualid              { CSlemma (floc $startpos $endpos, $2) }
| GOAL      qualid              { CSgoal  (floc $startpos $endpos, $2) }

ns:
| uqualid { Some $1 }
| DOT     { None }

(* Theory declarations *)

decl:
| TYPE with_list1(type_decl)                { Dtype $2 }
| TYPE late_invariant                       { Dtype [$2] }
| CONSTANT  constant_decl                   { Dlogic [$2] }
| FUNCTION  function_decl  with_logic_decl* { Dlogic ($2::$3) }
| PREDICATE predicate_decl with_logic_decl* { Dlogic ($2::$3) }
| INDUCTIVE   with_list1(inductive_decl)    { Dind (Why3_decl.Ind, $2) }
| COINDUCTIVE with_list1(inductive_decl)    { Dind (Why3_decl.Coind, $2) }
| AXIOM labels(ident_nq) COLON term         { Dprop (Why3_decl.Paxiom, $2, $4) }
| LEMMA labels(ident_nq) COLON term         { Dprop (Why3_decl.Plemma, $2, $4) }
| GOAL  labels(ident_nq) COLON term         { Dprop (Why3_decl.Pgoal, $2, $4) }
| META sident comma_list1(meta_arg)         { Dmeta ($2, $3) }

meta_arg:
| TYPE      ty      { Mty $2 }
| CONSTANT  qualid  { Mfs $2 }
| FUNCTION  qualid  { Mfs $2 }
| PREDICATE qualid  { Mps $2 }
| PROP      qualid  { Mpr $2 }
| STRING            { Mstr $1 }
| INTEGER           { Mint (small_integer $1) }

(* Type declarations *)

type_decl:
| labels(lident_nq) ty_var* typedefn
  { let model, vis, def, inv = $3 in
    let vis = if model then Abstract else vis in
    { td_ident = $1; td_params = $2;
      td_model = model; td_vis = vis; td_def = def;
      td_inv = inv; td_loc = floc $startpos $endpos } }

late_invariant:
| labels(lident_nq) ty_var* invariant+
  { { td_ident = $1; td_params = $2;
      td_model = false; td_vis = Public; td_def = TDabstract;
      td_inv = $3; td_loc = floc $startpos $endpos } }

ty_var:
| labels(quote_lident) { $1 }

typedefn:
| (* epsilon *)
    { false, Public, TDabstract, [] }
| model abstract bar_list1(type_case) invariant*
    { $1, $2, TDalgebraic $3, $4 }
| model abstract LEFTBRC semicolon_list1(type_field) RIGHTBRC invariant*
    { $1, $2, TDrecord $4, $6 }
| model abstract ty invariant*
    { $1, $2, TDalias $3, $4 }
(* FIXME: allow negative bounds *)
| EQUAL LT RANGE INTEGER INTEGER GT
    { false, Public,
      TDrange (Why3_number.compute_int $4, Why3_number.compute_int $5), [] }
| EQUAL LT FLOAT INTEGER INTEGER GT
    { false, Public,
      TDfloat (small_integer $4, small_integer $5), [] }

model:
| EQUAL         { false }
| MODEL         { true }

abstract:
| (* epsilon *) { Public }
| PRIVATE       { Private }
| ABSTRACT      { Abstract }

type_field:
| field_modifiers labels(lident_nq) cast
  { { f_ident = $2; f_mutable = fst $1; f_ghost = snd $1;
      f_pty = $3; f_loc = floc $startpos $endpos } }

field_modifiers:
| (* epsilon *) { false, false }
| MUTABLE       { true,  false }
| GHOST         { false, true  }
| GHOST MUTABLE { true,  true  }
| MUTABLE GHOST { true,  true  }

type_case:
| labels(uident_nq) params { floc $startpos $endpos, $1, $2 }

(* Logic declarations *)

constant_decl:
| labels(lident_rich) cast preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = []; ld_type = Some $2;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

function_decl:
| labels(lident_rich) params cast preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = Some $3;
      ld_def = $4; ld_loc = floc $startpos $endpos } }

predicate_decl:
| labels(lident_rich) params preceded(EQUAL,term)?
  { { ld_ident = $1; ld_params = $2; ld_type = None;
      ld_def = $3; ld_loc = floc $startpos $endpos } }

with_logic_decl:
| WITH labels(lident_rich) params cast? preceded(EQUAL,term)?
  { { ld_ident = $2; ld_params = $3; ld_type = $4;
      ld_def = $5; ld_loc = floc $startpos $endpos } }

(* Inductive declarations *)

inductive_decl:
| labels(lident_rich) params ind_defn
  { { in_ident = $1; in_params = $2;
      in_def = $3; in_loc = floc $startpos $endpos } }

ind_defn:
| (* epsilon *)             { [] }
| EQUAL bar_list1(ind_case) { $2 }

ind_case:
| labels(ident_nq) COLON term  { floc $startpos $endpos, $1, $3 }

(* Type expressions *)

ty:
| ty_arg          { $1 }
| lqualid ty_arg+ { PTtyapp ($1, $2) }
| ty ARROW ty     { PTarrow ($1, $3) }

ty_arg:
| lqualid                           { PTtyapp ($1, []) }
| quote_lident                      { PTtyvar ($1, false) }
| opaque_quote_lident               { PTtyvar ($1, true) }
| LEFTPAR comma_list2(ty) RIGHTPAR  { PTtuple $2 }
| LEFTPAR RIGHTPAR                  { PTtuple [] }
| LEFTPAR ty RIGHTPAR               { PTparen $2 }

cast:
| COLON ty  { $2 }

(* Parameters and binders *)

(* [param] and [binder] below must have the same grammar
   and raise [Error] in the same cases. Interpretaion of
   single-standing untyped [Qident]'s is different: [param]
   treats them as type expressions, [binder], as parameter
   names, whose type must be inferred. *)

params:  param*  { List.concat $1 }

binders: binder+ { List.concat $1 }

param:
| anon_binder
    { error_param (floc $startpos $endpos) }
| ty_arg
    { [floc $startpos $endpos, None, false, $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { [floc $startpos $endpos, None, true, $3] }
| ty_arg label label*
    { match $1 with
      | PTtyapp (Qident _, []) ->
             error_param (floc $startpos $endpos)
      | _ -> error_loc (floc $startpos($2) $endpos($2)) }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match $2 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match $3 with [l,_] -> error_param l
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, false, $3) $2 }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, true, $4) $3 }

binder:
| anon_binder
    { error_param (floc $startpos $endpos) }
| ty_arg
    { match $1 with
      | PTtyapp (Qident id, [])
      | PTparen (PTtyapp (Qident id, [])) ->
             [floc $startpos $endpos, Some id, false, None]
      | _ -> [floc $startpos $endpos, None, false, Some $1] }
| LEFTPAR GHOST ty RIGHTPAR
    { match $3 with
      | PTtyapp (Qident id, []) ->
             [floc $startpos $endpos, Some id, true, None]
      | _ -> [floc $startpos $endpos, None, true, Some $3] }
| ty_arg label label*
    { match $1 with
      | PTtyapp (Qident id, []) ->
             let id = add_lab id ($2::$3) in
             [floc $startpos $endpos, Some id, false, None]
      | _ -> error_loc (floc $startpos($2) $endpos($2)) }
| LEFTPAR binder_vars_rest RIGHTPAR
    { match $2 with [l,i] -> [l, i, false, None]
      | _ -> error_loc (floc $startpos($3) $endpos($3)) }
| LEFTPAR GHOST binder_vars_rest RIGHTPAR
    { match $3 with [l,i] -> [l, i, true, None]
      | _ -> error_loc (floc $startpos($4) $endpos($4)) }
| LEFTPAR binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, false, Some $3) $2 }
| LEFTPAR GHOST binder_vars cast RIGHTPAR
    { List.map (fun (l,i) -> l, i, true, Some $4) $3 }

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
      | PTtyapp (Qident id, []) -> of_id id :: acc
      | _ -> Why3_loc.error ~loc:(floc $startpos $endpos) Error in
    match $1 with
      | PTtyapp (Qident id, l) -> List.fold_left push [of_id id] l
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
    { match $1 with (* break the infix relation chain *)
      | Tinfix (l,o,r) -> Tinnfix (l,o,r) | d -> d }
| NOT term
    { Tunop (Tnot, $2) }
| prefix_op term %prec prec_prefix_op
    { Tidapp (Qident $1, [$2]) }
| l = term ; o = bin_op ; r = term
    { Tbinop (l, o, r) }
| l = term ; o = infix_op ; r = term
    { Tinfix (l, o, r) }
| term_arg located(term_arg)+ (* FIXME/TODO: "term term_arg" *)
    { let join f (a,_,e) = mk_term (Tapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).term_desc }
| IF term THEN term ELSE term
    { Tif ($2, $4, $6) }
| LET pattern EQUAL term IN term
    { match $2.pat_desc with
      | Pvar id -> Tlet (id, $4, $6)
      | Pwild -> Tlet (id_anonymous $2.pat_loc, $4, $6)
      | Ptuple [] -> Tlet (id_anonymous $2.pat_loc,
          { $4 with term_desc = Tcast ($4, PTtuple []) }, $6)
      | Pcast ({pat_desc = Pvar id}, ty) ->
          Tlet (id, { $4 with term_desc = Tcast ($4, ty) }, $6)
      | Pcast ({pat_desc = Pwild}, ty) ->
          let id = id_anonymous $2.pat_loc in
          Tlet (id, { $4 with term_desc = Tcast ($4, ty) }, $6)
      | _ -> Tmatch ($4, [$2, $6]) }
| MATCH term WITH match_cases(term) END
    { Tmatch ($2, $4) }
| MATCH comma_list2(term) WITH match_cases(term) END
    { Tmatch (mk_term (Ttuple $2) $startpos($2) $endpos($2), $4) }
| quant comma_list1(quant_vars) triggers DOT term
    { Tquant ($1, List.concat $2, $3, $5) }
| EPSILON
    { Why3_loc.errorm "Epsilon terms are currently not supported in WhyML" }
| label term %prec prec_named
    { Tnamed ($1, $2) }
| term cast
    { Tcast ($1, $2) }

term_arg: mk_term(term_arg_) { $1 }
term_dot: mk_term(term_dot_) { $1 }

term_arg_:
| qualid                    { Tident $1 }
| numeral                   { Tconst $1 }
| TRUE                      { Ttrue }
| FALSE                     { Tfalse }
| quote_uident              { Tident (Qident $1) }
| o = oppref ; a = term_arg { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_dot_:
| lqualid                   { Tident $1 }
| o = oppref ; a = term_dot { Tidapp (Qident o, [a]) }
| term_sub_                 { $1 }

term_sub_:
| term_dot DOT lqualid_rich                         { Tidapp ($3,[$1]) }
| LEFTPAR term RIGHTPAR                             { $2.term_desc }
| LEFTPAR RIGHTPAR                                  { Ttuple [] }
| LEFTPAR comma_list2(term) RIGHTPAR                { Ttuple $2 }
| LEFTBRC field_list1(term) RIGHTBRC                { Trecord $2 }
| LEFTBRC term_arg WITH field_list1(term) RIGHTBRC  { Tupdate ($2,$4) }
| term_arg LEFTSQ term RIGHTSQ
    { Tidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ term LARROW term RIGHTSQ
    { Tidapp (set_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT term RIGHTSQ
    { Tidapp (sub_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| term_arg LEFTSQ term DOTDOT RIGHTSQ
    { Tidapp (above_op $startpos($2) $endpos($2), [$1;$3]) }
| term_arg LEFTSQ DOTDOT term RIGHTSQ
    { Tidapp (below_op $startpos($2) $endpos($2), [$1;$4]) }

field_list1(X):
| fl = semicolon_list1(separated_pair(lqualid, EQUAL, X)) { fl }

match_cases(X):
| cl = bar_list1(separated_pair(pattern, ARROW, X)) { cl }

quant_vars:
| binder_var+ cast? { List.map (fun (l,i) -> l, i, false, $2) $1 }

triggers:
| (* epsilon *)                                                 { [] }
| LEFTSQ separated_nonempty_list(BAR,comma_list1(term)) RIGHTSQ { $2 }

%inline bin_op:
| ARROW   { Timplies }
| LRARROW { Tiff }
| OR      { Tor }
| BARBAR  { Tor_asym }
| AND     { Tand }
| AMPAMP  { Tand_asym }
| BY      { Tby }
| SO      { Tso }

quant:
| FORALL  { Tforall }
| EXISTS  { Texists }
| LAMBDA  { Tlambda }

numeral:
| INTEGER { Why3_number.ConstInt $1 }
| REAL    { Why3_number.ConstReal $1 }

(* Program declarations *)

pdecl:
| VAL top_ghost labels(lident_rich) type_v          { Dval ($3, $2, $4) }
| LET top_ghost labels(lident_rich) fun_defn        { Dfun ($3, $2, $4) }
| LET top_ghost labels(lident_rich) EQUAL fun_expr  { Dfun ($3, $2, $5) }
| LET REC with_list1(rec_defn)                      { Drec $3 }
| EXCEPTION labels(uident_nq)                       { Dexn ($2, PTtuple []) }
| EXCEPTION labels(uident_nq) ty                    { Dexn ($2, $3) }

top_ghost:
| (* epsilon *) { Gnone  }
| GHOST         { Gghost }
| LEMMA         { Glemma }

(* Function declarations *)

type_v:
| arrow_type_v  { $1 }
| cast          { PTpure $1 }

arrow_type_v:
| param params tail_type_c  { PTfunc ($1 @ $2, $3) }

tail_type_c:
| single_spec spec arrow_type_v { $3, spec_union $1 $2 }
| COLON simple_type_c           { $2 }

simple_type_c:
| ty spec { PTpure $1, $2 }

(* Function definitions *)

rec_defn:
| top_ghost labels(lident_rich) binders cast? spec EQUAL spec seq_expr
    { $2, $1, ($3, $4, $8, spec_union $5 $7) }

fun_defn:
| binders cast? spec EQUAL spec seq_expr { ($1, $2, $6, spec_union $3 $5) }

fun_expr:
| FUN binders spec ARROW spec seq_expr { ($2, None, $6, spec_union $3 $5) }

(* Program expressions *)

mk_expr(X): d = X { mk_expr d $startpos $endpos }

seq_expr:
| expr %prec below_SEMI   { $1 }
| expr SEMICOLON          { $1 }
| expr SEMICOLON seq_expr { mk_expr (Esequence ($1, $3)) $startpos $endpos }

expr: e = mk_expr(expr_) { e }

expr_:
| expr_arg_
    { match $1 with (* break the infix relation chain *)
      | Einfix (l,o,r) -> Einnfix (l,o,r) | d -> d }
| NOT expr %prec prec_prefix_op
    { Enot $2 }
| prefix_op expr %prec prec_prefix_op
    { Eidapp (Qident $1, [$2]) }
| l = expr ; o = lazy_op ; r = expr
    { Elazy (l,o,r) }
| l = expr ; o = infix_op ; r = expr
    { Einfix (l,o,r) }
| expr_arg located(expr_arg)+ (* FIXME/TODO: "expr expr_arg" *)
    { let join f (a,_,e) = mk_expr (Eapply (f,a)) $startpos e in
      (List.fold_left join $1 $2).expr_desc }
| IF seq_expr THEN expr ELSE expr
    { Eif ($2, $4, $6) }
| IF seq_expr THEN expr %prec prec_no_else
    { Eif ($2, $4, mk_expr (Etuple []) $startpos $endpos) }
| expr LARROW expr
    { match $1.expr_desc with
      | Eidapp (q, [e1]) -> Eassign (e1, q, $3)
      | Eidapp (Qident id, [e1;e2]) when id.id_str = mixfix "[]" ->
          Eidapp (Qident {id with id_str = mixfix "[]<-"}, [e1;e2;$3])
      | _ -> raise Error }
| LET top_ghost pattern EQUAL seq_expr IN seq_expr
    { match $3.pat_desc with
      | Pvar id -> Elet (id, $2, $5, $7)
      | Pwild -> Elet (id_anonymous $3.pat_loc, $2, $5, $7)
      | Ptuple [] -> Elet (id_anonymous $3.pat_loc, $2,
          { $5 with expr_desc = Ecast ($5, PTtuple []) }, $7)
      | Pcast ({pat_desc = Pvar id}, ty) ->
          Elet (id, $2, { $5 with expr_desc = Ecast ($5, ty) }, $7)
      | Pcast ({pat_desc = Pwild}, ty) ->
          let id = id_anonymous $3.pat_loc in
          Elet (id, $2, { $5 with expr_desc = Ecast ($5, ty) }, $7)
      | _ ->
          let e = match $2 with
            | Glemma -> Why3_loc.errorm ~loc:($3.pat_loc)
                "`let lemma' cannot be used with complex patterns"
            | Gghost -> { $5 with expr_desc = Eghost $5 }
            | Gnone -> $5 in
          Ematch (e, [$3, $7]) }
| LET top_ghost labels(lident_op_id) EQUAL seq_expr IN seq_expr
    { Elet ($3, $2, $5, $7) }
| LET top_ghost labels(lident_nq) fun_defn IN seq_expr
    { Efun ($3, $2, $4, $6) }
| LET top_ghost labels(lident_op_id) fun_defn IN seq_expr
    { Efun ($3, $2, $4, $6) }
| LET REC with_list1(rec_defn) IN seq_expr
    { Erec ($3, $5) }
| fun_expr
    { Elam $1 }
| VAL top_ghost labels(lident_rich) mk_expr(val_expr) IN seq_expr
    { Elet ($3, $2, $4, $6) }
| MATCH seq_expr WITH match_cases(seq_expr) END
    { Ematch ($2, $4) }
| MATCH comma_list2(expr) WITH match_cases(seq_expr) END
    { Ematch (mk_expr (Etuple $2) $startpos($2) $endpos($2), $4) }
| quote_uident COLON seq_expr
    { Emark ($1, $3) }
| LOOP loop_annotation seq_expr END
    { Eloop ($2, $3) }
| WHILE seq_expr DO loop_annotation seq_expr DONE
    { Ewhile ($2, $4, $5) }
| FOR lident EQUAL seq_expr for_direction seq_expr DO invariant* seq_expr DONE
    { Efor ($2, $4, $5, $6, $8, $9) }
| ABSURD
    { Eabsurd }
| RAISE uqualid
    { Eraise ($2, None) }
| RAISE LEFTPAR uqualid seq_expr RIGHTPAR
    { Eraise ($3, Some $4) }
| TRY seq_expr WITH bar_list1(exn_handler) END
    { Etry ($2, $4) }
| ANY simple_type_c
    { Eany $2 }
| GHOST expr
    { Eghost $2 }
| ABSTRACT spec seq_expr END
    { Eabstract($3, $2) }
| assertion_kind LEFTBRC term RIGHTBRC
    { Eassert ($1, $3) }
| label expr %prec prec_named
    { Enamed ($1, $2) }
| expr cast
    { Ecast ($1, $2) }

expr_arg: e = mk_expr(expr_arg_) { e }
expr_dot: e = mk_expr(expr_dot_) { e }

expr_arg_:
| qualid                    { Eident $1 }
| numeral                   { Econst $1 }
| TRUE                      { Etrue }
| FALSE                     { Efalse }
| o = oppref ; a = expr_arg { Eidapp (Qident o, [a]) }
| expr_sub                  { $1 }

expr_dot_:
| lqualid                   { Eident $1 }
| o = oppref ; a = expr_dot { Eidapp (Qident o, [a]) }
| expr_sub                  { $1 }

expr_sub:
| expr_dot DOT lqualid_rich                         { Eidapp ($3, [$1]) }
| BEGIN seq_expr END                                { $2.expr_desc }
| LEFTPAR seq_expr RIGHTPAR                         { $2.expr_desc }
| BEGIN END                                         { Etuple [] }
| LEFTPAR RIGHTPAR                                  { Etuple [] }
| LEFTPAR comma_list2(expr) RIGHTPAR                { Etuple $2 }
| LEFTBRC field_list1(expr) RIGHTBRC                { Erecord $2 }
| LEFTBRC expr_arg WITH field_list1(expr) RIGHTBRC  { Eupdate ($2, $4) }
| expr_arg LEFTSQ expr RIGHTSQ
    { Eidapp (get_op $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ expr LARROW expr RIGHTSQ
    { Eidapp (set_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT expr RIGHTSQ
    { Eidapp (sub_op $startpos($2) $endpos($2), [$1;$3;$5]) }
| expr_arg LEFTSQ expr DOTDOT RIGHTSQ
    { Eidapp (above_op $startpos($2) $endpos($2), [$1;$3]) }
| expr_arg LEFTSQ DOTDOT expr RIGHTSQ
    { Eidapp (below_op $startpos($2) $endpos($2), [$1;$4]) }

loop_annotation:
| (* epsilon *)
    { { loop_invariant = []; loop_variant = [] } }
| invariant loop_annotation
    { let a = $2 in { a with loop_invariant = $1 :: a.loop_invariant } }
| variant loop_annotation
    { let a = $2 in { a with loop_variant = variant_union $1 a.loop_variant } }

exn_handler:
| uqualid pat_arg? ARROW seq_expr { $1, $2, $4 }

val_expr:
| tail_type_c { Eany $1 }

%inline lazy_op:
| AMPAMP  { LazyAnd }
| BARBAR  { LazyOr }

assertion_kind:
| ASSERT  { Aassert }
| ASSUME  { Aassume }
| CHECK   { Acheck }

for_direction:
| TO      { To }
| DOWNTO  { Downto }

(* Specification *)

spec:
| (* epsilon *)     { empty_spec }
| single_spec spec  { spec_union $1 $2 }

single_spec:
| REQUIRES LEFTBRC term RIGHTBRC
    { { empty_spec with sp_pre = [$3] } }
| ENSURES LEFTBRC ensures RIGHTBRC
    { { empty_spec with sp_post = [floc $startpos($3) $endpos($3), $3] } }
| RETURNS LEFTBRC match_cases(term) RIGHTBRC
    { { empty_spec with sp_post = [floc $startpos($3) $endpos($3), $3] } }
| RAISES LEFTBRC bar_list1(raises) RIGHTBRC
    { { empty_spec with sp_xpost = [floc $startpos($3) $endpos($3), $3] } }
| READS  LEFTBRC comma_list0(lqualid) RIGHTBRC
    { { empty_spec with sp_reads = $3; sp_checkrw = true } }
| WRITES LEFTBRC comma_list0(term) RIGHTBRC
    { { empty_spec with sp_writes = $3; sp_checkrw = true } }
| RAISES LEFTBRC comma_list1(xsymbol) RIGHTBRC
    { { empty_spec with sp_xpost = [floc $startpos($3) $endpos($3), $3] } }
| DIVERGES
    { { empty_spec with sp_diverge = true } }
| variant
    { { empty_spec with sp_variant = $1 } }

ensures:
| term
    { let id = mk_id "result" $startpos $endpos in
      [mk_pat (Pvar id) $startpos $endpos, $1] }

raises:
| uqualid ARROW term
    { $1, mk_pat (Ptuple []) $startpos($1) $endpos($1), $3 }
| uqualid pat_arg ARROW term
    { $1, $2, $4 }

xsymbol:
| uqualid
    { $1, mk_pat Pwild $startpos $endpos, mk_term Ttrue $startpos $endpos }

invariant:
| INVARIANT LEFTBRC term RIGHTBRC { $3 }

variant:
| VARIANT LEFTBRC comma_list1(single_variant) RIGHTBRC { $3 }

single_variant:
| term preceded(WITH,lqualid)? { $1, $2 }

(* Patterns *)

mk_pat(X): X { mk_pat $1 $startpos $endpos }

pattern: mk_pat(pattern_) { $1 }
pat_arg: mk_pat(pat_arg_) { $1 }

pattern_:
| pat_conj_                             { $1 }
| mk_pat(pat_conj_) BAR pattern         { Por ($1,$3) }

pat_conj_:
| pat_uni_                              { $1 }
| comma_list2(mk_pat(pat_uni_))         { Ptuple $1 }

pat_uni_:
| pat_arg_                              { $1 }
| uqualid pat_arg+                      { Papp ($1,$2) }
| mk_pat(pat_uni_) AS labels(lident_nq) { Pas ($1,$3) }
| mk_pat(pat_uni_) cast                 { Pcast($1,$2) }

pat_arg_:
| UNDERSCORE                            { Pwild }
| labels(lident_nq)                     { Pvar $1 }
| uqualid                               { Papp ($1,[]) }
| LEFTPAR RIGHTPAR                      { Ptuple [] }
| LEFTPAR pattern_ RIGHTPAR             { $2 }
| LEFTBRC field_list1(pattern) RIGHTBRC { Prec $2 }

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
| lident_keyword  { mk_id $1 $startpos $endpos }
| LIDENT_QUOTE    { mk_id $1 $startpos $endpos }

lident_nq:
| LIDENT          { mk_id $1 $startpos $endpos }
| lident_keyword  { mk_id $1 $startpos $endpos }
| LIDENT_QUOTE    { let loc = floc $startpos($1) $endpos($1) in
                    Why3_loc.errorm ~loc "Symbol %s cannot be user-defined" $1 }

lident_keyword:
| MODEL           { "model" }
| RANGE           { "range" }
| FLOAT           { "float" }

quote_uident:
| QUOTE_UIDENT  { mk_id ("'" ^ $1) $startpos $endpos }

quote_lident:
| QUOTE_LIDENT  { mk_id $1 $startpos $endpos }

opaque_quote_lident:
| OPAQUE_QUOTE_LIDENT { mk_id $1 $startpos $endpos }

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
| LEFTSQ RIGHTSQ          { mixfix "[]" }
| LEFTSQ LARROW RIGHTSQ   { mixfix "[<-]" }
| LEFTSQ RIGHTSQ LARROW   { mixfix "[]<-" }
| LEFTSQ UNDERSCORE DOTDOT UNDERSCORE RIGHTSQ { mixfix "[_.._]" }
| LEFTSQ            DOTDOT UNDERSCORE RIGHTSQ { mixfix "[.._]" }
| LEFTSQ UNDERSCORE DOTDOT            RIGHTSQ { mixfix "[_..]" }

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
| uident                    { Qident $1 }
| lident                    { Qident $1 }
| lident_op_id              { Qident $1 }
| uqualid DOT uident        { Qdot ($1, $3) }
| uqualid DOT lident        { Qdot ($1, $3) }
| uqualid DOT lident_op_id  { Qdot ($1, $3) }

lqualid_rich:
| lident                    { Qident $1 }
| lident_op_id              { Qident $1 }
| uqualid DOT lident        { Qdot ($1, $3) }
| uqualid DOT lident_op_id  { Qdot ($1, $3) }

lqualid:
| lident              { Qident $1 }
| uqualid DOT lident  { Qdot ($1, $3) }

uqualid:
| uident              { Qident $1 }
| uqualid DOT uident  { Qdot ($1, $3) }

(* Theory/Module names *)

tqualid:
| uident                { Qident $1 }
| any_qualid DOT uident { Qdot ($1, $3) }

any_qualid:
| sident                { Qident $1 }
| any_qualid DOT sident { Qdot ($1, $3) }

sident:
| ident   { $1 }
| STRING  { mk_id $1 $startpos $endpos }

(* Labels and position markers *)

labels(X): X label* { add_lab $1 $2 }

label:
| STRING    { Lstr (Why3_ident.create_label $1) }
| POSITION  { Lpos $1 }

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
