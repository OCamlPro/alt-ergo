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

[@@@ocaml.warning "-33"]
open Options

open Parsed

(* helper functions *)

let mk_localized pp_loc pp_desc = { pp_loc ; pp_desc }

let mk_infix e1 op e2 = PPinfix (e1, op, e2)

let mk_prefix op e = PPprefix (op, e)

(** Declaration of types  **)

let mk_non_rec_type_decl loc ty_vars ty ty_kind =
  TypeDecl [ loc, ty_vars, ty, ty_kind ]

let mk_rec_type_decl l =
  TypeDecl l

let mk_abstract_type_decl loc ty_vars ty =
  mk_non_rec_type_decl loc ty_vars ty Abstract

let mk_enum_type_decl loc ty_vars ty enums =
  mk_non_rec_type_decl loc ty_vars ty (Enum enums)

let mk_algebraic_type_decl loc ty_vars ty enums =
  try
    let l =
      List.rev_map
        (fun (c, l) ->
           if l != [] then raise Exit;
           c
        )enums
    in
    mk_non_rec_type_decl loc ty_vars ty (Enum (List.rev l))
  with Exit ->
    mk_non_rec_type_decl loc ty_vars ty (Algebraic enums)

let mk_record_type_decl loc ty_vars ty ?(constr="{") fields =
  mk_non_rec_type_decl loc ty_vars ty (Record (constr, fields))


(** Declaration of symbols, functions, predicates, and goals *)

let mk_logic loc is_ac named_idents ty =
  Logic (loc , is_ac, named_idents, ty)

let mk_function_def loc named_ident args ty expr =
  Function_def (loc, named_ident, args, ty, expr)

let mk_ground_predicate_def loc named_ident expr =
  Predicate_def (loc, named_ident, [], expr)

let mk_non_ground_predicate_def loc named_ident args expr =
  Predicate_def (loc, named_ident, args, expr)

let mk_goal loc name expr =
  Goal (loc, name, expr)


(** Declaration of theories, generic axioms and rewriting rules **)

let mk_theory loc name ext expr =
  Theory (loc, name, ext, expr)

let mk_generic_axiom loc name expr =
  Axiom (loc, name, Util.Default, expr)

let mk_rewriting loc name expr =
  Rewriting (loc, name, expr)


(** Declaration of theory axioms and case-splits **)

let mk_theory_axiom loc name expr =
  Axiom (loc, name, Util.Propagator, expr)

let mk_theory_case_split loc name expr =
  Axiom (loc, name, Util.Default, expr)


(** Making pure and logic types *)

let int_type = PPTint

let bool_type = PPTbool

let real_type = PPTreal

let unit_type = PPTunit

let mk_bitv_type size =
  PPTbitv(int_of_string size)

let mk_external_type loc args ty =
  PPTexternal (args, ty, loc)

let mk_logic_type args_ty res_ty =
  match res_ty with
  | None ->  PPredicate args_ty
  | Some res -> PFunction (args_ty, res)

let mk_var_type loc alpha =
  PPTvarid (alpha, loc)


(** Making arithmetic expressions and predicates **)

let mk_int_const loc n =
  mk_localized loc (PPconst (ConstInt n))

let mk_real_const loc r =
  mk_localized loc (PPconst (ConstReal r))

let mk_add loc e1 e2 =
  mk_localized loc (mk_infix e1 PPadd e2)

let mk_sub loc e1 e2 =
  mk_localized loc (mk_infix e1 PPsub e2)


let mk_mul loc e1 e2 =
  mk_localized loc (mk_infix e1 PPmul e2)

let mk_div loc e1 e2 =
  mk_localized loc (mk_infix e1 PPdiv e2)

let mk_mod loc e1 e2 =
  mk_localized loc (mk_infix e1 PPmod e2)

let mk_minus loc e =
  mk_localized loc (mk_prefix PPneg e)

let mk_pred_lt loc e1 e2 =
  mk_localized loc (mk_infix e1 PPlt e2)

let mk_pred_le loc e1 e2 =
  mk_localized loc (mk_infix e1 PPle e2)

let mk_pred_gt loc e1 e2 =
  mk_localized loc (mk_infix e1 PPgt e2)

let mk_pred_ge loc e1 e2 =
  mk_localized loc (mk_infix e1 PPge e2)


(** Making Record expressions **)

let mk_record loc fields =
  mk_localized loc (PPrecord fields)

let mk_with_record loc e fields =
  mk_localized loc (PPwith(e, fields))

let mk_dot_record loc e label =
  mk_localized loc (PPdot(e, label))


(** Making Array expressions **)

let mk_array_get loc e1 e2 =
  mk_localized loc (PPget(e1, e2))

let mk_array_set loc e1 e2 e3 =
  mk_localized loc (PPset(e1, e2, e3))


(** Making Bit-vector expressions **)

let mk_bitv_const =
  let check_binary_mode s =
    String.iter
      (fun x ->
         match x with
         | '0' | '1' -> ()
         | _ -> raise Parsing.Parse_error) s;
    s
  in fun loc const ->
    mk_localized loc (PPconst (ConstBitv (check_binary_mode const)))

let mk_bitv_extract loc e i j =
  let i =  mk_int_const loc i in
  let j =  mk_int_const loc j in
  mk_localized loc (PPextract (e, i, j))

let mk_bitv_concat loc e1 e2 =
  mk_localized loc (PPconcat(e1, e2))


(** Making Boolean / Propositional expressions **)

let mk_true_const loc =
  mk_localized loc (PPconst ConstTrue)

let mk_false_const loc =
  mk_localized loc (PPconst ConstFalse)

let mk_and loc e1 e2 =
  mk_localized loc (mk_infix e1 PPand e2)

let mk_or loc e1 e2 =
  mk_localized loc (mk_infix e1 PPor e2)

let mk_xor loc e1 e2 =
  mk_localized loc (mk_infix e1 PPxor e2)

let mk_iff loc e1 e2 =
  mk_localized loc (mk_infix e1 PPiff e2)

let mk_implies loc e1 e2 =
  mk_localized loc (mk_infix e1 PPimplies e2)

let mk_not loc e =
  mk_localized loc (mk_prefix PPnot e)

let mk_pred_eq loc e1 e2 =
  mk_localized loc (mk_infix e1 PPeq e2)

let mk_pred_not_eq loc e1 e2 =
  mk_localized loc (mk_infix e1 PPneq e2)

let mk_distinct loc e2 =
  match e2 with
  | [a; b] -> mk_pred_not_eq loc a b
  | _ -> mk_localized loc (PPdistinct e2)

(** Making quantified formulas **)

let mk_forall loc vs_ty triggers filters expr =
  mk_localized loc (PPforall_named (vs_ty, triggers, filters, expr))

let mk_exists loc vs_ty triggers filters expr =
  mk_localized loc (PPexists_named (vs_ty, triggers, filters, expr))


(** Naming and casting types of expressions **)

let mk_named loc name e =
  mk_localized loc (PPnamed (name, e))


let mk_type_cast loc e ty =
  mk_localized loc (PPcast(e,ty))


(** Making vars, applications, if-then-else, and let expressions **)

let mk_var loc var =
  mk_localized loc (PPvar var)

let mk_application loc app args =
  mk_localized loc (PPapp (app, args))

let mk_pattern pat_loc pat_app args =
  { pat_loc ; pat_desc = (pat_app, args) }

let mk_ite loc cond th el =
  mk_localized loc (PPif (cond, th, el))

let mk_let loc binders e =
  mk_localized loc (PPlet (binders, e))

let mk_void loc =
  mk_localized loc (PPconst ConstVoid)


(** Making particular expression used in semantic triggers **)

let mk_in_interval loc expr low_br ei ej up_br =
  mk_localized loc (PPinInterval (expr, not low_br, ei ,ej, up_br))

let mk_maps_to loc v expr =
  mk_localized loc (PPmapsTo (v, expr))


(** Making cuts and checks **)

let mk_check loc expr =
  mk_localized loc (PPcheck expr)

let mk_cut loc expr =
  mk_localized loc (PPcut expr)

let mk_match loc expr cases =
  mk_localized loc (PPmatch (expr, cases))

let mk_algebraic_test loc expr cstr =
  mk_localized loc (PPisConstr (expr, cstr))

let mk_algebraic_project loc ~guarded expr cstr =
  mk_localized loc (PPproject (guarded, expr, cstr))

