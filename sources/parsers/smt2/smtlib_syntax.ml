(******************************************************************************)
(*                                                                            *)
(* An SMT-LIB 2 for the Alt-Ergo Theorem Prover                               *)
(*                                                                            *)
(******************************************************************************)

type 'a data = { p : (Lexing.position * Lexing.position) ; c : 'a ; ty : Smtlib_ty.ty; mutable is_quantif : bool}

type constant =
| Const_Dec of string
| Const_Num of string
| Const_Str of string
| Const_Hex of string
| Const_Bin of string

type symbol = string data

type keyword_aux =
| Category
| Smtlibversion
| Source
| Statuts of symbol
| License
| Notes
| Axioms
| Definitio
| Extensions
| Funs
| FunsDescript
| Language
| Sorts
| SortsDescr
| Theories
| Values
and keyword = keyword_aux data

and key_option_aux =
| Diagnooutputchan
| Globaldeclarations
| Interactive
| Printsucces
| Produceassertions
| Produceassignement
| Producemodels
| Produceproofs
| Produceunsatassumptions
| Produceunsatcores
| Randomseed
| Regularoutputchan
| Verbosity
| Ressourcelimit
and key_option = key_option_aux data

and option_aux =
| Option_key of key_option * index
| Option_attribute of attribute
and option = option_aux data

and key_info_aux =
| Allstats
| Assertionstacklvl
| Authors
| Errorbehav
| Name
| Reasonunknown
| Version
| Key_info of keyword
and key_info = key_info_aux data

and key_term_aux =
| Pattern of term list
| Named of symbol
and key_term = key_term_aux data

(* attributes *)
and sexpr_aux =
| SexprSpecConst of constant
| SexprSymbol of symbol
| SexprKeyword of keyword
| SexprInParen of sexpr list
and sexpr = sexpr_aux data

and attribute_value_aux =
| AttributeValSpecConst of constant
| AttributeValSymbol of symbol
| AttributeValSexpr of sexpr list
| NoAttributeValue
and attribute_value = attribute_value_aux data

and attribute_aux =
| AttributeKey of key_info
| AttributeKeyValue of key_info * attribute_value
and attribute = attribute_aux data

(* index *)
and index_aux =
| IndexSymbol of symbol
| IndexNumeral of string
and index = index_aux data

(* identifiers *)
and identifier_aux =
| IdSymbol of symbol
| IdUnderscoreSymNum of symbol * index list
and identifier = identifier_aux data

and prop_literal_aux =
| PropLit of symbol
| PropLitNot of symbol
and prop_literal = prop_literal_aux data

(* sorts and polymorphism *)
and sort_aux =
| SortIdentifier of identifier
| SortIdMulti of identifier * sort list
and sort = sort_aux data

(* typed variable *)
and sorted_var_aux = symbol * sort
and sorted_var =  sorted_var_aux data

(* qualidentifiers *)
and qualidentifier_aux =
| QualIdentifierId of identifier
| QualIdentifierAs of identifier * sort
and qualidentifier = qualidentifier_aux data

(* valued variable *)
and varbinding_aux = symbol * term
and varbinding = varbinding_aux data

and pattern_aux =
  | PatternSymb of symbol
  | PatternSymbplus of symbol * symbol list
and pattern = pattern_aux data

(* terms *)
and term_aux =
| TermSpecConst of constant
| TermQualIdentifier of qualidentifier
| TermQualIdTerm of qualidentifier * term list
| TermLetTerm of varbinding list * term
| TermForAllTerm of sorted_var list * term
| TermExistsTerm of sorted_var list * term
| TermExclimationPt of term * key_term list
| TermMatch of term * (pattern * term) list
and term = term_aux data

(* datatypes *)
and sort_dec = symbol * string
and selector_dec = symbol * sort
and constructor_dec = symbol * selector_dec list
and datatype_dec_aux =
| Datatype_dec_constr of constructor_dec list
| Datatype_dec_par of (symbol list) * (constructor_dec list)
and datatype_dec = datatype_dec_aux data

(* functions *)
and fun_dec_aux =
| Fun_dec of sort list * sort
| Fun_dec_par of symbol list * sort list * sort
and fun_dec = fun_dec_aux data

and fun_def_aux =
| Fun_def of symbol * sorted_var list * sort
| Fun_def_par of symbol * symbol list * sorted_var list * sort
and fun_def = fun_def_aux data

and const_dec_aux =
| Const_dec_sort of sort
| Const_dec_par of symbol list * sort
and const_dec = const_dec_aux data

(* asserts *)
and assert_dec_aux =
| Assert_dec of term
| Assert_dec_par of symbol list * term
and assert_dec = assert_dec_aux data

(* script commands *)
type command_aux =
| Cmd_Assert of assert_dec
| Cmd_CheckSat
| Cmd_CheckSatAssum of prop_literal list
| Cmd_CheckEntailment of assert_dec
| Cmd_DeclareConst of symbol * const_dec
| Cmd_DeclareDataType of symbol * datatype_dec
| Cmd_DeclareDataTypes of sort_dec list * datatype_dec list
| Cmd_DeclareFun of symbol * fun_dec
| Cmd_DeclareSort of symbol * string
| Cmd_DefineFun of fun_def * term
| Cmd_DefineFunRec of fun_def * term
| Cmd_DefineFunsRec of fun_def list * term list
| Cmd_DefineSort of symbol * symbol list * sort
| Cmd_Echo of attribute_value
| Cmd_GetAssert
| Cmd_GetProof
| Cmd_GetUnsatCore
| Cmd_GetValue of term list
| Cmd_GetAssign
| Cmd_GetOption of keyword
| Cmd_GetInfo of key_info
| Cmd_GetModel
| Cmd_GetUnsatAssumptions
| Cmd_Reset
| Cmd_ResetAssert
| Cmd_SetLogic of symbol
| Cmd_SetOption of option
| Cmd_SetInfo of attribute
| Cmd_Push of string
| Cmd_Pop of string
| Cmd_Exit
type command = command_aux data
type commands = command list

(*******************************************************************)

