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
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module DStd = Dolmen.Std
module Term = DStd.Term
module Stmt = DStd.Statement
module Id = DStd.Id
module SSet = Set.Make (String)

let prefix = "ae.fp."

(* Symbols of the prelude that are builtins of Alt-Ergo, as in Why3's Alt-Ergo
   driver ([round] is the generic [ae.float] instead of [float32] or [float64]).
   These are done here and not in the file directly because the alt-ergo native
   format does not allow dots in the symbol names. *)
let builtins = ["pow2", "int.pow2"; "round", "ae.float"]

type t =
  { mutable declared : SSet.t
        (** Source names of the declared and defined symbols without the prefix.
        *)
  }

let create () = { declared = SSet.empty }

let unsupported fmt = Fmt.failwith ("FPA prelude: unsupported " ^^ fmt)

let term_name (id : Id.t) =
  match id with { ns = Term; name = Simple n } -> Some n | _ -> None

let rename t (id : Id.t) =
  match term_name id with
  | Some n -> (
    match List.assoc_opt n builtins with
    | Some builtin -> Id.mk Id.term builtin
    | None ->
      if SSet.mem n t.declared
      then { id with name = DStd.Name.simple (prefix ^ n) }
      else id)
  | None -> id

let rec rewrite_term t (e : Term.t) =
  let term : Term.descr =
    match e.term with
    | Symbol id -> Symbol (rename t id)
    | Builtin _ as b -> b
    | App (f, args) -> App (rewrite_term t f, List.map (rewrite_term t) args)
    | Colon (u, v) -> Colon (rewrite_term t u, rewrite_term t v)
    | Binder (b, vars, body) ->
      Binder (b, List.map (rewrite_term t) vars, rewrite_term t body)
    | Match _ -> unsupported "pattern matching"
  in
  { e with term; attr = List.map (rewrite_term t) e.attr }

let declare t (id : Id.t) =
  match term_name id with
  | Some n ->
    t.declared <- SSet.add n t.declared;
    rename t id
  | None -> unsupported "declaration of %a" Id.print id

let rewrite_decl t (decl : Stmt.decl) =
  match decl with
  | Abstract a -> Stmt.Abstract { a with id = declare t a.id }
  | Record { id; _ } | Inductive { id; _ } ->
    unsupported "type declaration %a" Id.print id

let rewrite_def t (def : Stmt.def) =
  let body = rewrite_term t def.body in
  { def with id = declare t def.id; body }

let rewrite t (stmt : Stmt.t) =
  let descr : Stmt.descr =
    match stmt.descr with
    | Decls { contents; recursive } ->
      Decls { contents = List.map (rewrite_decl t) contents; recursive }
    | Defs { contents; recursive } ->
      Defs { contents = List.map (rewrite_def t) contents; recursive }
    | Antecedent f -> Antecedent (rewrite_term t f)
    | _ -> unsupported "statement %a" Stmt.print stmt
  in
  { stmt with descr }
