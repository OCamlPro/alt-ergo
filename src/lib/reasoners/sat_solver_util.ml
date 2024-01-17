(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2023 --- OCamlPro SAS                           *)
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
(*     Until 2013, some parts of this code were released under            *)
(*     the Apache Software License version 2.0.                           *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module type S = Sat_solver_sig.S

type 'a sat_module = (module S with type t = 'a)
type any_sat_module = (module S)

type lbool = False | True | Unknown

let pp_lbool ppf b =
  match b with
  | False -> Fmt.pf ppf "false"
  | True -> Fmt.pf ppf "true"
  | Unknown -> Fmt.pf ppf "unknown"

open Sat_solver_sig

let internal_assume (type a) (module SAT : S with type t = a) env id e =
  SAT.assume env
    {Expr.ff= e;
     origin_name = id;
     gdist = -1;
     hdist = 0;
     trigger_depth = max_int;
     nb_reductions = 0;
     age=0;
     lem=None;
     mf=true;
     gf=false;
     from_terms = [];
     theory_elim = true;
    }
    Explanation.empty

let check (type a) (module SAT : S with type t = a) env =
  try
    let ex = SAT.unsat env
        {Expr.ff=Expr.vrai;
         origin_name = "";
         hdist = -1;
         gdist = 0;
         trigger_depth = max_int;
         nb_reductions = 0;
         age=0;
         lem=None;
         mf=true;
         gf=true;
         from_terms = [];
         theory_elim = true;
        }
    in
    raise_notrace (Unsat ex)
  with
  | I_dont_know | Sat -> ()

exception Wrong_model of Explanation.t
exception No_model

(* Assert the last computed model in the environment [env].

   @raise Wrong_model if the solver found a contradiction, which means the model
          is wrong. *)
let assert_model (type a) (module SAT : S with type t = a) env mdl =
  try
    ModelMap.iter
      (fun ({ hs; _ } as name, _, ret_ty) graph ->
         ModelMap.Graph.iter
           (fun val_args val_ret ->
              let e = Expr.mk_app name val_args ret_ty in
              let iff = match ret_ty with Ty.Tbool -> true | _ -> false in
              let eq = Expr.mk_eq ~iff e val_ret in
              internal_assume (module SAT) env (Hstring.view hs) eq
           )
           graph
      )
      mdl.Models.model;
    check (module SAT) env
  with Unsat ex -> raise_notrace (Wrong_model ex)

(* [get_value_in_boolean_model bmdl e] retrieves the assignment of the boolean
   expression [e] in the boolean model [bmdl].

   @return [None] if the formula [e] hasn't been assigned by the SAT solver. *)
let get_value_in_boolean_model bmdl e =
  match Expr.type_info e with
  | Ty.Tbool ->
    begin
      Compat.List.find_map
        (fun lit ->
           if Expr.equal e lit then
             Some true
           else if Expr.equal e (Expr.neg lit) then
             Some false
           else
             None
        )
        bmdl
    end
  | _ -> invalid_arg "get_value_in_boolean_model"

(* [get_value_in_model mdl bmdl e] tries to retrieve the value of the expression
   [e] in the first-order model [mdl]. For boolean expressions, we retrieve
   their value in the boolean model [bmdl]. *)
let get_value_in_model mdl bmdl e =
  let { Expr.f; xs; ty; _ } = Expr.term_view e in
  match f, ty with
  | _, Ty.Tbool ->
    (* Values of boolean expressions are decided by the SAT solver. *)
    Option.map Expr.Core.of_bool @@
    get_value_in_boolean_model bmdl e

  | Symbols.Name name, _ ->
    let arg_tys = List.map Expr.type_info xs in
    let typed_name = (name, arg_tys, ty) in
    ModelMap.get_value typed_name xs mdl.Models.model
  | _ -> None

let (let*) = Option.bind

let get_value (type a) (module SAT : S with type t = a) env l =
  let* mdl = SAT.get_model env in
  (* HOTFIX for SatML: we can assert new formula in [env.satml] only at the
     level of decision [0]. After performing [unsat], the decision level isn't
     necessary [0] and the SMT statement `get-value` can be called only in
     SAT mode, so we have to reset all the decisions of the solver here.
     Before resetting the decisions, we save the boolean model for sake
     of optimization.

     See issue: https://github.com/OCamlPro/alt-ergo/issues/1063 *)
  let bmdl = SAT.get_boolean_model env in
  SAT.reset_decisions env;
  assert_model (module SAT) env mdl;
  (* First, we attempt to retrieve each model term in the last computed
     boolean and first-order models.

     If we don't find the model term for an expression of [l], we assert a
     new equation to force the solver to produce a model term for this
     expression. *)
  let l =
    List.map
      (fun e ->
         match get_value_in_model mdl bmdl e with
         | Some v -> Either.Left v
         | None ->
           (* For each expression [e] of the list [l], we assert an equality
              of the form [n = e] where [n] is a fresh name. *)
           let ty = Expr.type_info e in
           let id = Id.Namespace.GetValue.fresh () in
           let sy = Symbols.name ~ns:GetValue id in
           let name = Expr.mk_term sy [] ty in
           let iff = match ty with Ty.Tbool -> true | _ -> false in
           let t = Expr.mk_eq ~iff name e in
           let () =
             let { Expr.f; ty; _ } = Expr.term_view name in
             match f with
             | Symbols.Name name ->
               SAT.declare env (name, [], ty)
             | _ -> assert false
           in
           internal_assume (module SAT) env id t;
           Either.Right name
      ) l
  in
  (* We have to check the satisfability of the new environment [env] in order
     to produce a new model. If this call raise [Unsat], the model is wrong
     and we cannot produce model terms for the expressions of [l]. *)
  try
    check (module SAT) env;
    let* mdl = SAT.get_model env in
    let bmdl = SAT.get_boolean_model env in
    let values =
      List.map
        (fun v ->
           match v with
           | Either.Left v -> v
           | Either.Right name ->
             match get_value_in_model mdl bmdl name with
             | Some v -> v
             | None ->
               (* The model generation has to produce a value for each
                  declared names. If some declared names are missing in the
                  model, it's a bug. *)
               assert false
        ) l
    in
    Some values
  with Unsat ex -> raise_notrace (Wrong_model ex)

let get_assignment (type a) (module SAT : S with type t = a) env =
  let bmdl = SAT.get_boolean_model env in
  List.map
    (fun e ->
       match get_value_in_boolean_model bmdl e with
       | Some true -> True
       | Some false -> False
       | None -> Unknown
    )
