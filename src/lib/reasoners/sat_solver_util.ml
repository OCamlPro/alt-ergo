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
         (* Another vrai form ;) *)
         origin_name = "vrey";
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

(* Assert the last computed model in the environment [env].

   @raise Unsat if the solver found a contradiction, which means the model
          is wrong. *)
let assert_model (type a) (module SAT : S with type t = a) env mdl =
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

let (let*) = Option.bind

(* [get_value_in_boolean_model env e] retrieves the assignment of the boolean
   expression [e] in the last boolean model of [env].

   @return [None] if the formula [e] hasn't been assigned by the SAT
           solver. *)
let get_value_in_boolean_model (type a) (module SAT : S with type t = a) env e =
  match Expr.type_info e with
  | Ty.Tbool ->
    begin
      let* bmodel = SAT.get_boolean_model env in
      Stdcompat.List.find_map
        (fun lit ->
           if Expr.equal e lit then
             Some true
           else if Expr.equal e (Expr.neg lit) then
             Some false
           else
             None
        )
        bmodel
    end
  | _ -> invalid_arg "get_value_in_boolean_model"

(* [get_value_in_model mdl e] tries to retrieve the value of the expression
   [e] in the model [mdl]. For boolean expressions, we retrieve their value
   in the last boolean model of [env]. *)
let get_value_in_model (type a) (module SAT : S with type t = a) env mdl e =
  let { Expr.f; xs; ty; _ } = Expr.term_view e in
  match f, ty with
  | _, Ty.Tbool ->
    begin
      (* Values of boolean expressions are decided by the SAT solver. *)
      match get_value_in_boolean_model (module SAT) env e with
      | Some true -> Some Expr.vrai
      | Some false -> Some Expr.faux
      | None -> None
    end
  | Symbols.Name name, _ ->
    let arg_tys = List.map Expr.type_info xs in
    let typed_name = (name, arg_tys, ty) in
    ModelMap.get_value typed_name xs mdl.Models.model
  | _ -> None

let get_value (type a) (module SAT : S with type t = a) env l =
  let* mdl = SAT.get_model env in
  assert_model (module SAT) env mdl;
  (* First, we attempt to retrieve each model term in the last computed
     boolean and first-order models.

     If we don't find the model term for an expression of [l], we assert a
     new equation to force the solver to produce a model term for this
     expression. *)
  let res =
    List.map
      (fun e ->
         match get_value_in_model (module SAT) env mdl e with
         | Some v -> Some v, None
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
           None, Some name
      ) l
  in
  (* We have to check the satisfability of the new environment [env] in order
     to produce a new model. If this call raise [Unsat], the model is wrong
     and we cannot produce model terms for the expressions of [l]. *)
  check (module SAT) env;
  let* mdl = SAT.get_model env in
  let values =
    List.map
      (fun (v, name) ->
         match v, name with
         | Some v, None -> v
         | None, Some name ->
           begin match get_value_in_model (module SAT) env mdl name with
             | Some v -> v
             | None ->
               (* The model generation has to produce a value for each
                  declared names. If some declared names are missing in the
                  model, it's a bug. *)
               assert false
           end
         | _ ->
           (* This case is excluded by the construction of the list [res]. *)
           assert false
      ) res
  in
  Some values

let get_assignment (type a) (module SAT : S with type t = a) env =
  List.map
    (fun e ->
       match get_value_in_boolean_model (module SAT) env e with
       | Some true -> True
       | Some false -> False
       | None -> Unknown
    )
