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

module X = Shostak.Combine
module Sy = Symbols

module Graph = struct
  module M = Map.Make
      (struct
        type t = Expr.t list [@@deriving ord]
      end)

  type t = Expr.t M.t

  let empty = M.empty
  let add = M.add
  let map = M.map
  let cardinal = M.cardinal
  let choose = M.choose

  (* A fiber of the function [f] over a value [v] is the set of all the values
     in the domain of [f] whose the image by [f] is [v].

     The function [inverse] of this module constructs a map of all the
     non-empty fibers of the function represented by its graph. *)
  module Fiber = struct
    include Set.Make (struct
        type t = Expr.t list [@@deriving ord]
      end)

    let pp_arg ppf (ctr, arg) =
      Fmt.pf ppf "(= arg_%i %a)" ctr Expr.pp_smtlib arg

    (* For an argument (x_1, ..., x_n) of the function represented by the graph,
       prints the SMT-LIB formula:
        (and (= arg_0 x_1)(= arg_1 x2) ... (= arg_n x_n)).
    *)
    let pp_args ppf = function
      | [] -> ()
      | [arg] ->
        pp_arg ppf (0, arg)
      | args ->
        Fmt.pf ppf "(and %a)" Fmt.(iter_bindings ~sep:sp List.iteri pp_arg) args

    (* For a fiber [x; y; z; ...] of the function represented by the graph,
       prints the SMT-LIB formula:
        (or
          (and (= arg_0 x_0) (= arg_1 x_1) ...)
          (and (= arg_0 y_0) (= arg_1 y_1) ...)
           ...)
    *)
    let pp ppf fiber =
      match cardinal fiber with
      | 0 -> ()
      | 1 ->
        let args = choose fiber in
        Fmt.pf ppf "%a" pp_args args
      | _ ->
        Fmt.pf ppf "(or %a)" (Fmt.iter ~sep:Fmt.sp iter pp_args) fiber
  end

  (* Compute all the fibers of the function represented by the graph. *)
  let inverse graph =
    M.fold (fun arg_vals ret_val acc ->
        match Expr.Map.find_opt ret_val acc with
        | Some fib ->
          Expr.Map.add ret_val (Fiber.add arg_vals fib) acc
        | None ->
          Expr.Map.add ret_val (Fiber.of_list [arg_vals]) acc
      ) graph Expr.Map.empty

  let pp_inverse ppf rel =
    let rec aux ppf seq =
      match seq () with
      | Seq.Nil -> ()
      | Cons ((ret_val, _), seq) when Stdcompat.Seq.is_empty seq ->
        Fmt.pf ppf "%a" Expr.pp_smtlib ret_val
      | Cons ((ret_val, fiber), seq) ->
        Fmt.pf ppf "(@[<hv>ite %a@ %a@ %a)@]"
          Fiber.pp fiber
          Expr.pp_smtlib ret_val
          aux seq
    in
    aux ppf (Expr.Map.to_seq rel)
end

module P = Map.Make
    (struct
      type t = Id.typed

      let compare = Id.compare_typed
    end)

type t = {
  values : Graph.t P.t;
  suspicious : bool;
}

let add ((id, arg_tys, _) as sy) arg_vals ret_val { values; suspicious } =
  if List.compare_lengths arg_tys arg_vals <> 0 then
    Fmt.invalid_arg "The arity of the symbol %a doesn't agree the number of \
                     arguments" Id.pp id;
  let graph =
    try
      let graph = P.find sy values in
      (* If the graph associated with [sy] contains only an abstract value,
         it means there is no constraint on this graph. We replace it by
         the graph with the only constraint given by [arg_vals] and
         [ret_val]. *)
      if Graph.cardinal graph == 1 then
        let _, value = Graph.choose graph in
        let Expr.{ f; _ } = Expr.term_view value in
        match f with
        | Sy.Name { hs; _ }
          when Id.Namespace.Abstract.is_id (Hstring.view hs) ->
          Graph.empty
        | _ -> graph
      else
        graph
    with Not_found -> Graph.empty in
  let values = P.add sy (Graph.add arg_vals ret_val graph) values in
  { values; suspicious }

module DeclSets = Set.Make
    (struct
      type t = Id.typed
      let compare = Id.compare_typed
    end)

let empty ~suspicious declared_ids =
  let values =
    List.fold_left
      (fun values ((_, arg_tys, ret_ty) as sy) ->
         let arg_vals = List.map Expr.mk_abstract arg_tys in
         let ret_val = Expr.mk_abstract ret_ty in
         let graph = Graph.add arg_vals ret_val Graph.empty in
         P.add sy graph values
      )
      P.empty declared_ids
  in
  { values; suspicious }

let rec subst_in_term id e c =
  let Expr.{ f; xs; ty = ty'; _ } = Expr.term_view c in
  match f, xs with
  | Sy.Name { hs = id'; _ }, [] when Id.equal id id' ->
    let ty = Expr.type_info e in
    if not @@ Ty.equal ty ty' then
      raise (Errors.Error (Model_error (Subst_type_clash (id, ty', ty))));
    e
  | _ ->
    begin
      let xs = List.map (subst_in_term id e) xs in
      Expr.mk_term f xs ty'
    end

let subst id e { values; suspicious } =
  if not @@ Expr.is_model_term e then
    raise (Errors.Error (Model_error (Subst_not_model_term e)));
  let values = P.map (Graph.map (subst_in_term id e)) values in
  { values; suspicious }

let pp_named_arg_ty ~unused ppf (arg_name, arg_ty) =
  let pp_unused ppf unused = if unused then Fmt.pf ppf "_" else () in
  Fmt.pf ppf "(%aarg_%i %a)" pp_unused unused arg_name Ty.pp_smtlib arg_ty

let pp_define_fun ppf ((id, arg_tys, ret_ty), graph) =
  let inverse_rel = Graph.inverse graph in
  let is_constant = Expr.Map.cardinal inverse_rel = 1 in
  let named_arg_tys = List.mapi (fun i arg_ty -> (i, arg_ty)) arg_tys in
  Fmt.pf ppf "(@[define-fun %a (%a) %a@ %a)@]"
    Id.pp id
    Fmt.(list ~sep:sp (pp_named_arg_ty ~unused:is_constant)) named_arg_tys
    Ty.pp_smtlib ret_ty
    Graph.pp_inverse inverse_rel

let pp ppf {values; suspicious} =
  if suspicious then begin
    Fmt.pf ppf "; This model is a best-effort. It includes symbols\n\
                ; for which model generation is known to be incomplete.@."
  end;
  if P.is_empty values then
    Fmt.pf ppf "@[<v 2>(@]@,)"
  else
    Fmt.pf ppf "@[<v 2>(@,%a@]@,)"
      (Fmt.iter_bindings ~sep:Fmt.cut P.iter pp_define_fun) values
