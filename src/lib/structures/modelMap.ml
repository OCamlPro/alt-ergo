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

type sy = Id.t * Ty.t list * Ty.t [@@deriving ord]

module Value = struct
  type simple = [
    | `Abstract of sy
    | `Constant of string
  ]
  [@@deriving ord]

  type record = string * simple list
  [@@deriving ord]

  type array = [
    | `Abstract of sy
    | `Store of array * string * string
  ]
  [@@deriving ord]

  type t = [
    | `Array of array
    | `Record of record
    | simple
  ]
  [@@deriving ord]

  let pp_simple ppf simple =
    match simple with
    | `Abstract (id, _, ty) ->
      Fmt.pf ppf "(as %a %a)" Id.pp id Ty.pp_smtlib ty
    | `Constant s ->
      Fmt.string ppf s

  let rec pp_array ppf arr =
    match arr with
    | `Abstract (id, _, ty) ->
      Fmt.pf ppf "(as %a %a)" Id.pp id Ty.pp_smtlib ty
    | `Store (arr, i, v) ->
      Fmt.pf ppf "(@[<hv>store@ %a@ %s %s)@]"
        pp_array arr i v

  let pp ppf v =
    match v with
    | `Array arr -> pp_array ppf arr
    | `Record (id, fields) ->
      Fmt.pf ppf "(@[<hv>%s %a)@]"
        (Util.quoted_string id)
        Fmt.(list ~sep:sp pp_simple) fields
    | #simple as w -> pp_simple ppf w

  module Map = Map.Make (struct
      type nonrec t = t

      let compare = compare
    end)
end

module Graph = struct
  module M = Map.Make
      (struct
        type t = Value.t list [@@deriving ord]
      end)

  type t = Value.t M.t

  let empty = M.empty
  let add = M.add

  module Fiber = struct
    include Set.Make (struct
        type t = Value.t list [@@deriving ord]
      end)

    (* For an argument (x_1, ..., x_n) of the function represented by the graph,
       prints the SMT-LIB formula:
        (and (= arg_0 x_1)
          (and (= arg_1 x2)
            ... (= arg_n x_n).
    *)
    let rec pp_args ctr ppf = function
      | [] -> ()
      | [arg] ->
        Fmt.pf ppf "(= arg_%i %a)" ctr Value.pp arg
      | arg :: args ->
        Fmt.pf ppf "(and (= arg_%i %a) %a)"
          ctr
          Value.pp arg
          (pp_args (ctr + 1)) args

    (* For a fiber [x; y; z; ...] of the function represented by the graph,
       prints the SMT-LIB formula:
        (or (and (= arg_0 x_0) (and (= arg_1 x_1) ...))
          (or (and (= arg_0 y_0) (and (= arg_1 y_1) ...))
            ...
    *)
    let pp ppf fiber =
      let rec aux ppf seq =
        match seq () with
        | Seq.Nil -> ()
        | Cons (args, seq) when Stdcompat.Seq.is_empty seq ->
          Fmt.pf ppf "%a" (pp_args 0) args
        | Cons (args, seq) ->
          Fmt.pf ppf "(or %a %a)"
            (pp_args 0) args
            aux seq
      in
      aux ppf (to_seq fiber)
  end

  (* Compute all the fibers of the function represented by the graph. *)
  let inverse graph =
    M.fold (fun arg_vals ret_val acc ->
        match Value.Map.find_opt ret_val acc with
        | Some fib ->
          Value.Map.add ret_val (Fiber.add arg_vals fib) acc
        | None ->
          Value.Map.add ret_val (Fiber.of_list [arg_vals]) acc
      ) graph Value.Map.empty

  let pp_inverse ppf rel =
    let rec aux ppf seq =
      match seq () with
      | Seq.Nil -> ()
      | Cons ((ret_val, _), seq) when Stdcompat.Seq.is_empty seq ->
        Fmt.pf ppf "%a" Value.pp ret_val
      | Cons ((ret_val, fiber), seq) ->
        Fmt.pf ppf "(@[<hv>ite %a@ %a@ %a)@]"
          Fiber.pp fiber
          Value.pp ret_val
          aux seq
    in
    aux ppf (Value.Map.to_seq rel)
end

module P = Map.Make
    (struct
      type t = sy [@@deriving ord]
    end)

type t = {
  values : Graph.t P.t;
  suspicious : bool;
}

let is_suspicious_name hs =
  match Hstring.view hs with
  | "@/" | "@%" | "@*" -> true
  | _ -> false

(* The model generation is known to be imcomplete for FPA and Bitvector
   theories. *)
let is_suspicious_symbol = function
  | Sy.Op (Float | Abs_int | Abs_real | Sqrt_real
          | Sqrt_real_default | Sqrt_real_excess
          | Real_of_int | Int_floor | Int_ceil
          | Max_int | Max_real | Min_int | Min_real
          | Pow | Integer_log2 | Integer_round) -> true
  | Sy.Name { hs; _ } when is_suspicious_name hs -> true
  | _ -> false

let add ((id, arg_tys, _) as sy) arg_vals ret_val { values; suspicious } =
  if List.compare_lengths arg_tys arg_vals <> 0 then
    Fmt.invalid_arg "The arity of the symbol %a doesn't agree the number of \
                     arguments" Id.pp id;

  let graph = try P.find sy values with Not_found -> Graph.empty in
  let values = P.add sy (Graph.add arg_vals ret_val graph) values in
  { values; suspicious }

let empty ~suspicious = { values = P.empty; suspicious }

let pp_named_arg_ty ~unused ppf (arg_name, arg_ty) =
  let pp_unused ppf unused = if unused then Fmt.pf ppf "_" else () in
  Fmt.pf ppf "(%aarg_%i %a)" pp_unused unused arg_name Ty.pp_smtlib arg_ty

let pp_define_fun ppf ((id, arg_tys, ret_ty), graph) =
  let inverse_rel = Graph.inverse graph in
  let is_constant = Value.Map.cardinal inverse_rel = 1 in
  let named_arg_tys = List.mapi (fun i arg_ty -> (i, arg_ty)) arg_tys in
  Fmt.pf ppf "(@[define-fun %a (%a) %a@ %a)@]"
    Id.pp id
    Fmt.(list ~sep:sp (pp_named_arg_ty ~unused:is_constant)) named_arg_tys
    Ty.pp_smtlib ret_ty
    Graph.pp_inverse inverse_rel

let pp_seq ppf seq =
  match seq () with
  | Seq.Nil -> ()
  | Cons _ -> Fmt.pf ppf "@,%a" Fmt.(seq ~sep:cut pp_define_fun) seq

let pp ppf {values; suspicious} =
  if suspicious then begin
    Fmt.pf ppf "; This model is a best-effort. It includes symbols\n\
                ; for which model generation is known to be incomplete.@."
  end;
  Fmt.pf ppf "@[<v 2>(%a@]@,)" pp_seq (P.to_seq values)
