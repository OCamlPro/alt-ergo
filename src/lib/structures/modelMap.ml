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

type sig_ = Id.t * Ty.t list * Ty.t [@@deriving ord]

module Value = struct
  type simple = [
    | `Abstract of sig_
    | `Constant of string
  ]
  [@@deriving ord]

  type record = string * simple list
  [@@deriving ord]

  type array = [
    | `Abstract of sig_
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
      Fmt.pf ppf "%s" s

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

  module Fiber = struct
    include Set.Make (struct
        type t = Value.t list [@@deriving ord]
      end)

    let rec pp_args ctr ppf = function
      | [] -> ()
      | [arg] ->
        Fmt.pf ppf "(= arg_%i %a)" ctr Value.pp arg
      | arg :: args ->
        Fmt.pf ppf "(and (= arg_%i %a) %a)"
          ctr
          Value.pp arg
          (pp_args (ctr + 1)) args

    let pp ppf fiber =
      let rec aux ppf seq =
        match seq () with
        | Seq.Nil -> ()
        | Cons (args, seq) when Seq.is_empty seq ->
          Fmt.pf ppf "%a" (pp_args 0) args
        | Cons (args, seq) ->
          Fmt.pf ppf "(or %a %a)"
            (pp_args 0) args
            aux seq
      in
      aux ppf (to_seq fiber)
  end

  type t = Value.t M.t

  let empty = M.empty
  let add = M.add

  (* Compute the inverse relation of the graph. *)
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
      | Cons ((ret_val, _), seq) when Seq.is_empty seq ->
        Fmt.pf ppf "%a" Value.pp ret_val
      | Cons ((ret_val, fiber), seq) ->
        Fmt.pf ppf "(@[<hv>ite %a@ %a@ %a)@]"
          Fiber.pp fiber
          Value.pp ret_val
          aux seq
    in
    aux ppf (Value.Map.to_seq rel)

  let pp ppf graph = pp_inverse ppf (inverse graph)
end

module P = Map.Make
    (struct
      type t = sig_ [@@deriving ord]
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

let add ((_, arg_tys, _) as sig_) arg_vals ret_val { values; suspicious } =
  assert (List.compare_lengths arg_tys arg_vals = 0);
  let graph = try P.find sig_ values with Not_found -> Graph.empty in
  let values = P.add sig_ (Graph.add arg_vals ret_val graph) values in
  { values; suspicious = suspicious (* || is_suspicious_symbol sy *) }

let create _sigs = { values = P.empty; suspicious = false }

let pp_named_arg_ty ppf (arg_name, arg_ty) =
  Fmt.pf ppf "(arg_%i %a)" arg_name Ty.pp_smtlib arg_ty

let pp_define_fun ppf ((id, arg_tys, ret_ty), graph) =
  let named_arg_tys = List.mapi (fun i arg_ty -> (i, arg_ty)) arg_tys in
  Fmt.pf ppf "(@[define-fun %a (%a) %a@ %a)@]"
    Id.pp id
    Fmt.(list ~sep:cut pp_named_arg_ty) named_arg_tys
    Ty.pp_smtlib ret_ty
    Graph.pp graph

let pp_seq ppf seq =
  match seq () with
  | Seq.Nil -> ()
  | Cons _ -> Fmt.pf ppf "@,%a" Fmt.(seq ~sep:cut pp_define_fun) seq

let pp ppf {values; suspicious} =
  if suspicious then begin
    Fmt.pf ppf "; This model is a best-effort. It includes symbols
        for which model generation is known to be incomplete. @."
  end;
  Fmt.pf ppf "@[<v 2>(%a@]@,)" pp_seq (P.to_seq values)
