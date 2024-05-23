(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) 2013-2024 --- OCamlPro SAS                           *)
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

module DStd = Dolmen.Std
module DE = DStd.Expr
module DT = DE.Ty
module B = Dolmen.Std.Builtin
open DE

type t = Dolmen.Std.Expr.ty_def list

(* A nest is the set of all the constructors of a mutually recursive definition
   of ADTs.

   For each type ty of a nest, we denote by S(ty) the set of all the
   constructors of this type in this nest and G(ty) the set of the constructors
   with an argument of type ty in this nest.

   Recall that a (directed) hypergraph is a set of nodes and hyperedges between
   subsets of these nodes.

   To generate our total order of a nest, we build in [build_graph] a hypergraph
   where:
   - the nodes are all the constructors of the nest;
   - for all type ty of the nest, there is a a hyperedge from S(ty) to G(ty).

    In particular, our graph has exactly one outgoing hyperedge per node. *)

(* Node of the hypergraph. *)
type node = {
  id : term_cst;
  (* Dolmen constructor identifier. *)

  weight : int;
  (* This weight is used to prioritize constructors with less destructors
     during the sorting (see [add_nest]). *)

  mutable outgoing : edge;
  (* Hyperedge from a subset S in S(ty) to a subset G in G(ty) where ty is
     the type of [id]. At the beginning, we have S = S(ty) and G = G(ty).

     One use a double indirection because this hyperedge is shared between
     all the elements of S. *)

  mutable in_degree : int;
  (* Number of hyperedges into this constructor. *)
}

(* Type of a hyperedge. *)
and edge = node list ref

module Hp =
  Heap.MakeOrdered
    (struct
      type t = node
      let compare { weight = w1; _ } { weight = w2; _ } = w1 - w2

      let default =
        let dummy_edge : node list ref = ref [] in
        {
          id = Term.Const.Int.int "0" (* dummy *);
          outgoing = dummy_edge;
          in_degree = -1;
          weight = -1;
        }
    end)

let (let*) = Option.bind

(* Return the type definition of the return type of the destructor [dstr]. *)
let def_of_dstr dstr =
  let* ty_cst =
    match dstr with
    | DE.{ builtin = B.Destructor _; id_ty; _ } ->
      begin match DT.view id_ty with
        | `Arrow (_, ty) ->
          begin match DT.view ty with
            | `App (`Generic ty_cst, _) -> Some ty_cst
            | _ -> None
          end
        | _ -> None
      end
    | _ -> assert false
  in
  DT.definition ty_cst

(* Build the hypergraph of dependencies between the constructors of the
   nest [defs].

   @return a heap that contains all the nodes of this graph without ingoing
   hyperedges. *)
let build_graph (defs : ty_def list) : Hp.t =
  let map : (ty_def, edge) Hashtbl.t = Hashtbl.create 17 in
  let hp : Hp.t = Hp.create 17 in
  List.iter (fun d -> Hashtbl.add map d (ref [])) defs;
  List.iter
    (fun def ->
       match def with
       | Abstract -> assert false
       | Adt { cases; _ } ->
         Array.iter
           (fun { cstr; dstrs; _ } ->
              let node = {
                id = cstr;
                outgoing = Hashtbl.find map def;
                in_degree = -1; (* dummy value *)
                weight = Array.length dstrs
              }
              in
              let in_degree =
                Array.fold_left
                  (fun acc2 dstr ->
                     let d = let* dstr = dstr in def_of_dstr dstr in
                     match d with
                     | Some d ->
                       begin match Hashtbl.find map d with
                         | used_by ->
                           used_by := node :: !used_by;
                           acc2 + 1
                         | exception Not_found ->
                           acc2
                       end
                     | None -> acc2
                  ) 0 dstrs
              in
              node.in_degree <- in_degree;
              if in_degree = 0 then Hp.insert hp node
           ) cases
    ) defs;
  hp

module H = Hashtbl.Make (Uid)

(* Internal state used to store the current order. *)
let add_cstr, find_weight, reinit =
  let ctr = ref 0 in
  let order : int H.t = H.create 100 in
  (* add_weight *)
  (fun cstr ->
     H.add order cstr !ctr;
     incr ctr),
  (* find_weight *)
  (fun cstr ->
     try
       H.find order cstr
     with Not_found ->
       Fmt.failwith "cannot find uid %a" Uid.pp cstr),
  (* reinit *)
  (fun () ->
     ctr := 0;
     H.clear order)

(* Sort the constructors of the nest using a sorting based on the
   Kahn's algorithm. *)
let add_nest n =
  let hp = build_graph n in
  while not @@ Hp.is_empty hp do
    (* Loop invariant: the set of nodes in heap [hp] is exactly
       the set of the nodes of the graph without ingoing hyperedge. *)
    let { id; outgoing; in_degree; _ } = Hp.pop_minimum hp in
    add_cstr @@ Uid.of_dolmen id;
    assert (in_degree = 0);
    outgoing :=
      List.filter_map
        (fun node ->
           assert (node.in_degree > 0);
           let node = { node with in_degree = node.in_degree - 1 } in
           if node.in_degree = 0 then (
             Hp.insert hp node;
             None
           ) else (
             Some node
           )
        ) !outgoing
  done

let compare (id1 : Uid.t) (id2 : Uid.t) =
  match id1, id2 with
  | Dolmen _, Dolmen _ ->
    find_weight id1 - find_weight id2
  | _ ->
    Uid.compare id1 id2
