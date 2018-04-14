(******************************************************************************)
(*                                                                            *)
(* An SMT-LIB 2 for the Alt-Ergo Theorem Prover                               *)
(*                                                                            *)
(******************************************************************************)

open Smtlib_error

type ty = { id : int; mutable desc : desc }
and desc =
  | TDummy
  | TInt
  | TReal
  | TBool
  | TString
  | TArray of ty * ty
  | TBitVec of int
  | TSort of string * (ty list)
  | TDatatype of string * (ty list)
  | TVar of string
  | TFun of ty list * ty
  | TLink of ty

let cpt_ty = ref 0
let new_type desc =
  incr cpt_ty;
  { id = !cpt_ty; desc}

(* return the string correponding to the type *)
let rec to_string t =
  match t.desc with
  | TDummy -> Printf.sprintf "Dummy:%d" t.id
  | TInt -> "Int"
  | TReal -> "Real"
  | TBool -> "Bool"
  | TString -> "String"
  | TArray(t1,t2) -> Printf.sprintf "Array(%s %s)" (to_string t1) (to_string t2)
  | TBitVec(n) -> Printf.sprintf "BitVec(%d)" n
  | TSort(s,tl) ->
    if List.length tl = 0 then
      Printf.sprintf "%s(S)" s
    else Printf.sprintf "%s(S) (%s)" s
        (String.concat " " (List.map to_string tl))
  | TDatatype(s,tl) ->
    if List.length tl = 0 then
      (Printf.sprintf "%s(Dt)" s)
    else (Printf.sprintf "%s(Dt)" s)^ "(" ^
      (String.trim
         (List.fold_left
            (fun acc t -> acc^" "^(to_string t)) "" (List.rev tl))) ^ ")"
  | TVar(s) -> Printf.sprintf "(%s:%d)" s t.id
  | TFun(pars,ret) -> Printf.sprintf "Fun : %s %s"
                        (List.fold_left (fun acc par ->
                           Printf.sprintf "%s -> %s" (to_string par) acc) "" (List.rev pars)) (to_string ret)
  | TLink(t) -> Printf.sprintf "Link(%s)" (to_string t)

module IMap = Map.Make(struct type t = int let compare = compare end)
module SMap = Map.Make(String)

let rec shorten ty =
  match ty.desc with
  | TLink(t) -> shorten t
  | _ -> ty

let rec fun_ret ty =
  match (shorten ty).desc with
  | TFun(_,ret) -> ret
  | _ -> ty

let is_bool ty =
  (shorten ty).desc == TBool

let is_dummy ty =
  (shorten ty).desc == TDummy

let rec inst links m t =
  try m, IMap.find t.id m
  with Not_found ->
    let m, t' = match t.desc with
    | TDummy | TInt | TReal | TBool | TString -> m, t
    | TArray (t1,t2) ->
      let m1, t1' = inst links m t1 in
      let m2, t2' = inst links m1 t2 in
      m2, new_type (TArray(t1', t2'))
    | TBitVec(n) -> m, new_type (TBitVec(n))
    | TSort (s,tl) ->
      let m,tl = List.fold_left (fun (m,tl) t ->
          let m',t' = inst links m t in
          m', t' :: tl
        ) (m,[]) (List.rev tl) in
      m, new_type (TSort(s,tl))
    | TDatatype(s,tl) ->
      let m,tl = List.fold_left (fun (m,tl) t ->
          let m',t' = inst links m t in
          m', t' :: tl
        ) (m,[]) (List.rev tl) in
      m, new_type (TDatatype(s,tl))
    | TVar(s) -> begin
      try
        let ty = SMap.find s links in
        if ty.id < t.id then
          m, t
        else
          m, new_type (TDummy)
      with Not_found ->
        m, new_type (TDummy)
    end
    | TFun(pars, ret) ->
      let m,pars = List.fold_left (fun (m,tl) t ->
          let m',t' = inst links m t in
          m', t' :: tl
        ) (m,[]) (List.rev pars) in
      let m,ret = inst links m ret in
      m, new_type (TFun(pars,ret))
    | TLink(t1) ->
      inst links m (shorten t1)
    in
    let m = IMap.add t.id t' m in
    m, t'

let rec subst m t =
  try IMap.find t.id m
  with Not_found ->
  match t.desc with
  | TDummy | TInt | TReal | TBool | TString -> t
  | TArray (t1,t2) ->
    let t1' = subst m t1 in
    let t2' = subst m t2 in
    new_type (TArray(t1', t2'))
  | TBitVec(n) -> t
  | TSort (s,tl) ->
    let tl = List.fold_left (fun tl t ->
          let t' = subst m t in
          t' :: tl
        ) [] (List.rev tl) in
      new_type (TSort(s,tl))
    | TDatatype(s,tl) ->
    let tl = List.fold_left (fun tl t ->
          let t' = subst m t in
          t' :: tl
        ) [] (List.rev tl) in
    new_type (TDatatype(s,tl))
    | TVar(s) -> t
    | TFun(pars, ret) ->
      let pars = List.fold_left (fun tl t ->
          let t' = subst m t in
          t' :: tl
        ) [] (List.rev pars) in
      let ret = subst m ret in
      new_type (TFun(pars,ret))
    | TLink(t) -> subst m (shorten t)


let rec unify t1 t2 pos =
  (* Printf.printf "Unification de (%s) et (%s) \n%!" (to_string t1) (to_string t2); *)
  if t1.id <> t2.id then
    begin  match t1.desc, t2.desc with
      | TLink(t), _ -> unify (shorten t) t2 pos
      | _, TLink(t) -> unify t1 (shorten t) pos
      | TDummy, TDummy -> t1.desc <- (TLink t2)
      | TDummy, _ -> t1.desc <- (TLink(shorten t2))
      | _, TDummy -> t2.desc <- (TLink(shorten t1))
      | TVar(s1), TVar(s2) ->
        if t1.id <> t2.id then
          (error (Type_clash_error( to_string t1, to_string t2)) pos)
      | TInt, TInt | TReal, TReal | TBool, TBool | TString, TString -> ()
      | TInt, TReal | TReal, TInt ->
        assert false
        (* if not( get_is_int_real ()) then
         *   (error (Type_clash_error( to_string t1, to_string t2)) pos) *)
      | TArray(t1a,t1b), TArray(t2a,t2b) ->
        unify t1a t2a pos; unify t1b t2b pos
      | TBitVec(n1), TBitVec(n2) ->
        if not (n1 = n2) then
          (error (Type_clash_error( to_string t1, to_string t2)) pos)
      | TSort(s1,tl1), TSort(s2,tl2) ->
        if s1 <> s2 then
          (error (Type_clash_error( to_string t1, to_string t2)) pos);
        begin
          try List.iter2 (fun l l' -> unify l l' pos) tl1 tl2
          with Invalid_argument _ ->
            (error (Type_clash_error( to_string t1, to_string t2)) pos)
        end
      | TDatatype(s1,tl1), TDatatype(s2,tl2) ->
        if s1 <> s2 then
          if s1 <> "" && s2 <> "" then
            (error (Type_clash_error( to_string t1, to_string t2)) pos)
          else
            ();
        begin
          try List.iter2 (fun l l' -> unify l l' pos) tl1 tl2
          with Invalid_argument _ ->
            (error (Type_clash_error( to_string t1, to_string t2)) pos)
        end
      | TFun(pars1,ret1), TFun(pars2,ret2) ->
        begin
          try List.iter2 (fun l l' -> unify l l' pos) pars1 pars2;
            unify ret1 ret2 pos
          with Invalid_argument _ ->
            (error (Type_clash_error( to_string t1, to_string t2)) pos)
        end
      | _ , _ -> (error (Type_clash_error( to_string t1, to_string t2)) pos)
    end
