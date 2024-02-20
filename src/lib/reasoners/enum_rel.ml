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

module A  = Xliteral
module L  = List
module Hs = Hstring

let timer = Timers.M_Sum

type 'a abstract = 'a Enum.abstract =
  | Cons of Hs.t * Ty.t
  | Alien of 'a

module X = Shostak.Combine
module Sh = Shostak.Enum

module Ex = Explanation

module MX = Shostak.MXH
module HSS = Set.Make (struct type t=Hs.t let compare = Hs.compare end)

module LR = Uf.LX

type t = {
  (* TODO: rename the field domains to be consistent with the ADT theory. *)
  mx : (HSS.t * Ex.t) MX.t;
  (* Map of uninterpreted enum semantic values to domains of their possible
     values. The explanation justifies that any value assigned to the semantic
     value has to lie in the domain. *)

  classes : Expr.Set.t list;
  (* State of the union-find represented by all its equivalence classes.
     This state is kept for debugging purposes only. It is updated with
     [Uf.cl_extract] after assuming literals of the theory and returned by
     queries in case of inconsistency. *)

  size_splits : Numbers.Q.t
  (* Estimate the number of case-splits performed by the theory. The
     estimation is updated while assuming new literals of the theory.
     We don't perfom new case-splits if this estimation exceeds
     [Options.get_max_split ()]. *)
}

let empty classes = {
  mx = MX.empty;
  classes = classes;
  size_splits = Numbers.Q.one
}

(*BISECT-IGNORE-BEGIN*)
module Debug = struct
  open Printer

  let assume bol r1 r2 =
    if Options.get_debug_sum () then
      print_dbg
        ~module_name:"Enum_rel" ~function_name:"assume"
        "we assume %a %s %a"
        X.print r1 (if bol then "=" else "<>") X.print r2

  let print_env env =
    if Options.get_debug_sum () then begin
      Printer.print_dbg ~flushed:false
        ~module_name:"Enum_rel" ~function_name:"print_env"
        "@[<v 2>--SUM env ---------------------------------@ ";
      MX.iter
        (fun r (hss, ex) ->
           Printer.print_dbg  ~flushed:false ~header:false
             "%a ::= " X.print r;
           begin
             match HSS.elements hss with
               []      -> ()
             | hs :: l ->
               Printer.print_dbg  ~flushed:false ~header:false
                 " %s" (Hs.view hs);
               L.iter (fun hs ->
                   Printer.print_dbg  ~flushed:false ~header:false
                     " | %s" (Hs.view hs)) l
           end;
           Printer.print_dbg ~flushed:false ~header:false
             " : %a@ " Ex.print ex;
        ) env.mx;
      Printer.print_dbg ~header:false
        "@ -------------------------------------------";
    end

  let case_split r r' =
    if Options.get_debug_sum () then
      Printer.print_dbg
        ~module_name:"Enum_rel" ~function_name:"case_split"
        "%a = %a" X.print r X.print r'

  let no_case_split () =
    if Options.get_debug_sum () then
      Printer.print_dbg
        ~module_name:"Enum_rel" ~function_name:"no_case_split"
        "sum: nothing"

  let add r =
    if Options.get_debug_sum () then
      Printer.print_dbg
        ~module_name:"Enum_rel" ~function_name:"add"
        "%a" X.print r

end
(*BISECT-IGNORE-END*)

(* Return the list of all the constructors of the type of [r]. *)
let values_of r =
  match X.type_info r with
  | Ty.Tsum (_,l) ->
    Some (List.fold_left (fun st hs -> HSS.add hs st) HSS.empty l)
  | _ ->
    (* This case can happen since we don't dispatch the literals
       processed in [assume] by their types in the Relation module. *)
    None

(* Update the domains of the semantic values [sm1] and [sm2] according to
   the disequality [sm1 <> sm2]. More precisely, if one of these semantic
   values is a constructor, we remove it from the domain of the other one.

   In any case, we produce an equality if the domain of one of these semantic
   values becomes a singleton.

   @raise Ex.Inconsistent if the disequality is inconsistent with the
   current environment [env]. *)
let add_diseq hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Alien r , Cons(h,ty)
  | Cons (h,ty), Alien r  ->
    let enum, ex = try MX.find r env.mx with Not_found -> hss, Ex.empty in
    let enum = HSS.remove h enum in
    let ex = Ex.union ex dep in
    if HSS.is_empty enum then raise (Ex.Inconsistent (ex, env.classes))
    else
      let env = { env with mx = MX.add r (enum, ex) env.mx } in
      if HSS.cardinal enum = 1 then
        let h' = HSS.choose enum in
        env,
        (Literal.LSem (LR.mkv_eq r (Sh.is_mine (Cons(h',ty)))),
         ex, Th_util.Other)::eqs
      else env, eqs

  | Alien r1, Alien r2 ->
    let enum1,ex1= try MX.find r1 env.mx with Not_found -> hss,Ex.empty in
    let enum2,ex2= try MX.find r2 env.mx with Not_found -> hss,Ex.empty in

    let eqs =
      if HSS.cardinal enum1 = 1 then
        let ex = Ex.union dep ex1 in
        let h' = HSS.choose enum1 in
        let ty = X.type_info r1 in
        (Literal.LSem (LR.mkv_eq r1 (Sh.is_mine (Cons(h',ty)))),
         ex, Th_util.Other)::eqs
      else eqs
    in
    let eqs =
      if HSS.cardinal enum2 = 1 then
        let ex = Ex.union dep ex2 in
        let h' = HSS.choose enum2 in
        let ty = X.type_info r2 in
        (Literal.LSem (LR.mkv_eq r2 (Sh.is_mine (Cons(h',ty)))),
         ex, Th_util.Other)::eqs
      else eqs
    in
    env, eqs

  |  _ -> env, eqs

(* Update the domains of the semantic values [sm1] and [sm2] according to
   the equation [sm1 = sm2]. More precisely, we replace their domains by
   the intersection of these domains.

   @raise Ex.Inconsistent if the domains of [sm1] and [sm2] are disjoint. *)
let add_eq hss sm1 sm2 dep env eqs =
  match sm1, sm2 with
  | Alien r, Cons(h,_)
  | Cons (h,_), Alien r  ->
    let enum, ex = try MX.find r env.mx with Not_found -> hss, Ex.empty in
    let ex = Ex.union ex dep in
    if not (HSS.mem h enum) then raise (Ex.Inconsistent (ex, env.classes));
    (* We don't need to produce a new equality as we are already processing
       it. *)
    {env with mx = MX.add r (HSS.singleton h, ex) env.mx} , eqs

  | Alien r1, Alien r2   ->
    let enum1,ex1 =
      try MX.find r1 env.mx with Not_found -> hss, Ex.empty in
    let enum2,ex2 =
      try MX.find r2 env.mx with Not_found -> hss, Ex.empty in
    let ex = Ex.union dep (Ex.union ex1 ex2) in
    let diff = HSS.inter enum1 enum2 in
    if HSS.is_empty diff then raise (Ex.Inconsistent (ex, env.classes));
    let mx = MX.add r1 (diff, ex) env.mx in
    let env = {env with mx = MX.add r2 (diff, ex) mx } in

    (* We produce an equality if the domain of these semantic values becomes
       a singleton. *)
    if HSS.cardinal diff = 1 then
      let h' = HSS.choose diff in
      let ty = X.type_info r1 in
      env, (Literal.LSem (LR.mkv_eq r1 (Sh.is_mine (Cons(h',ty)))),
            ex, Th_util.Other)::eqs
    else env, eqs

  |  _ -> env, eqs

(* Update the counter of case-split size in [env]. *)
let count_splits env la =
  let nb =
    List.fold_left
      (fun nb (_,_,_,i) ->
         match i with
         | Th_util.CS (Th_util.Th_sum, n) -> Numbers.Q.mult nb n
         | _ -> nb
      )env.size_splits la
  in
  {env with size_splits = nb}

(* Add the uninterpreted semantic value [r] to the environment [env] with
   all the constructors of its type as domain. *)
let add_aux env r =
  Debug.add r;
  match Sh.embed r, values_of r with
  | Alien r, Some hss ->
    if MX.mem r env.mx then env else
      { env with mx = MX.add r (hss, Ex.empty) env.mx }
  | _ -> env

(* Needed for models generation because fresh terms are not added with function
   add. *)
let add_rec env r = List.fold_left add_aux env (X.leaves r)

let assume env uf la =
  let env = count_splits env la in
  let classes = Uf.cl_extract uf in
  let env = { env with classes = classes } in
  let aux bol r1 r2 dep env eqs = function
    | None     -> env, eqs
    | Some hss ->
      Debug.assume bol r1 r2;
      if bol then
        add_eq hss (Sh.embed r1) (Sh.embed r2) dep env eqs
      else
        add_diseq hss (Sh.embed r1) (Sh.embed r2) dep env eqs
  in
  Debug.print_env env;
  let env, eqs =
    List.fold_left
      (fun (env,eqs) -> function
         | A.Eq(r1,r2), _, ex, _ ->
           (* needed for models generation because fresh terms are not
              added with function add *)
           let env = add_rec (add_rec env r1) r2 in
           aux true  r1 r2 ex env eqs (values_of r1)

         | A.Distinct(false, [r1;r2]), _, ex, _ ->
           (* needed for models generation because fresh terms are not
              added with function add *)
           let env = add_rec (add_rec env r1) r2 in
           aux false r1 r2 ex env eqs (values_of r1)

         | _ -> env, eqs

      ) (env,[]) la
  in
  env, { Sig_rel.assume = eqs; remove = [] }

let add env _ r _ = add_aux env r, []

(* Do a case-split by choosing a value for an uninterpreted semantic value
   whose domain in [env] is of minimal size. *)
let case_split env uf ~for_model =
  let acc = MX.fold
      (fun r (hss, _) acc ->
         let x, _ = Uf.find_r uf r in
         match Sh.embed x with
         | Cons _ ->
           (* The equivalence class of [r] already contains a value so
              we don't need to make another case-split for this semantic
              value. *)
           acc
         | _ ->
           (* We have to perform a case-split, even if the domain of [r] is
              of cardinal 1 as we have to let the union-find know this
              equality. *)
           let sz = HSS.cardinal hss in
           match acc with
           | Some (n,_,_) when n <= sz -> acc
           | _ -> Some (sz, r, HSS.choose hss)
      ) env.mx None
  in
  match acc with
  | Some (n,r,hs) ->
    let n = Numbers.Q.from_int n in
    if for_model ||
       Numbers.Q.compare
         (Numbers.Q.mult n env.size_splits) (Options.get_max_split ()) <= 0  ||
       Numbers.Q.sign  (Options.get_max_split ()) < 0 then
      let r' = Sh.is_mine (Cons(hs,X.type_info r)) in
      Debug.case_split r r';
      [LR.mkv_eq r r', true, Th_util.CS (Th_util.Th_sum, n)]
    else
      []
  | None ->
    Debug.no_case_split ();
    []

let optimizing_objective _env _uf _o = None

let query env uf a_ex =
  try ignore(assume env uf [a_ex]); None
  with Ex.Inconsistent (expl, classes) -> Some (expl, classes)

let new_terms _ = Expr.Set.empty

let instantiate ~do_syntactic_matching:_ _ env _ _  = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Sum ->
    failwith "This Theory does not support theories extension"
  | _ -> t
