(******************************************************************************)
(*                                                                            *)
(*     The Alt-Ergo theorem prover                                            *)
(*     Copyright (C) 2006-2013                                                *)
(*                                                                            *)
(*     Sylvain Conchon                                                        *)
(*     Evelyne Contejean                                                      *)
(*                                                                            *)
(*     Francois Bobot                                                         *)
(*     Mohamed Iguernelala                                                    *)
(*     Stephane Lescuyer                                                      *)
(*     Alain Mebsout                                                          *)
(*                                                                            *)
(*     CNRS - INRIA - Universite Paris Sud                                    *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(*  ------------------------------------------------------------------------  *)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the Apache Software        *)
(*     License version 2.0                                                    *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options

type t =
  | Tint
  | Treal
  | Tbool
  | Tunit
  | Tvar of tvar
  | Tbitv of int
  | Text of t list * Hstring.t
  | Tfarray of t * t
  | Tsum of Hstring.t * Hstring.t list
  | Tadt of Hstring.t * t list
  | Trecord of trecord

and tvar = { v : int ; mutable value : t option }
and trecord = {
  mutable args : t list;
  name : Hstring.t;
  mutable lbs :  (Hstring.t * t) list;
  record_constr : Hstring.t; (* for ADTs that become records. default is "{" *)
}

exception TypeClash of t*t
exception Shorten of t

type adt_constr =
  { constr : Hstring.t ;
    destrs : (Hstring.t * t) list }

type type_body =
  | Adt of adt_constr list


let assoc_destrs hs cases =
  let res = ref None in
  try
    List.iter
      (fun {constr = s ; destrs = t} ->
         if Hstring.equal hs s then begin
           res := Some t;
           raise Exit
         end
      )cases;
    raise Not_found
  with Exit ->
  match !res with
  | None -> assert false
  | Some destrs -> destrs


(*** pretty print ***)
let print_generic body_of =
  let h = Hashtbl.create 17 in
  let rec print body_of fmt = function
    | Tint -> fprintf fmt "int"
    | Treal -> fprintf fmt "real"
    | Tbool -> fprintf fmt "bool"
    | Tunit -> fprintf fmt "unit"
    | Tbitv n -> fprintf fmt "bitv[%d]" n
    | Tvar{v=v ; value = None} -> fprintf fmt "'a_%d" v
    | Tvar{v=v ; value = Some (Trecord { args = l; name = n; _ } as t) } ->
      if Hashtbl.mem h v then
        fprintf fmt "%a %s" print_list l (Hstring.view n)
      else
        (Hashtbl.add h v ();
         (*fprintf fmt "('a_%d->%a)" v print t *)
         print body_of fmt t)
    | Tvar{ value = Some t; _ } ->
      (*fprintf fmt "('a_%d->%a)" v print t *)
      print body_of fmt t
    | Text(l, s) -> fprintf fmt "%a <ext>%s" print_list l (Hstring.view s)
    | Tfarray (t1, t2) ->
      fprintf fmt "(%a,%a) farray" (print body_of) t1 (print body_of) t2
    | Tsum(s, _) -> fprintf fmt "<sum>%s" (Hstring.view s)
    | Trecord { args = lv; name = n; lbs = lbls; _ } ->
      fprintf fmt "%a <record>%s" print_list lv (Hstring.view n);
      if body_of != None then begin
        fprintf fmt " = {";
        let first = ref true in
        List.iter
          (fun (s, t) ->
             fprintf fmt "%s%s : %a" (if !first then "" else "; ")
               (Hstring.view s) (print body_of) t;
             first := false
          ) lbls;
        fprintf fmt "}"
      end
    | Tadt (n, lv) ->
      fprintf fmt "%a <adt>%s" print_list lv (Hstring.view n);
      begin match body_of with
        | None -> ()
        | Some type_body ->
          let cases = match type_body n lv with
            | Adt cases -> cases
          in
          fprintf fmt " = {";
          let first = ref true in
          List.iter
            (fun {constr = s ; destrs = t} ->
               fprintf fmt "%s%s%a" (if !first then "" else " | ")
                 (Hstring.view s) print_adt_tuple t;
               first := false
            ) cases;
          fprintf fmt "}"
      end

  and print_adt_tuple fmt = function
    | [] -> ()
    | (d, e)::l ->
      fprintf fmt " of { %a : %a " Hstring.print d (print None) e;
      List.iter
        (fun (d, e) ->
           fprintf fmt "; %a : %a " Hstring.print d (print None) e
        ) l;
      fprintf fmt "}"

  and print_list fmt = function
    | [] -> ()
    | [t] -> fprintf fmt "%a " (print body_of) t
    | t::l ->
      fprintf fmt "(%a" (print body_of) t;
      List.iter (fprintf fmt ", %a" (print body_of)) l;
      fprintf fmt ")"
  in
  print, print_list

let print_list = snd (print_generic None)
let print      = fst (print_generic None) None


let fresh_var =
  let cpt = ref (-1) in
  fun () -> incr cpt; {v= !cpt ; value = None }

let fresh_tvar () = Tvar (fresh_var ())

let rec shorten ty =
  match ty with
  | Tvar { value = None; _ }  -> ty
  | Tvar { value = Some (Tvar{ value = None; _ } as t'); _ } -> t'
  | Tvar ({ value = Some (Tvar t2); _ } as t1) ->
    t1.value <- t2.value; shorten ty
  | Tvar { value = Some t'; _ } -> shorten t'

  | Text (l,s) ->
    let l, same = Lists.apply shorten l in
    if same then ty else Text(l,s)

  | Tfarray (t1,t2) ->
    let t1' = shorten t1 in
    let t2' = shorten t2 in
    if t1 == t1' && t2 == t2' then ty
    else Tfarray(t1', t2')

  | Trecord r ->
    r.args <- List.map shorten r.args;
    r.lbs <- List.map (fun (lb, ty) -> lb, shorten ty) r.lbs;
    ty

  | Tadt (n, args) ->
    let args' = List.map shorten args in
    shorten_body n args;
    (* should not rebuild the type if no changes are made *)
    Tadt (n, args')

  | Tint | Treal | Tbool | Tunit | Tbitv _ | Tsum (_, _) -> ty

and shorten_body _ _ =
  ()
    [@ocaml.ppwarning "TODO: should be implemented ?"]

let rec compare t1 t2 =
  match shorten t1 , shorten t2 with
  | Tvar{ v = v1; _ } , Tvar{ v = v2; _ } -> Pervasives.compare v1 v2
  | Tvar _, _ -> -1 | _ , Tvar _ -> 1
  | Text(l1, s1) , Text(l2, s2) ->
    let c = Hstring.compare s1 s2 in
    if c<>0 then c
    else compare_list l1 l2
  | Text _, _ -> -1 | _ , Text _ -> 1
  | Tfarray (ta1,ta2), Tfarray (tb1,tb2) ->
    let c = compare ta1 tb1 in
    if c<>0 then c
    else compare ta2 tb2
  | Tfarray _, _ -> -1 | _ , Tfarray _ -> 1
  | Tsum(s1, _), Tsum(s2, _) ->
    Hstring.compare s1 s2
  | Tsum _, _ -> -1 | _ , Tsum _ -> 1
  | Trecord { args = a1; name = s1; lbs = l1; _ },
    Trecord { args = a2; name = s2; lbs = l2; _ } ->
    let c = Hstring.compare s1 s2 in
    if c <> 0 then c else
      let c = compare_list a1 a2 in
      if c <> 0 then c else
        let l1, l2 = List.map snd l1, List.map snd l2 in
        compare_list l1 l2
  | Trecord _, _ -> -1 | _ , Trecord _ -> 1

  | Tadt (s1, pars1), Tadt (s2, pars2) ->
    let c = Hstring.compare s1 s2 in
    if c <> 0 then c
    else compare_list pars1 pars2
  (* no need to compare bodies *)

  | Tadt _, _ -> -1 | _ , Tadt _ -> 1

  | t1 , t2 -> Pervasives.compare t1 t2


and compare_list l1 l2 = match l1, l2 with
  | [] , [] -> 0
  | [] , _ -> -1
  | _ , [] -> 1
  | x::ll1 , y::ll2 ->
    let c = compare x y in
    if c<>0 then c else compare_list ll1 ll2

let rec equal t1 t2 =
  t1 == t2 ||
  match shorten t1 , shorten t2 with
  | Tvar{ v = v1; _ }, Tvar{ v = v2; _ } -> v1 = v2
  | Text(l1, s1), Text(l2, s2) ->
    (try Hstring.equal s1 s2 && List.for_all2 equal l1 l2
     with Invalid_argument _ -> false)
  | Tfarray (ta1, ta2), Tfarray (tb1, tb2) ->
    equal ta1 tb1 && equal ta2 tb2
  | Tsum (s1, _), Tsum (s2, _) -> Hstring.equal s1 s2
  | Trecord { args = a1; name = s1; lbs = l1; _ },
    Trecord { args = a2; name = s2; lbs = l2; _ } ->
    begin
      try
        Hstring.equal s1 s2 && List.for_all2 equal a1 a2 &&
        List.for_all2
          (fun (l1, ty1) (l2, ty2) ->
             Hstring.equal l1 l2 && equal ty1 ty2) l1 l2
      with Invalid_argument _ -> false
    end
  | Tint, Tint | Treal, Treal | Tbool, Tbool | Tunit, Tunit -> true
  | Tbitv n1, Tbitv n2 -> n1 =n2

  | Tadt (s1, pars1), Tadt (s2, pars2) ->
    begin
      try Hstring.equal s1 s2 && List.for_all2 equal pars1 pars2
      with Invalid_argument _ -> false
      (* no need to compare bodies *)
    end

  | _ -> false

(*** matching with a substitution mechanism ***)
module M = Map.Make(struct type t=int let compare = Pervasives.compare end)
type subst = t M.t

let esubst = M.empty

let rec matching s pat t =
  match pat , t with
  | Tvar {v=n;value=None} , _ ->
    (try if not (equal (M.find n s) t) then raise (TypeClash(pat,t)); s
     with Not_found -> M.add n t s)
  | Tvar { value = _; _ }, _ -> raise (Shorten pat)
  | Text (l1,s1) , Text (l2,s2) when Hstring.equal s1 s2 ->
    List.fold_left2 matching s l1 l2
  | Tfarray (ta1,ta2), Tfarray (tb1,tb2) ->
    matching (matching s ta1 tb1) ta2 tb2
  | Trecord r1, Trecord r2 when Hstring.equal r1.name r2.name ->
    let s = List.fold_left2 matching s r1.args r2.args in
    List.fold_left2
      (fun s (_, p) (_, ty) -> matching s p ty) s r1.lbs r2.lbs
  | Tsum (s1, _), Tsum (s2, _) when Hstring.equal s1 s2 -> s
  | Tint , Tint | Tbool , Tbool | Treal , Treal | Tunit, Tunit -> s
  | Tbitv n , Tbitv m when n=m -> s
  | Tadt(n1, args1), Tadt(n2, args2) when Hstring.equal n1 n2 ->
    List.fold_left2 matching s args1 args2
  | _ , _ ->
    raise (TypeClash(pat,t))

let apply_subst =
  let rec apply_subst s ty =
    match ty with
    | Tvar { v= n; _ } ->
      (try M.find n s with Not_found -> ty)

    | Text (l,e) ->
      let l, same = Lists.apply (apply_subst s) l in
      if same then ty else Text(l, e)

    | Tfarray (t1,t2) ->
      let t1' = apply_subst s t1 in
      let t2' = apply_subst s t2 in
      if t1 == t1' && t2 == t2' then ty else Tfarray (t1', t2')

    | Trecord r ->
      let lbs,  same1 = Lists.apply_right (apply_subst s) r.lbs in
      let args, same2 = Lists.apply (apply_subst s) r.args in
      if same1 && same2 then ty
      else
        Trecord
          {r with args = args;
                  name = r.name;
                  lbs = lbs}

    | Tadt(name, params)
        [@ocaml.ppwarning "TODO: detect when there are no changes "]
      ->
      Tadt (name, List.map (apply_subst s) params)

    | Tint | Treal | Tbool | Tunit | Tbitv _ | Tsum (_, _) -> ty
  in
  fun s ty -> if M.is_empty s then ty else apply_subst s ty

let rec fresh ty subst =
  match ty with
  | Tvar { v= x; _ } ->
    begin
      try M.find x subst, subst
      with Not_found ->
        let nv = Tvar (fresh_var()) in
        nv, M.add x nv subst
    end
  | Text (args, n) ->
    let args, subst = fresh_list args subst in
    Text (args, n), subst
  | Tfarray (ty1, ty2) ->
    let ty1, subst = fresh ty1 subst in
    let ty2, subst = fresh ty2 subst in
    Tfarray (ty1, ty2), subst
  | Trecord ({ args; name = n; lbs; _ } as r) ->
    let args, subst = fresh_list args subst in
    let lbs, subst =
      List.fold_right
        (fun (x,ty) (lbs, subst) ->
           let ty, subst = fresh ty subst in
           (x, ty)::lbs, subst) lbs ([], subst)
    in
    Trecord {r with  args = args; name = n; lbs = lbs}, subst
  | Tadt(s,args) ->
    let args, subst = fresh_list args subst in
    Tadt (s,args), subst
  | t -> t, subst

and fresh_list lty subst =
  List.fold_right
    (fun ty (lty, subst) ->
       let ty, subst = fresh ty subst in
       ty::lty, subst) lty ([], subst)

module Decls = struct

  module MH = Hstring.Map

  module MTY = Map.Make(struct
      type ty = t
      type t = ty list
      let compare = compare_list
    end)

  type decl =
    { decl : t list * type_body;
      instances : type_body MTY.t }

  type decls = decl MH.t

  let (decls : decls ref) = ref MH.empty


  let fresh_type params body =
    let params, subst = fresh_list params esubst in
    match body with
    | Adt cases ->
      let _subst, cases =
        List.fold_left
          (fun (subst, cases) {constr; destrs} ->
             let subst, destrs =
               List.fold_left
                 (fun (subst, destrs) (d, ty) ->
                    let ty, subst = fresh ty subst in
                    subst, (d, ty) :: destrs
                 )(subst, []) (List.rev destrs)
             in
             subst, {constr; destrs} :: cases
          )(subst, []) (List.rev cases)
      in
      params, Adt cases


  let add name params body =
    try
      let decl = MH.find name !decls in
      let decl = {decl with instances = MTY.add params body decl.instances} in
      decls := MH.add name decl !decls
    with Not_found ->
      let params, body = fresh_type params body in
      decls :=
        MH.add name {decl = (params, body); instances = MTY.empty} !decls

  let body name args =
    try
      let {decl = (params, body); instances} = MH.find name !decls in
      try
        if compare_list params args = 0 then body
        else MTY.find args instances
      (* should I instantiate if not found ?? *)
      with Not_found ->
        let params, body = fresh_type params body in
        (*if true || debug_adt () then*)
        let sbt =
          try
            List.fold_left2
              (fun sbt vty ty ->
                 let vty = shorten vty in
                 match vty with
                 | Tvar { value = Some _ ; _ } -> assert false
                 | Tvar {v ; value = None}   ->
                   if equal vty ty then sbt else M.add v ty sbt
                 | _ ->
                   fprintf fmt "vty = %a and ty = %a@." print vty print ty;
                   assert false
              )M.empty params args
          with Invalid_argument _ -> assert false
        in
        let body = match body with
          | Adt cases ->
            Adt(
              List.map
                (fun {constr; destrs} ->
                   {constr;
                    destrs =
                      List.map (fun (d, ty) -> d, apply_subst sbt ty) destrs }
                ) cases
            )
        in
        let params = List.map (fun ty -> apply_subst sbt ty) params in
        add name params body;
        body
    with Not_found ->
      if debug_adt () then
        fprintf fmt "%a not found@." Hstring.print name;
      assert false
end

let type_body name args = Decls.body name args


(* smart constructors *)
let tunit = Text ([],Hstring.make "unit")

let text l s = Text (l,Hstring.make s)

let fresh_empty_text =
  let cpt = ref (-1) in
  fun () -> incr cpt; text [] ("'_c"^(string_of_int !cpt))

let tsum s lc = Tsum (Hstring.make s, List.map Hstring.make lc)

let t_adt ?(body=None) s ty_vars =
  let hs = Hstring.make s in
  let ty = Tadt (hs, ty_vars) in
  begin match body with
    | None -> ()
    | Some [] -> assert false
    | Some ([_] as cases) ->
      if debug_adt () then
        Format.eprintf "should be registered as a record@.";
      let cases =
        List.map (fun (s, l) ->
            let l =
              List.map (fun (d, e) -> Hstring.make d, e) l
            in
            {constr = Hstring.make s ; destrs = l}
          ) cases
      in
      Decls.add hs ty_vars (Adt cases)
    | Some cases ->
      let cases =
        List.map (fun (s, l) ->
            let l =
              List.map (fun (d, e) -> Hstring.make d, e) l
            in
            {constr = Hstring.make s; destrs = l}
          ) cases
      in
      Decls.add hs ty_vars (Adt cases)
  end;
  ty

let trecord ?(record_constr="{") lv n lbs =
  let lbs = List.map (fun (l,ty) -> Hstring.make l, ty) lbs in
  let lbs, record_constr =
    if String.equal record_constr "{" then
      List.sort (fun (l1, _) (l2, _) -> Hstring.compare l1 l2) lbs,
      sprintf "%s___%s" record_constr n
    else lbs, record_constr
  in
  let record_constr = Hstring.make record_constr in
  Trecord { record_constr; args = lv; name = Hstring.make n; lbs = lbs}

let rec hash t =
  match t with
  | Tvar{ v; _ } -> v
  | Text(l,s) ->
    abs (List.fold_left (fun acc x-> acc*19 + hash x) (Hstring.hash s) l)
  | Tfarray (t1,t2) -> 19 * (hash t1) + 23 * (hash t2)
  | Trecord { args; name = s; lbs; _ } ->
    let h =
      List.fold_left (fun h ty -> 27 * h + hash ty) (Hstring.hash s) args
    in
    let h =
      List.fold_left
        (fun h (lb, ty) -> 23 * h + 19 * (Hstring.hash lb) + hash ty)
        (abs h) lbs
    in
    abs h
  | Tsum (s, _) -> abs (Hstring.hash s) (*we do not hash constructors*)

  | Tadt (s, args) ->
    let h =
      List.fold_left (fun h ty -> 31 * h + hash ty) (Hstring.hash s) args
    in
    abs h

  | _ -> Hashtbl.hash t

let occurs { v = n; _ } t =
  let rec occursrec = function
    | Tvar { v = m; _ } -> n=m
    | Text(l,_) -> List.exists occursrec l
    | Tfarray (t1,t2) -> occursrec t1 || occursrec t2
    | Trecord { args ; _ } | Tadt (_, args) -> List.exists occursrec args
    | Tsum _ | Tint | Treal | Tbool | Tunit | Tbitv _ -> false
  in occursrec t

(*** destructive unification ***)
let rec unify t1 t2 =
  let t1 = shorten t1 in
  let t2 = shorten t2 in
  match t1 , t2 with
    Tvar ({v=n;value=None} as tv1), Tvar {v=m;value=None} ->
    if n<>m then tv1.value <- Some t2
  | _ ,  Tvar ({ value = None; _ } as tv) ->
    if (occurs tv t1) then raise (TypeClash(t1,t2));
    tv.value <- Some t1
  | Tvar ({ value = None; _ } as tv) , _ ->
    if (occurs tv t2) then raise (TypeClash(t1,t2));
    tv.value <- Some t2
  | Text(l1,s1) , Text(l2,s2) when Hstring.equal s1 s2 ->
    List.iter2 unify l1 l2
  | Tfarray (ta1,ta2), Tfarray (tb1,tb2) -> unify ta1 tb1;unify ta2 tb2
  | Trecord r1, Trecord r2 when Hstring.equal r1.name r2.name ->
    List.iter2 unify r1.args r2.args
  | Tsum(s1, _) , Tsum(s2, _) when Hstring.equal s1 s2 -> ()
  | Tint, Tint | Tbool, Tbool | Treal, Treal | Tunit, Tunit -> ()
  | Tbitv n , Tbitv m when m=n -> ()

  | Tadt(n1, p1), Tadt (n2, p2) when Hstring.equal n1 n2 ->
    List.iter2 unify p1 p2

  | _ , _ [@ocaml.ppwarning "TODO: remove fragile pattern "] ->
    raise (TypeClash(t1,t2))

let instantiate lvar lty ty =
  let s =
    List.fold_left2
      (fun s x t ->
         match x with
         | Tvar { v = n; _ } ->
           M.add n t s
         | _ -> assert false) M.empty lvar lty
  in
  apply_subst s ty

let union_subst s1 s2 =
  M.fold (fun k x s2 -> M.add k x s2) (M.map (apply_subst s2)  s1) s2

let compare_subst = M.compare Pervasives.compare

let equal_subst = M.equal Pervasives.(=)

module Svty =
  Set.Make(struct type t = int let compare = Pervasives.compare end)

module Set =
  Set.Make(struct
    type t' = t
    type t = t'
    let compare = compare
  end)

let vty_of t =
  let rec vty_of_rec acc t =
    let t = shorten t in
    match t with
    | Tvar { v = i ; value = None } -> Svty.add i acc
    | Text(l,_) -> List.fold_left vty_of_rec acc l
    | Tfarray (t1,t2) -> vty_of_rec (vty_of_rec acc t1) t2
    | Trecord { args; lbs; _ } ->
      let acc = List.fold_left vty_of_rec acc args in
      List.fold_left (fun acc (_, ty) -> vty_of_rec acc ty) acc lbs
    | Tadt(_, args) ->
      List.fold_left vty_of_rec acc args

    | Tvar { value = Some _ ; _ }
    | Tint | Treal | Tbool | Tunit | Tbitv _ | Tsum (_, _) ->
      acc
  in
  vty_of_rec Svty.empty t


    [@ocaml.ppwarning "TODO: detect when there are no changes "]
let rec monomorphize ty =
  match ty with
  | Tint | Treal | Tbool | Tunit   | Tbitv _  | Tsum _ -> ty
  | Text (tyl,hs) -> Text (List.map monomorphize tyl, hs)
  | Trecord ({ args = tylv; name = n; lbs = tylb; _ } as r) ->
    let m_tylv = List.map monomorphize tylv in
    let m_tylb =
      List.map (fun (lb, ty_lb) -> lb, monomorphize ty_lb) tylb
    in
    Trecord {r with args = m_tylv; name = n; lbs = m_tylb}
  | Tfarray (ty1,ty2)    -> Tfarray (monomorphize ty1,monomorphize ty2)
  | Tvar {v=v; value=None} -> text [] ("'_c"^(string_of_int v))
  | Tvar ({ value = Some ty1; _ } as r) ->
    Tvar { r with value = Some (monomorphize ty1)}
  | Tadt(name, params) ->
    Tadt(name, List.map monomorphize params)



let print_subst fmt sbt =
  M.iter (fun n ty -> fprintf fmt "%d -> %a" n print ty) sbt;
  fprintf fmt "@?"

let print_full =
  fst (print_generic (Some type_body)) (Some type_body)
