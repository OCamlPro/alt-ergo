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
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

open Alias.Dolmen

type t =
  | Tint
  | Treal
  | Tbool
  | Tvar of tvar
  | Tbitv of int
  | Text of t list * DE.ty_cst
  | Tfarray of t * t
  | Tadt of DE.ty_cst * t list
  | Trecord of trecord

and tvar = { v : int ; mutable value : t option }

and trecord = {
  mutable args : t list;
  name : DE.ty_cst;
  mutable lbs :  (DE.term_cst * t) list;
  record_constr : DE.term_cst;
  (* for ADTs that become records. default is "{" *)
}

module Smtlib = struct
  let rec pp ppf = function
    | Tint -> Fmt.pf ppf "Int"
    | Treal -> Fmt.pf ppf "Real"
    | Tbool -> Fmt.pf ppf "Bool"
    | Tbitv n -> Fmt.pf ppf "(_ BitVec %d)" n
    | Tfarray (a_t, r_t) ->
      Fmt.pf ppf "(Array %a %a)" pp a_t pp r_t
    | Text ([], name)
    | Trecord { args = []; name; _ } | Tadt (name, []) ->
      DE.Ty.Const.print ppf name
    | Text (args, name)
    | Trecord { args; name; _ } | Tadt (name, args) ->
      Fmt.(pf ppf "(@[%a %a@])" DE.Ty.Const.print name (list ~sep:sp pp) args)
    | Tvar { v; value = None; _ } -> Fmt.pf ppf "A%d" v
    | Tvar { value = Some t; _ } -> pp ppf t
end

let pp_smtlib = Smtlib.pp

exception TypeClash of t*t
exception Shorten of t

type adt_constr =
  { constr : DE.term_cst ;
    destrs : (DE.term_cst * t) list }

type type_body = adt_constr list

let assoc_destrs hs cases =
  let res = ref None in
  try
    List.iter
      (fun {constr = s ; destrs = t} ->
         if DE.Term.Const.equal hs s then begin
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
  let rec print =
    let open Format in
    fun body_of fmt -> function
      | Tint -> fprintf fmt "int"
      | Treal -> fprintf fmt "real"
      | Tbool -> fprintf fmt "bool"
      | Tbitv n -> fprintf fmt "bitv[%d]" n
      | Tvar{v=v ; value = None} -> fprintf fmt "'a_%d" v
      | Tvar{v=v ; value = Some (Trecord { args = l; name = n; _ } as t) } ->
        if Hashtbl.mem h v then
          fprintf fmt "%a %a" print_list l DE.Ty.Const.print n
        else
          (Hashtbl.add h v ();
           (*fprintf fmt "('a_%d->%a)" v print t *)
           print body_of fmt t)
      | Tvar{ value = Some t; _ } ->
        (*fprintf fmt "('a_%d->%a)" v print t *)
        print body_of fmt t
      | Text(l, s) when l == [] ->
        fprintf fmt "<ext>%a" DE.Ty.Const.print s
      | Text(l,s) ->
        fprintf fmt "%a <ext>%a" print_list l DE.Ty.Const.print s
      | Tfarray (t1, t2) ->
        fprintf fmt "(%a,%a) farray" (print body_of) t1 (print body_of) t2
      | Trecord { args = lv; name = n; lbs = lbls; _ } ->
        begin
          fprintf fmt "%a <record>%a" print_list lv DE.Ty.Const.print n;
          if body_of != None then begin
            fprintf fmt " = {";
            let first = ref true in
            List.iter
              (fun (s, t) ->
                 fprintf fmt "%s%a : %a" (if !first then "" else "; ")
                   DE.Term.Const.print s (print body_of) t;
                 first := false
              ) lbls;
            fprintf fmt "}"
          end
        end
      | Tadt (n, lv) ->
        fprintf fmt "%a <adt>%a" print_list lv DE.Ty.Const.print n;
        begin match body_of with
          | None -> ()
          | Some type_body ->
            let cases = type_body n lv in
            fprintf fmt " = {";
            let first = ref true in
            List.iter
              (fun {constr = s ; destrs = t} ->
                 fprintf fmt "%s%a%a" (if !first then "" else " | ")
                   DE.Term.Const.print s print_adt_tuple t;
                 first := false
              ) cases;
            fprintf fmt "}"
        end

  and print_adt_tuple fmt = function
    | [] -> ()
    | (d, e)::l ->
      Format.fprintf fmt " of { %a : %a " DE.Term.Const.print d (print None) e;
      List.iter
        (fun (d, e) ->
           Format.fprintf fmt "; %a : %a " DE.Term.Const.print d (print None) e
        ) l;
      Format.fprintf fmt "}"

  and print_list fmt = function
    | [] -> ()
    | [t] -> Format.fprintf fmt "%a " (print body_of) t
    | t::l ->
      Format.fprintf fmt "(%a" (print body_of) t;
      List.iter (Format.fprintf fmt ", %a" (print body_of)) l;
      Format.fprintf fmt ")"
  in
  let print body_of ppf t =
    if Options.get_output_smtlib () then
      pp_smtlib ppf t
    else
      print body_of ppf t
  and print_list ppf ts =
    if Options.get_output_smtlib () then
      Fmt.(list ~sep:sp pp_smtlib |> parens) ppf ts
    else
      print_list ppf ts
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
    let l, same = My_list.apply shorten l in
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

  | Tint | Treal | Tbool | Tbitv _ -> ty

and shorten_body _ _ =
  ()
  [@ocaml.ppwarning "TODO: should be implemented ?"]

let rec compare t1 t2 =
  match shorten t1 , shorten t2 with
  | Tvar{ v = v1; _ } , Tvar{ v = v2; _ } -> Int.compare v1 v2
  | Tvar _, _ -> -1 | _ , Tvar _ -> 1
  | Text(l1, s1) , Text(l2, s2) ->
    let c = DE.Ty.Const.compare s1 s2 in
    if c<>0 then c
    else compare_list l1 l2
  | Text _, _ -> -1 | _ , Text _ -> 1
  | Tfarray (ta1,ta2), Tfarray (tb1,tb2) ->
    let c = compare ta1 tb1 in
    if c<>0 then c
    else compare ta2 tb2
  | Tfarray _, _ -> -1 | _ , Tfarray _ -> 1
  | Trecord { args = a1; name = s1; lbs = l1; _ },
    Trecord { args = a2; name = s2; lbs = l2; _ } ->
    let c = DE.Ty.Const.compare s1 s2 in
    if c <> 0 then c else
      let c = compare_list a1 a2 in
      if c <> 0 then c else
        let l1, l2 = List.map snd l1, List.map snd l2 in
        compare_list l1 l2
  | Trecord _, _ -> -1 | _ , Trecord _ -> 1

  | Tadt (s1, pars1), Tadt (s2, pars2) ->
    let c = DE.Ty.Const.compare s1 s2 in
    if c <> 0 then c
    else compare_list pars1 pars2
  (* no need to compare bodies *)

  | Tadt _, _ -> -1 | _ , Tadt _ -> 1

  | Tint, Tint -> 0
  | Tint, _ -> -1 | _, Tint -> 1

  | Treal, Treal -> 0
  | Treal, _ -> -1 | _, Treal -> 1

  | Tbool, Tbool -> 0
  | Tbool, _ -> -1 | _, Tbool -> 1

  | Tbitv sz1, Tbitv sz2 -> Int.compare sz1 sz2

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
    (try DE.Ty.Const.equal s1 s2 && List.for_all2 equal l1 l2
     with Invalid_argument _ -> false)
  | Tfarray (ta1, ta2), Tfarray (tb1, tb2) ->
    equal ta1 tb1 && equal ta2 tb2
  | Trecord { args = a1; name = s1; lbs = l1; _ },
    Trecord { args = a2; name = s2; lbs = l2; _ } ->
    begin
      try
        DE.Ty.Const.equal s1 s2 && List.for_all2 equal a1 a2 &&
        List.for_all2
          (fun (l1, ty1) (l2, ty2) ->
             DE.Term.Const.equal l1 l2 && equal ty1 ty2) l1 l2
      with Invalid_argument _ -> false
    end
  | Tint, Tint | Treal, Treal | Tbool, Tbool -> true
  | Tbitv n1, Tbitv n2 -> n1 =n2

  | Tadt (s1, pars1), Tadt (s2, pars2) ->
    begin
      try DE.Ty.Const.equal s1 s2 && List.for_all2 equal pars1 pars2
      with Invalid_argument _ -> false
      (* no need to compare bodies *)
    end

  | _ -> false

(*** matching with a substitution mechanism ***)
module M = Util.MI
type subst = t M.t

let esubst = M.empty

let rec matching s pat t =
  match pat , t with
  | Tvar {v=n;value=None} , _ ->
    (try if not (equal (M.find n s) t) then raise (TypeClash(pat,t)); s
     with Not_found -> M.add n t s)
  | Tvar { value = _; _ }, _ -> raise (Shorten pat)
  | Text (l1,s1) , Text (l2,s2) when DE.Ty.Const.equal s1 s2 ->
    List.fold_left2 matching s l1 l2
  | Tfarray (ta1,ta2), Tfarray (tb1,tb2) ->
    matching (matching s ta1 tb1) ta2 tb2
  | Trecord r1, Trecord r2 when DE.Ty.Const.equal r1.name r2.name ->
    let s = List.fold_left2 matching s r1.args r2.args in
    List.fold_left2
      (fun s (_, p) (_, ty) -> matching s p ty) s r1.lbs r2.lbs
  | Tint , Tint | Tbool , Tbool | Treal , Treal -> s
  | Tbitv n , Tbitv m when n=m -> s
  | Tadt(n1, args1), Tadt(n2, args2) when DE.Ty.Const.equal n1 n2 ->
    List.fold_left2 matching s args1 args2
  | _ , _ ->
    raise (TypeClash(pat,t))

let apply_subst =
  let rec apply_subst s ty =
    match ty with
    | Tvar { v= n; _ } ->
      (try M.find n s with Not_found -> ty)

    | Text (l,e) ->
      let l, same = My_list.apply (apply_subst s) l in
      if same then ty else Text(l, e)

    | Tfarray (t1,t2) ->
      let t1' = apply_subst s t1 in
      let t2' = apply_subst s t2 in
      if t1 == t1' && t2 == t2' then ty else Tfarray (t1', t2')

    | Trecord r ->
      let lbs,  same1 = My_list.apply_right (apply_subst s) r.lbs in
      let args, same2 = My_list.apply (apply_subst s) r.args in
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

    | Tint | Treal | Tbool | Tbitv _ -> ty
  in
  fun s ty -> if M.is_empty s then ty else apply_subst s ty

(* Assume that [shorten] have been applied on [ty]. *)
let rec fresh ty subst =
  match ty with
  | Tvar { value = Some _; _ } ->
    (* This case is eliminated by the normalization performed
       in [shorten]. *)
    assert false

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
  | Tadt(s, args) ->
    let args, subst = fresh_list args subst in
    Tadt (s, args), subst
  | t -> t, subst

(* Assume that [shorten] have been applied on [lty]. *)
and fresh_list lty subst =
  List.fold_right
    (fun ty (lty, subst) ->
       let ty, subst = fresh ty subst in
       ty::lty, subst) lty ([], subst)

let fresh ty subst = fresh (shorten ty) subst

let fresh_list lty subst = fresh_list (List.map shorten lty) subst

module Decls = struct

  module MH = Map.Make (DE.Ty.Const)

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


  let fresh_type params cases =
    let params, subst = fresh_list params esubst in
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
    params, cases


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
        let params, cases = fresh_type params body in
        (*if true || get_debug_adt () then*)
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
                   Printer.print_err "vty = %a and ty = %a"
                     print vty print ty;
                   assert false
              )M.empty params args
          with Invalid_argument _ -> assert false
        in
        let cases =
          List.map
            (fun {constr; destrs} ->
               {constr;
                destrs =
                  List.map (fun (d, ty) -> d, apply_subst sbt ty) destrs }
            ) cases
        in
        let params = List.map (fun ty -> apply_subst sbt ty) params in
        add name params cases;
        cases
    with Not_found ->
      Printer.print_err "%a not found" DE.Ty.Const.print name;
      assert false

  let reinit () = decls := MH.empty

end

let type_body name args = Decls.body name args


(* smart constructors *)
let text l s = Text (l, s)

let fresh_empty_text =
  let cpt = ref (-1) in
  fun () ->
    incr cpt;
    let id =
      let path = DStd.Path.global @@ Fmt.str "'_c%d" !cpt in
      DStd.Expr.Ty.Const.mk path 0
    in
    text [] id

let t_adt ?(body=None) s ty_vars =
  let ty = Tadt (s, ty_vars) in
  begin match body with
    | None -> ()
    | Some [] -> assert false
    | Some ([_] as cases) ->
      if Options.get_debug_adt () then
        Printer.print_dbg ~module_name:"Ty"
          "should be registered as a record";
      let cases =
        List.map (fun (constr, destrs) -> {constr; destrs}) cases
      in
      Decls.add s ty_vars cases
    | Some cases ->
      let cases =
        List.map (fun (constr, destrs) -> {constr; destrs}) cases
      in
      Decls.add s ty_vars cases
  end;
  ty

let tunit =
  let () =
    match DE.Ty.definition DT.Const.unit with
    | Some def -> Nest.attach_orders [def]
    | None -> assert false
  in
  let body = Some [DE.Term.Cstr.void, []] in
  let ty = t_adt ~body DT.Const.unit [] in
  ty

let trecord ~record_constr lv name lbs =
  Trecord { record_constr; args = lv; name; lbs = lbs}

let rec hash t =
  match t with
  | Tvar{ v; _ } -> v
  | Text(l,s) ->
    abs (List.fold_left (fun acc x-> acc*19 + hash x) (DE.Ty.Const.hash s) l)
  | Tfarray (t1,t2) -> 19 * (hash t1) + 23 * (hash t2)
  | Trecord { args; name = s; _ } ->
    (* We do not hash constructors. *)
    let h =
      List.fold_left (fun h ty -> 27 * h + hash ty) (DE.Ty.Const.hash s) args
    in
    abs h

  | Tadt (ty, args) ->
    (* We do not hash constructors. *)
    let h =
      List.fold_left (fun h ty -> 31 * h + hash ty) (DE.Ty.Const.hash ty) args
    in
    abs h

  | _ -> Hashtbl.hash t

let compare_subst = M.compare compare

let equal_subst = M.equal equal

module Svty = Util.SI

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
    | Tint | Treal | Tbool | Tbitv _ ->
      acc
  in
  vty_of_rec Svty.empty t

let print_subst =
  let sep ppf () = Fmt.pf ppf " -> " in
  Fmt.(box @@ braces
       @@ iter_bindings ~sep:comma M.iter (pair ~sep int print))

let print_full =
  fst (print_generic (Some type_body)) (Some type_body)

(** Goal sort *)

type goal_sort = Cut | Check | Thm | Sat

let print_goal_sort fmt = function
  | Cut -> Format.fprintf fmt "cut"
  | Check -> Format.fprintf fmt "check"
  | Thm -> Format.fprintf fmt "thm"
  | Sat -> Format.fprintf fmt "sat"

let fresh_hypothesis_name =
  let cpt = ref 0 in
  fun sort ->
    incr cpt;
    match sort with
    | Thm | Sat -> "@H"^(string_of_int !cpt)
    | _ -> "@L"^(string_of_int !cpt)

let is_local_hyp s =
  try String.equal (String.sub s 0 2) "@L" with Invalid_argument _ -> false

let is_global_hyp s =
  try String.equal (String.sub s 0 2) "@H" with Invalid_argument _ -> false

(* Context reinitialization *)
let reinit_decls () = Decls.reinit ()
