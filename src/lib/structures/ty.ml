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

type t =
  | Tint
  | Treal
  | Tbool
  | Tunit
  | Tvar of tvar
  | Tbitv of int
  | Trecord of trecord
  | Text of {
      cstr : Hstring.t;
      params : t list
    }
  | Tfarray of {
      key_ty : t;
      val_ty : t;
    }
  | Tsum of {
      name : Hstring.t;
      cstrs : Hstring.t list
    }
  | Tadt of {
      cstr : Hstring.t;
      payload : t list
    }

and tvar = { v : int ; mutable value : t option }
and trecord = {
  mutable args : t list;
  name : Hstring.t;
  mutable lbs :  (Hstring.t * t) list;
  record_cstr : Hstring.t;
}

exception TypeClash of t*t
exception Shorten of t

type adt_cstr = {
  cstr : Hstring.t ;
  dstrs : (Hstring.t * t) list
}

type type_body =
  | Adt of adt_cstr list


let assoc_destrs hs cases =
  let res = ref None in
  try
    List.iter
      (fun {cstr = s ; dstrs = t} ->
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
  let rec print =
    let open Format in
    fun (body_of: (Hstring.t -> t list -> type_body) option) fmt -> function
      | Tint ->
        if Options.get_output_smtlib () then fprintf fmt "Int"
        else fprintf fmt "int"
      | Treal ->
        if Options.get_output_smtlib () then fprintf fmt "Real"
        else fprintf fmt "real"
      | Tbool ->
        if Options.get_output_smtlib () then fprintf fmt "Bool"
        else fprintf fmt "bool"
      | Tunit -> fprintf fmt "unit"
      | Tbitv n -> fprintf fmt "bitv[%d]" n
      | Tvar { v; value = None } -> fprintf fmt "'a_%d" v
      | Tvar { v; value = Some (Trecord { args; name; _ } as t) } ->
        if Hashtbl.mem h v then
          fprintf fmt "%a %s" print_list args (Hstring.view name)
        else
          (Hashtbl.add h v ();
           (*fprintf fmt "('a_%d->%a)" v print t *)
           print body_of fmt t)
      | Tvar { value = Some t; _ } ->
        (*fprintf fmt "('a_%d->%a)" v print t *)
        print body_of fmt t
      | Text { cstr; params } when params == [] ->
        if Options.get_output_smtlib () then
          fprintf fmt "%s" (Hstring.view cstr)
        else fprintf fmt "<ext>%s" (Hstring.view cstr)
      | Text { cstr; params } ->
        if Options.get_output_smtlib () then
          fprintf fmt "(%s %a)" (Hstring.view cstr) print_list params
        else fprintf fmt "%a <ext>%s" print_list params (Hstring.view cstr)
      | Tfarray { key_ty; val_ty } ->
        if Options.get_output_smtlib () then
          fprintf fmt "(Array %a %a)"  (print body_of) key_ty
            (print body_of) val_ty
        else
          fprintf fmt "(%a,%a) farray" (print body_of) key_ty
            (print body_of) val_ty
      | Tsum { name; _ } ->
        if Options.get_output_smtlib () then
          fprintf fmt "%s" (Hstring.view name)
        else fprintf fmt "<sum>%s" (Hstring.view name)
      | Trecord {args = lv; name; lbs = lbls; _} ->
        if Options.get_output_smtlib () then begin
          if lv == [] then fprintf fmt "%s" (Hstring.view name)
          else fprintf fmt "%a %s" print_list lv (Hstring.view name)
        end
        else begin
          fprintf fmt "%a <record>%s" print_list lv (Hstring.view name);
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
        end
      | Tadt { cstr; payload } ->
        fprintf fmt "%a <adt>%s" print_list payload (Hstring.view cstr);
        begin match body_of with
          | None -> ()
          | Some type_body ->
            let cases = match type_body cstr payload with
              | Adt cases -> cases
            in
            fprintf fmt " = {";
            let first = ref true in
            List.iter
              (fun { cstr; dstrs } ->
                 fprintf fmt "%s%s%a" (if !first then "" else " | ")
                   (Hstring.view cstr) print_adt_tuple dstrs;
                 first := false
              ) cases;
            fprintf fmt "}"
        end

  and print_adt_tuple fmt = function
    | [] -> ()
    | (d, e)::l ->
      Format.fprintf fmt " of { %a : %a " Hstring.print d (print None) e;
      List.iter
        (fun (d, e) ->
           Format.fprintf fmt "; %a : %a " Hstring.print d (print None) e
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
  print, print_list

let print_list = snd (print_generic None)
let print = fst (print_generic None) None

let fresh_var =
  let cpt = ref (-1) in
  fun () -> incr cpt; {v= !cpt ; value = None }

let fresh_tvar () = Tvar (fresh_var ())

let rec shorten ty =
  match ty with
  | Tvar { value = None; _ } -> ty
  | Tvar { value = Some (Tvar {value = None; _} as t'); _ } -> t'
  | Tvar ({value = Some (Tvar t2); _ } as t1) ->
    t1.value <- t2.value; shorten ty
  | Tvar { value = Some t'; _ } -> shorten t'
  | Text { cstr; params } ->
    let params, same = Lists.apply shorten params in
    if same then ty else Text { cstr; params }
  | Tfarray { key_ty; val_ty } ->
    let key_ty' = shorten key_ty in
    let val_ty' = shorten val_ty in
    if key_ty == key_ty' && val_ty == val_ty' then ty
    else Tfarray { key_ty = key_ty'; val_ty = val_ty' }
  | Trecord r ->
    r.args <- List.map shorten r.args;
    r.lbs <- List.map (fun (lb, ty) -> lb, shorten ty) r.lbs;
    ty
  | Tadt { cstr; payload } ->
    let payload' = List.map shorten payload in
    shorten_body cstr payload;
    (* should not rebuild the type if no changes are made *)
    Tadt { cstr; payload = payload' }
  | Tint | Treal | Tbool | Tunit | Tbitv _ | Tsum _ -> ty

and shorten_body _ _ =
  ()
  [@ocaml.ppwarning "TODO: should be implemented ?"]

let rec compare t1 t2 =
  match shorten t1, shorten t2 with
  | Tvar {v = v1; _}, Tvar {v = v2; _} -> Stdlib.compare v1 v2
  | Tvar _, _ -> -1 | _, Tvar _ -> 1
  | Text { cstr = c1; params = a1 }, Text { cstr = c2; params = a2 } ->
    let c = Hstring.compare c1 c2 in
    if c <> 0 then c
    else compare_list a1 a2
  | Text _, _ -> -1 | _ , Text _ -> 1
  | Tfarray {key_ty = key_ty1; val_ty = val_ty1},
    Tfarray {key_ty = key_ty2; val_ty = val_ty2} ->
    let c = compare key_ty1 key_ty2 in
    if c <> 0 then c
    else compare val_ty1 val_ty2
  | Tfarray _, _ -> -1 | _ , Tfarray _ -> 1
  | Tsum {name = s1; _}, Tsum {name = s2; _} ->
    Hstring.compare s1 s2
  | Tsum _, _ -> -1 | _ , Tsum _ -> 1
  | Trecord {args = a1; name = s1; lbs = l1; _},
    Trecord {args = a2; name = s2; lbs = l2; _} ->
    let c = Hstring.compare s1 s2 in
    if c <> 0 then c else
      let c = compare_list a1 a2 in
      if c <> 0 then c else
        let l1, l2 = List.map snd l1, List.map snd l2 in
        compare_list l1 l2
  | Trecord _, _ -> -1 | _ , Trecord _ -> 1
  | Tadt { cstr = s1; payload = p1}, Tadt { cstr = s2; payload = p2 } ->
    let c = Hstring.compare s1 s2 in
    if c <> 0 then c
    else compare_list p1 p2
  (* no need to compare bodies *)
  | Tadt _, _ -> -1 | _ , Tadt _ -> 1
  | t1, t2 -> Stdlib.compare t1 t2

and compare_list l1 l2 = match l1, l2 with
  | [] , [] -> 0
  | [] , _ -> -1
  | _ , [] -> 1
  | x::ll1 , y::ll2 ->
    let c = compare x y in
    if c<>0 then c else compare_list ll1 ll2

let rec equal t1 t2 =
  t1 == t2 ||
  match shorten t1, shorten t2 with
  | Tvar { v = v1; _ }, Tvar { v = v2; _ } -> v1 = v2
  | Text { cstr = s1; params = l1}, Text { cstr = s2; params = l2 } ->
    (try Hstring.equal s1 s2 && List.for_all2 equal l1 l2
     with Invalid_argument _ -> false)
  | Tfarray { key_ty = key_ty1; val_ty = val_ty1 },
    Tfarray { key_ty = key_ty2; val_ty = val_ty2 } ->
    equal key_ty1 key_ty2 && equal val_ty1 val_ty2
  | Tsum { name = s1; _ }, Tsum { name = s2; _ } -> Hstring.equal s1 s2
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
  | Tbitv n1, Tbitv n2 -> n1 = n2
  | Tadt { cstr = s1; payload = pars1 }, Tadt { cstr = s2; payload = pars2} ->
    begin
      try Hstring.equal s1 s2 && List.for_all2 equal pars1 pars2
      with Invalid_argument _ -> false
      (* no need to compare bodies *)
    end
  | _ -> false

(*** matching with a substitution mechanism ***)
module Subst = struct
  type ty = t
  type nonrec t = t Util.MI.t

  let empty = Util.MI.empty
  let is_empty = Util.MI.is_empty
  let add = Util.MI.add
  let remove = Util.MI.remove
  let mem = Util.MI.mem
  let filter = Util.MI.filter

  let compare = Util.MI.compare Stdlib.compare
  let equal = Util.MI.equal Stdlib.(=)

  let apply =
    let rec apply s ty =
      match ty with
      | Tvar {v = n; _} ->
        begin
          try Util.MI.find n s with Not_found -> ty
        end
      | Text { cstr; params } ->
        let params, same = Lists.apply (apply s) params in
        if same then ty else Text { cstr; params }
      | Tfarray {key_ty; val_ty} ->
        begin
          let key_ty' = apply s key_ty in
          let val_ty' = apply s val_ty in
          if key_ty == key_ty' && val_ty == val_ty' then ty
          else Tfarray {key_ty = key_ty'; val_ty = val_ty'}
        end
      | Trecord r ->
        let lbs,  same1 = Lists.apply_right (apply s) r.lbs in
        let args, same2 = Lists.apply (apply s) r.args in
        if same1 && same2 then ty
        else
          Trecord {r with args; name = r.name; lbs}
      | Tadt { cstr; payload }
        [@ocaml.ppwarning "TODO: detect when there are no changes "]
        ->
        Tadt { cstr; payload = List.map (apply s) payload }
      | Tint | Treal | Tbool | Tunit | Tbitv _ | Tsum _ -> ty
    in
    fun s ty -> if Util.MI.is_empty s then ty else apply s ty

  let union s1 s2 =
    Util.MI.fold (fun k x s2 ->
        Util.MI.add k x s2
      ) (Util.MI.map (apply s2) s1) s2

  let print fmt sbt =
    Util.MI.iter (fun n ty -> Format.fprintf fmt "%d -> %a" n print ty) sbt;
    Format.fprintf fmt "@?"
end

let rec matching s pat t =
  match pat , t with
  | Tvar {v = n; value = None} , _ ->
    (try if not (equal (Util.MI.find n s) t) then raise (TypeClash(pat,t)); s
     with Not_found -> Util.MI.add n t s)
  | Tvar {value = _; _}, _ -> raise (Shorten pat)
  | Text {cstr = s1; params = l1},
    Text {cstr = s2; params = l2} when Hstring.equal s1 s2 ->
    List.fold_left2 matching s l1 l2
  | Tfarray {key_ty = key_ty1; val_ty = val_ty1},
    Tfarray {key_ty = key_ty2; val_ty = val_ty2} ->
    matching (matching s key_ty1 key_ty2) val_ty1 val_ty2
  | Trecord r1, Trecord r2 when Hstring.equal r1.name r2.name ->
    let s = List.fold_left2 matching s r1.args r2.args in
    List.fold_left2
      (fun s (_, p) (_, ty) -> matching s p ty) s r1.lbs r2.lbs
  | Tsum {name = s1; _}, Tsum {name = s2; _} when Hstring.equal s1 s2 -> s
  | Tint , Tint | Tbool , Tbool | Treal , Treal | Tunit, Tunit -> s
  | Tbitv n , Tbitv m when n=m -> s
  | Tadt {cstr = n1; payload = payload1},
    Tadt {cstr = n2; payload = payload2} when Hstring.equal n1 n2 ->
    List.fold_left2 matching s payload1 payload2
  | _ , _ ->
    raise (TypeClash(pat,t))

let rec fresh ty subst =
  match ty with
  | Tvar { v= x; _ } ->
    begin
      try Util.MI.find x subst, subst
      with Not_found ->
        let nv = Tvar (fresh_var()) in
        nv, Util.MI.add x nv subst
    end
  | Text {cstr; params} ->
    let params, subst = fresh_list params subst in
    Text {cstr; params}, subst
  | Tfarray {key_ty; val_ty} ->
    let key_ty, subst = fresh key_ty subst in
    let val_ty, subst = fresh val_ty subst in
    Tfarray {key_ty; val_ty}, subst
  | Trecord ({args; name; lbs; _} as r) ->
    let args, subst = fresh_list args subst in
    let lbs, subst =
      List.fold_right
        (fun (x, ty) (lbs, subst) ->
           let ty, subst = fresh ty subst in
           (x, ty)::lbs, subst) lbs ([], subst)
    in
    Trecord {r with  args; name; lbs}, subst
  | Tadt { cstr; payload } ->
    let payload, subst = fresh_list payload subst in
    Tadt { cstr; payload }, subst
  | t -> t, subst

and fresh_list lty subst =
  List.fold_right
    (fun ty (lty, subst) ->
       let ty, subst = fresh ty subst in
       ty::lty, subst) lty ([], subst)

module Decls = struct

  module MH = Hstring.Map

  module MTY = Map.Make(struct
      type nonrec t = t list
      let compare = compare_list
    end)

  type decl = {
    decl : t list * type_body;
    instances : type_body MTY.t
  }

  type decls = decl MH.t

  let (decls : decls ref) = ref MH.empty


  let fresh_type params body =
    let params, subst = fresh_list params Subst.empty in
    match body with
    | Adt cases ->
      let _subst, cases =
        List.fold_left
          (fun (subst, cases) { cstr; dstrs } ->
             let subst, dstrs =
               List.fold_left
                 (fun (subst, dstrs) (d, ty) ->
                    let ty, subst = fresh ty subst in
                    subst, (d, ty) :: dstrs
                 )(subst, []) (List.rev dstrs)
             in
             subst, { cstr; dstrs } :: cases
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
        MH.add name { decl = (params, body); instances = MTY.empty } !decls

  let body name args =
    try
      let { decl = (params, body); instances } = MH.find name !decls in
      try
        if compare_list params args = 0 then body
        else MTY.find args instances
      (* should I instantiate if not found ?? *)
      with Not_found ->
        let params, body = fresh_type params body in
        (*if true || get_debug_adt () then*)
        let sbt =
          try
            List.fold_left2
              (fun sbt vty ty ->
                 let vty = shorten vty in
                 match vty with
                 | Tvar { value = Some _; _ } -> assert false
                 | Tvar { v; value = None }   ->
                   if equal vty ty then sbt else Util.MI.add v ty sbt
                 | _ ->
                   Printer.print_err "vty = %a and ty = %a"
                     print vty print ty;
                   assert false
              ) Util.MI.empty params args
          with Invalid_argument _ -> assert false
        in
        let body = match body with
          | Adt cases ->
            Adt(
              List.map
                (fun { cstr; dstrs } -> {
                     cstr;
                     dstrs =
                       List.map (fun (d, ty) -> d, Subst.apply sbt ty) dstrs
                   }) cases
            )
        in
        let params = List.map (fun ty -> Subst.apply sbt ty) params in
        add name params body;
        body
    with Not_found ->
      Printer.print_err "%a not found" Hstring.print name;
      assert false

  let reinit () = decls := MH.empty

end

let type_body name args = Decls.body name args

(* smart constructors *)
let tunit = Text { cstr = Hstring.make "unit"; params = [] }

let[@inline always] text ~params cstr =
  Text { cstr = Hstring.make cstr; params }

let fresh_empty_text =
  let cpt = ref (-1) in
  fun () -> incr cpt; text ~params:[] ("'_c"^(string_of_int !cpt))

let[@inline always] tsum ~cstrs name =
  Tsum {
    name = Hstring.make name;
    cstrs = List.map Hstring.make cstrs
  }

let t_adt ?(body=None) ~payload cstr =
  let cstr = Hstring.make cstr in
  let ty = Tadt { cstr; payload } in
  begin match body with
    | None -> ()
    | Some [] -> assert false
    | Some ([_] as cases) ->
      if Options.get_debug_adt () then
        Printer.print_dbg ~module_name:"Ty"
          "should be registered as a record";
      let cases =
        List.map (fun (s, l) ->
            let l =
              List.map (fun (d, e) -> Hstring.make d, e) l
            in
            { cstr = Hstring.make s; dstrs = l }
          ) cases
      in
      Decls.add cstr payload (Adt cases)
    | Some cases ->
      let cases =
        List.map (fun (s, l) ->
            let l =
              List.map (fun (d, e) -> Hstring.make d, e) l
            in
            { cstr = Hstring.make s; dstrs = l }
          ) cases
      in
      Decls.add cstr payload (Adt cases)
  end;
  ty

let trecord ?(record_cstr="{") ~args ~fields name =
  let fields = List.map (fun (l, ty) -> Hstring.make l, ty) fields in
  let fields, record_cstr =
    if String.equal record_cstr "{" then
      List.sort (fun (l1, _) (l2, _) -> Hstring.compare l1 l2) fields,
      Format.sprintf "%s___%s" record_cstr name
    else fields, record_cstr
  in
  let record_cstr = Hstring.make record_cstr in
  Trecord { record_cstr; args; name = Hstring.make name; lbs = fields }

let rec hash t =
  match t with
  | Tvar { v; _ } -> v
  | Text { cstr = s; params = l } ->
    abs (List.fold_left (fun acc x-> acc*19 + hash x) (Hstring.hash s) l)
  | Tfarray { key_ty; val_ty } -> 19 * (hash key_ty) + 23 * (hash val_ty)
  | Trecord { args; name; lbs; _ } ->
    let h =
      List.fold_left (fun h ty -> 27 * h + hash ty) (Hstring.hash name) args
    in
    let h =
      List.fold_left
        (fun h (lb, ty) -> 23 * h + 19 * (Hstring.hash lb) + hash ty)
        (abs h) lbs
    in
    abs h
  | Tsum { name; _ } -> abs (Hstring.hash name) (*we do not hash constructors*)

  | Tadt { cstr; payload } ->
    let h =
      List.fold_left (fun h ty -> 31 * h + hash ty) (Hstring.hash cstr) payload
    in
    abs h

  | _ -> Hashtbl.hash t

let occurs { v = n; _ } t =
  let rec occursrec = function
    | Tvar { v = m; _ } -> n=m
    | Text { params; _ } -> List.exists occursrec params
    | Tfarray { key_ty; val_ty } -> occursrec key_ty || occursrec val_ty
    | Trecord { args; _ } | Tadt { payload = args; _ } ->
      List.exists occursrec args
    | Tsum _ | Tint | Treal | Tbool | Tunit | Tbitv _ -> false
  in occursrec t

(*** destructive unification ***)
let rec unify t1 t2 =
  let t1 = shorten t1 in
  let t2 = shorten t2 in
  match t1 , t2 with
    Tvar ({ v = n; value = None } as tv1), Tvar { v = m; value = None } ->
    if n<>m then tv1.value <- Some t2
  | _ ,  Tvar ({ value = None; _ } as tv) ->
    if (occurs tv t1) then raise (TypeClash(t1,t2));
    tv.value <- Some t1
  | Tvar ({ value = None; _ } as tv) , _ ->
    if (occurs tv t2) then raise (TypeClash(t1,t2));
    tv.value <- Some t2
  | Text { cstr = s1; params = l1 }, Text { cstr = s2; params = l2 }
    when Hstring.equal s1 s2 -> List.iter2 unify l1 l2
  | Tfarray { key_ty = key_ty1; val_ty = val_ty1 },
    Tfarray { key_ty = key_ty2; val_ty = val_ty2 } ->
    unify key_ty1 key_ty2; unify val_ty1 val_ty2
  | Trecord r1, Trecord r2 when Hstring.equal r1.name r2.name ->
    List.iter2 unify r1.args r2.args
  | Tsum { name = s1; _ }, Tsum { name = s2; _ } when Hstring.equal s1 s2 -> ()
  | Tint, Tint | Tbool, Tbool | Treal, Treal | Tunit, Tunit -> ()
  | Tbitv n , Tbitv m when m=n -> ()
  | Tadt { cstr = n1; payload = p1 }, Tadt { cstr = n2; payload = p2 }
    when Hstring.equal n1 n2 -> List.iter2 unify p1 p2
  | _ , _ [@ocaml.ppwarning "TODO: remove fragile pattern"] ->
    raise (TypeClash(t1,t2))

let instantiate lvar lty ty =
  let s =
    List.fold_left2
      (fun s x t ->
         match x with
         | Tvar { v = n; _ } ->
           Util.MI.add n t s
         | _ -> assert false) Util.MI.empty lvar lty
  in
  Subst.apply s ty

module Svty = Util.SI

module Set =
  Set.Make(struct
    type nonrec t = t
    let compare = compare
  end)

let vty_of t =
  let rec vty_of_rec acc t =
    let t = shorten t in
    match t with
    | Tvar { v = i; value = None } -> Svty.add i acc
    | Text { params; _ } -> List.fold_left vty_of_rec acc params
    | Tfarray { key_ty; val_ty } -> vty_of_rec (vty_of_rec acc key_ty) val_ty
    | Trecord { args; lbs; _ } ->
      let acc = List.fold_left vty_of_rec acc args in
      List.fold_left (fun acc (_, ty) -> vty_of_rec acc ty) acc lbs
    | Tadt { payload; _ } -> List.fold_left vty_of_rec acc payload
    | Tvar { value = Some _ ; _}
    | Tint | Treal | Tbool | Tunit | Tbitv _ | Tsum _ -> acc
  in
  vty_of_rec Svty.empty t


  [@ocaml.ppwarning "TODO: detect when there are no changes "]
let rec monomorphize ty =
  match ty with
  | Tint | Treal | Tbool | Tunit   | Tbitv _  | Tsum _ -> ty
  | Text { cstr; params } ->
    Text { cstr; params = List.map monomorphize params }
  | Trecord ({ args = tylv; name; lbs = tylb; _ } as r) ->
    let m_tylv = List.map monomorphize tylv in
    let m_tylb =
      List.map (fun (lb, ty_lb) -> lb, monomorphize ty_lb) tylb
    in
    Trecord { r with args = m_tylv; name; lbs = m_tylb }
  | Tfarray { key_ty; val_ty } ->
    Tfarray { key_ty = monomorphize key_ty; val_ty = monomorphize val_ty }
  | Tvar { v; value = None } -> text ~params:[] ("'_c"^(string_of_int v))
  | Tvar ({ value = Some ty1; _ } as r) ->
    Tvar { r with value = Some (monomorphize ty1) }
  | Tadt { cstr; payload } ->
    Tadt { cstr; payload = List.map monomorphize payload }

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
    | Thm -> "@H"^(string_of_int !cpt)
    | _ -> "@L"^(string_of_int !cpt)

let is_local_hyp s =
  try String.equal (String.sub s 0 2) "@L" with Invalid_argument _ -> false

let is_global_hyp s =
  try String.equal (String.sub s 0 2) "@H" with Invalid_argument _ -> false

(* Context reinitialization *)
let reinit_decls () = Decls.reinit ()
