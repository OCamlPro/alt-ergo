(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2018 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options

module ME = Expr.Map
module E = Expr
module Hs = Hstring



module type ATOM = sig

  type var =
    {  vid : int;
       pa : atom;
       na : atom;
       mutable weight : float;
       mutable sweight : int;
       mutable seen : bool;
       mutable level : int;
       mutable index : int;
       mutable reason: reason;
       mutable vpremise : premise}

  and atom =
    { var : var;
      lit : E.t;
      neg : atom;
      mutable watched : clause Vec.t;
      mutable is_true : bool;
      mutable timp : int;
      mutable is_guard : bool;
      aid : int }

  and clause =
    { name : string;
      mutable atoms : atom Vec.t ;
      mutable activity : float;
      mutable removed : bool;
      learnt : bool;
      cpremise : premise;
      form : E.t}

  and reason = clause option

  and premise = clause list

  type hcons_env

  val empty_hcons_env : unit -> hcons_env
  val copy_hcons_env : hcons_env -> hcons_env
  val nb_made_vars : hcons_env -> int

  val pr_atom : Format.formatter -> atom -> unit
  val pr_clause : Format.formatter -> clause -> unit
  val get_atom : hcons_env -> E.t ->  atom

  val literal : atom -> E.t
  val weight : atom -> float
  val is_true : atom -> bool
  val neg : atom -> atom
  val vrai_atom  : atom
  val faux_atom  : atom
  val level : atom -> int
  val index : atom -> int
  val reason : atom -> reason
  val reason_atoms : atom -> atom list

  val dummy_var : var
  val dummy_atom : atom
  val dummy_clause : clause

  val to_float : int -> float
  val to_int : float -> int

  val fresh_name : unit -> string

  val fresh_lname : unit -> string

  val fresh_dname : unit -> string

  val make_clause : string -> atom list -> E.t -> int -> bool ->
    premise-> clause

  (*val made_vars_info : unit -> int * var list*)

  val cmp_atom : atom -> atom -> int
  val eq_atom   : atom -> atom -> bool
  val hash_atom  : atom -> int
  val tag_atom   : atom -> int

  val add_atom : hcons_env -> E.t -> var list -> atom * var list

  module Set : Set.S with type elt = atom
  module Map : Map.S with type key = atom
end

(*

  (*module Make (Dummy : sig end) : sig*)

  val literal : atom -> E.t
  val weight : atom -> float
  val is_true : atom -> bool
  val level : atom -> int
  val index : atom -> int
  val neg : atom -> atom

  val cpt_mk_var : int ref
  val ma : var E.Map.t ref


  val make_var : E.t -> var * bool

  val get_atom : E.t -> atom (* get existing atom of a lit *)
  val vrai_atom  : atom
  val faux_atom  : atom

  val fresh_name : unit -> string

  val fresh_lname : unit -> string

  val fresh_dname : unit -> string


  val to_int : float -> int

  (****)


  val cmp_var : var -> var -> int
  val eq_var   : var -> var -> bool
  val h_var    : var -> int
  val tag_var  : var -> int

  val reason_atoms : atom -> atom list

  (*end*)

  val pr_atom : Format.formatter -> atom -> unit

  val pr_clause : Format.formatter -> clause -> unit

  val iter_atoms_of_clauses : clause Vec.t -> (atom -> unit) -> unit

*)

module Atom : ATOM = struct

  type var =
    {  vid : int;
       pa : atom;
       na : atom;
       mutable weight : float;
       mutable sweight : int;
       mutable seen : bool;
       mutable level : int;
       mutable index : int;
       mutable reason: reason;
       mutable vpremise : premise}

  and atom =
    { var : var;
      lit : E.t;
      neg : atom;
      mutable watched : clause Vec.t;
      mutable is_true : bool;
      mutable timp : int;
      mutable is_guard : bool;
      aid : int }

  and clause =
    { name : string;
      mutable atoms : atom Vec.t ;
      mutable activity : float;
      mutable removed : bool;
      learnt : bool;
      cpremise : premise;
      form : E.t}

  and reason = clause option

  and premise = clause list

  let dummy_lit = E.vrai

  let vraie_form = E.vrai

  let rec dummy_var =
    { vid = -101;
      pa = dummy_atom;
      na = dummy_atom;
      level = -1;
      index = -1;
      reason = None;
      weight = -1.;
      sweight = 0;
      seen = false;
      vpremise = [] }
  and dummy_atom =
    { var = dummy_var;
      timp = 0;
      lit = dummy_lit;
      watched = {Vec.dummy=dummy_clause; data=[||]; sz=0};
      neg = dummy_atom;
      is_true = false;
      is_guard = false;
      aid = -102 }
  and dummy_clause =
    { name = "";
      atoms = {Vec.dummy=dummy_atom; data=[||]; sz=0};
      activity = -1.;
      removed = false;
      learnt = false;
      cpremise = [];
      form = vraie_form }


  module Debug = struct

    let sign a = if a==a.var.pa then "" else "-"

    let level a =
      match a.var.level, a.var.reason with
      | n, _ when n < 0 -> assert false
      | 0, Some c -> sprintf "->0/%s" c.name
      | 0, None   -> "@0"
      | n, Some c -> sprintf "->%d/%s" n c.name
      | n, None   -> sprintf "@@%d" n

    let value a =
      if a.is_true then sprintf "[T%s]" (level a)
      else if a.neg.is_true then sprintf "[F%s]" (level a)
      else ""

    let premise fmt v =
      List.iter (fun { name = name; _ } -> fprintf fmt "%s," name) v

    let atom fmt a =
      fprintf fmt "%s%d%s [index=%d | lit:%a] vpremise={{%a}}"
        (sign a) (a.var.vid+1) (value a) a.var.index E.print a.lit
        premise a.var.vpremise


    let atoms_vec fmt vec =
      for i = 0 to Vec.size vec - 1 do
        fprintf fmt "%a ; " atom (Vec.get vec i)
      done

    let clause fmt { name; atoms=arr; cpremise=cp; _ } =
      fprintf fmt "%s:{ %a} cpremise={{%a}}" name atoms_vec arr premise cp

  end

  let pr_atom = Debug.atom
  let pr_clause = Debug.clause

  let normal_form lit = (* XXX do better *)
    let is_pos = E.is_positive lit in
    (if is_pos then lit else E.neg lit), not is_pos

  let max_depth a = E.depth a

  let literal a = a.lit
  let weight a = a.var.weight

  let is_true a = a.is_true
  let level a = a.var.level
  let index a = a.var.index
  let neg a = a.neg

  module HT = Hashtbl.Make(E)

  type hcons_env = { tbl : var HT.t ; cpt : int ref }

  let make_var =
    fun hcons lit acc ->
    let lit, negated = normal_form lit in
    try HT.find hcons.tbl lit, negated, acc
    with Not_found ->
      let cpt = !(hcons.cpt) in
      let cpt_fois_2 = cpt * 2 in
      let rec var  =
        { vid = cpt;
          pa = pa;
          na = na;
          level = -1;
          index = -1;
          reason = None;
          weight = 0.;
          sweight = max_depth lit;
          seen = false;
          vpremise = [];
        }
      and pa =
        { var = var;
          lit = lit;
          watched = Vec.make 10 dummy_clause;
          neg = na;
          is_true = false;
          is_guard = false;
          timp = 0;
          aid = cpt_fois_2 (* aid = vid*2 *) }
      and na =
        { var = var;
          lit = E.neg lit;
          watched = Vec.make 10 dummy_clause;
          neg = pa;
          is_true = false;
          is_guard = false;
          timp = 0;
          aid = cpt_fois_2 + 1 (* aid = vid*2+1 *) } in
      HT.add hcons.tbl lit var;
      incr hcons.cpt;
      var, negated, var :: acc

  let add_atom hcons lit acc =
    let var, negated, acc = make_var hcons lit acc in
    (if negated then var.na else var.pa), acc

  (* with this code, all envs created with empty_hcons_env () will be
     initialized with the good reference to "vrai" *)
  let copy_hcons_env hcons =
    { tbl = HT.copy hcons.tbl ; cpt = ref !(hcons.cpt) }

  let empty_hcons_env, vrai_atom =
    let empty_hcons = { tbl= HT.create 5048 ; cpt = ref (-1) } in
    let a, _ = add_atom empty_hcons E.vrai [] in
    a.is_true <- true;
    a.var.level <- 0;
    a.var.reason <- None;
    let f_empty_hashcons () = copy_hcons_env empty_hcons in
    f_empty_hashcons, a

  let faux_atom = vrai_atom.neg

  let nb_made_vars hcons = !(hcons.cpt)

  let get_atom hcons lit =
    try (HT.find hcons.tbl lit).pa
    with Not_found ->
    try (HT.find hcons.tbl (E.neg lit)).na
    with Not_found -> assert false

  let make_clause name ali f sz_ali is_learnt premise =
    let atoms = Vec.from_list ali sz_ali dummy_atom in
    { name  = name;
      atoms = atoms;
      removed = false;
      learnt = is_learnt;
      activity = 0.;
      cpremise = premise;
      form = f}

  let fresh_lname =
    let cpt = ref 0 in
    fun () -> incr cpt; "L" ^ (string_of_int !cpt)

  let fresh_dname =
    let cpt = ref 0 in
    fun () -> incr cpt; "D" ^ (string_of_int !cpt)

  let fresh_name =
    let cpt = ref 0 in
    fun () -> incr cpt; "C" ^ (string_of_int !cpt)


  let to_float i = float_of_int i

  let to_int f = int_of_float f

  (* unused --
     let cmp_var v1 v2 = v1.vid - v2.vid
     let eq_var v1 v2 = v1.vid - v2.vid = 0
     let tag_var v = v.vid
     let h_var v = v.vid
  *)

  let cmp_atom a1 a2 = a1.aid - a2.aid
  let eq_atom   a1 a2 = a1.aid - a2.aid = 0
  let hash_atom a1 = a1.aid
  let tag_atom  a1 = a1.aid

  let reason a =
    a.var.reason

  let reason_atoms a =
    match a.var.reason with
      None -> []
    | Some c ->
      let cpt = ref 0 in
      let l = ref [] in
      for i = 0 to Vec.size c.atoms - 1 do
        let b = Vec.get c.atoms i in
        if eq_atom a b then incr cpt
        else l := b :: !l
      done;
      if !cpt <> 1 then begin
        Printer.print_err
          "cpt = %d@ a = %a@ c = %a"
          !cpt pr_atom a pr_clause c;
        assert false
      end;
      !l

  module Set = Set.Make(struct type t=atom let compare=cmp_atom end)
  module Map = Map.Make(struct type t=atom let compare=cmp_atom end)

end

(******************************************************************************)

module type FLAT_FORMULA = sig
  type t
  type view = private UNIT of Atom.atom | AND of t list | OR of t list
  type hcons_env

  val equal   : t -> t -> bool
  val compare : t -> t -> int
  val print   : Format.formatter -> t -> unit
  val print_stats : Format.formatter -> unit
  val vrai    : t
  val faux    : t
  val view    : t -> view
  val mk_lit  : hcons_env -> E.t -> Atom.var list -> t * Atom.var list
  val mk_and  : hcons_env -> t list -> t
  val mk_or   : hcons_env -> t list -> t
  val mk_not  : t -> t

  val empty_hcons_env : unit -> hcons_env
  val nb_made_vars : hcons_env -> int
  val get_atom : hcons_env -> E.t -> Atom.atom

  val simplify :
    hcons_env ->
    E.t ->
    (E.t -> t * 'a) ->
    Atom.var list ->
    t * (E.t * (t * Atom.atom)) list
    * Atom.var list

  val get_proxy_of : t ->
    (Atom.atom * Atom.atom list * bool) Util.MI.t -> Atom.atom option

  val cnf_abstr :
    hcons_env ->
    t ->
    (Atom.atom * Atom.atom list * bool) Util.MI.t ->
    Atom.var list ->
    Atom.atom
    * (Atom.atom * Atom.atom list * bool) list
    * (Atom.atom * Atom.atom list * bool) Util.MI.t
    * Atom.var list

  val expand_proxy_defn :
    Atom.atom list list ->
    Atom.atom * Atom.atom list * bool -> Atom.atom list list

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

module Flat_Formula : FLAT_FORMULA = struct

  type view = UNIT of Atom.atom | AND  of t list | OR of t list
  and t =
    {view : view;
     tag : int;
     neg : t
    }

  let mk_not f = f.neg

  let cpt = ref 0

  let sp() = let s = ref "" in for _ = 1 to !cpt do s := " " ^ !s done; !s ^ !s

  let rec print fmt fa = match fa.view with
    | UNIT a -> fprintf fmt "%a" Atom.pr_atom a
    | AND s  ->
      incr cpt;
      fprintf fmt "(and%a" print_list s;
      decr cpt;
      fprintf fmt "@.%s)" (sp())

    | OR s   ->
      incr cpt;
      fprintf fmt "(or%a" print_list s;
      decr cpt;
      fprintf fmt "@.%s)" (sp())

  and print_list fmt l =
    match l with
    | [] -> assert false
    | e::l ->
      fprintf fmt "@.%s%a" (sp()) print e;
      List.iter(fprintf fmt "@.%s%a" (sp()) print) l


  let print fmt f = cpt := 0; print fmt f

  let print_stats _ = ()

  let compare f1 f2 = f1.tag - f2.tag

  let equal f1 f2 = f1.tag == f2.tag
  (* unused -- let hash f = f.tag *)
  (* unused -- let tag  f = f.tag *)
  let view f = f.view

  let is_positive pos = match pos with
    | AND _ -> true
    | OR  _ -> false
    | UNIT at -> at == at.Atom.var.Atom.pa

  module HT =
    Hashtbl.Make
      (struct
        type nonrec t = t

        let hash f =
          let h_aux f = match f with
            | UNIT a -> Atom.hash_atom a
            | AND l  -> List.fold_left (fun acc f -> acc * 19 + f.tag) 1 l
            | OR l   -> List.fold_left (fun acc f -> acc * 23 + f.tag) 1 l
          in
          let h = h_aux f.view in
          match f.view with
          | UNIT _ -> abs (3 * h)
          | AND _  -> abs (3 * h + 1)
          | OR _   -> abs (3 * h + 2)

        let equal f1 f2 =
          let eq_aux c1 c2 = match c1, c2 with
            | UNIT x , UNIT y -> Atom.eq_atom x y
            | AND u  , AND v | OR u , OR v  ->
              (try
                 List.iter2
                   (fun x y -> if x.tag <> y.tag then raise Exit) u v; true
               with
               | Exit -> false
               | Invalid_argument s ->
                 assert (String.compare s "List.iter2" = 0);
                 false)

            | _, _ -> false
          in
          eq_aux f1.view f2.view
      end)

  type hcons_env = { tbl : t HT.t ; cpt : int ref ;
                     atoms : Atom.hcons_env}

  let make hcons pos neg =
    let is_pos = is_positive pos in
    let pos, neg = if is_pos then pos, neg else neg, pos in
    let rec p =
      {
        view = pos;
        tag  = 2 * !(hcons.cpt);
        neg  = n;
      }
    and n =
      {
        view = neg;
        tag  = 2 * !(hcons.cpt) + 1;
        neg  = p;
      }
    in
    let res =
      try HT.find hcons.tbl p
      with Not_found ->
        incr hcons.cpt;
        HT.add hcons.tbl p p;
        p
    in
    if is_pos then res else mk_not res

  let aaz a = assert (a.Atom.var.Atom.level = 0)

  let complements f1 f2 = f1.tag == f2.neg.tag

  let mk_lit hcons a acc =
    let at, acc = Atom.add_atom hcons.atoms a acc in
    let at =
      if get_disable_flat_formulas_simplification () then at
      else
      if at.Atom.var.Atom.level = 0 then
        if at.Atom.is_true then Atom.vrai_atom
        else begin
          if at.Atom.neg.Atom.is_true then Atom.faux_atom else at
        end
      else at
    in
    make hcons (UNIT at) (UNIT at.Atom.neg), acc

  (* with this code, all envs created with empty_hcons_env () will be
     initialized with the good reference to "vrai" *)
  let empty_hcons_env, vrai =
    let empty_hcons =
      { tbl = HT.create 4096 ;
        cpt = ref 0 ;
        atoms = Atom.empty_hcons_env () }
    in
    let vrai = mk_lit empty_hcons E.vrai [] |> fst in
    let f_empty_hcons () =
      { tbl = HT.copy empty_hcons.tbl ;
        cpt = ref !(empty_hcons.cpt) ;
        atoms = Atom.copy_hcons_env empty_hcons.atoms }
    in
    f_empty_hcons, vrai

  let faux = mk_not vrai

  let nb_made_vars hcons = Atom.nb_made_vars hcons.atoms

  let merge_and_check l1 l2 =
    let rec merge_rec l1 l2 hd =
      match l1, l2 with
      | [], l2 -> l2
      | l1, [] -> l1
      | h1 :: t1, h2 :: t2 ->
        let c = compare h1 h2 in
        if c = 0 then merge_rec l1 t2 hd
        else
        if compare h1 h2 < 0
        then begin
          if complements hd h1 then raise Exit;
          h1 :: merge_rec t1 l2 h1
        end
        else begin
          if complements hd h2 then raise Exit;
          h2 :: merge_rec l1 t2 h2
        end
    in
    match l1, l2 with
    | [], l2 -> l2
    | l1, [] -> l1
    | h1 :: t1, h2 :: _ ->
      let c = compare h1 h2 in
      if c = 0 then merge_rec t1 l2 h1
      else
      if compare h1 h2 < 0
      then merge_rec l1 l2 h1
      else merge_rec l1 l2 h2

  let mk_and hcons l =
    try
      let so, nso =
        List.fold_left
          (fun ((so,nso) as acc) e ->
             match e.view with
             | AND l -> merge_and_check so l, nso
             | UNIT a when
                 not (get_disable_flat_formulas_simplification ()) &&
                 a.Atom.var.Atom.level = 0 ->
               begin
                 if a.Atom.neg.Atom.is_true then (aaz a; raise Exit); (* XXX*)
                 if a.Atom.is_true then (aaz a; acc)
                 else so, e::nso
               end
             | _     -> so, e::nso
          )([],[]) l
      in
      let delta_inv = List.fast_sort (fun a b -> compare b a) nso in
      let delta_u = match delta_inv with
        | [] -> delta_inv
        | e::l ->
          let _, delta_u =
            List.fold_left
              (fun ((c,l) as acc) e ->
                 if complements c e then raise Exit;
                 if equal c e then acc
                 else (e, e::l)
              )(e,[e]) l
          in
          delta_u
      in
      match merge_and_check so delta_u with
      | [] -> vrai
      | [e]-> e
      | l -> make hcons (AND l) (OR (List.rev (List.rev_map mk_not l)))
    with Exit -> faux

  (* res = l1 inter l2 *)
  let intersect_list l1 l2 =
    let rec inter l1 l2 acc =
      match l1, l2 with
      | [], _ | _ , [] -> List.rev acc
      | f1::r1, f2::r2 ->
        let c = compare f1 f2 in
        if c = 0 then inter r1 r2 (f1::acc)
        else if c > 0 then inter l1 r2 acc else inter r1 l2 acc
    in
    inter l1 l2 []

  exception Not_included

  let remove_elt e l =
    let rec relt l acc =
      match l with
      | [] -> raise Not_included
      | f::r ->
        let c = compare f e in
        if c = 0 then List.rev_append acc r
        else if c < 0 then relt r (f::acc)
        else raise Not_included
    in
    relt l []

  let diff_list to_exclude l =
    let rec diff l1 l2 acc =
      match l1, l2 with
      | [], [] -> List.rev acc
      | [], r  -> List.rev_append acc r
      | _ , [] -> raise Not_included
      | f1::r1, f2::r2 ->
        let c = compare f1 f2 in
        if c = 0 then diff r1 r2 acc
        else if c > 0 then diff l1 r2 (f2::acc)
        else raise Not_included
    in
    diff to_exclude l []

  let extract_common l =
    let atoms, ands =
      List.fold_left
        (fun (atoms, ands) f ->
           match view f with
           | OR _   -> assert false
           | UNIT _ -> f::atoms, ands
           | AND l  -> atoms, l::ands
        )([],[]) l
    in
    match atoms, ands with
    | [], [] -> assert false

    | _::_::_, _ ->
      if get_debug_sat () then
        Printer.print_dbg
          ~module_name:"Satml_types" ~function_name:"extract_common"
          "Failure: many distinct atoms";
      None

    | [_] as common, _ ->
      if get_debug_sat () then
        Printer.print_dbg
          ~module_name:"Satml_types" ~function_name:"extract_common"
          "TODO: Should have one toplevel common atom";
      begin
        try
          (*  a + (a . B_1) + ... (a . B_n) = a *)
          ignore (List.rev_map (diff_list common) ands);
          Some (common, [[]])
        with Not_included -> None
      end

    | [], ad::ands' ->
      if get_debug_sat () then
        Printer.print_dbg
          ~module_name:"Satml_types" ~function_name:"extract_common"
          "Should look for internal common parts";
      let common = List.fold_left intersect_list ad ands' in
      match common with
        [] -> None
      | _ ->
        try Some (common, List.rev_map (diff_list common) ands)
        with Not_included -> assert false

  let rec mk_or hcons l =
    try
      let so, nso =
        List.fold_left
          (fun ((so,nso) as acc) e ->
             match e.view with
             | OR l  -> merge_and_check so l, nso
             | UNIT a  when
                 not (get_disable_flat_formulas_simplification ()) &&
                 a.Atom.var.Atom.level = 0 ->
               begin
                 if a.Atom.is_true then (aaz a; raise Exit); (* XXX *)
                 if a.Atom.neg.Atom.is_true then (aaz a; acc)
                 else so, e::nso
               end
             | _     -> so, e::nso
          )([],[]) l
      in
      let delta_inv = List.fast_sort (fun a b -> compare b a) nso in
      let delta_u = match delta_inv with
        | [] -> delta_inv
        | e::l ->
          let _, delta_u =
            List.fold_left
              (fun ((c,l) as acc) e ->
                 if complements c e then raise Exit;
                 if equal c e then acc
                 else (e, e::l)
              )(e,[e]) l
          in
          delta_u
      in
      match merge_and_check so delta_u with
      | [] -> faux
      | [e]-> e
      | l  ->
        match extract_common l with
        | None ->
          begin match l with
            | [{ view = UNIT _; _ } as fa; { view = AND ands; _ }] ->
              begin
                try
                  mk_or hcons
                    [fa ; (mk_and hcons (remove_elt (mk_not fa) ands))]
                with Not_included ->
                  make hcons (OR l) (AND (List.rev (List.rev_map mk_not l)))
              end
            | _ ->
              make hcons (OR l) (AND (List.rev (List.rev_map mk_not l)))
          end
        | Some (com,ands) ->
          let ands = List.rev_map (mk_and hcons) ands in
          mk_and hcons ((mk_or hcons ands) :: com)
    with Exit -> vrai

  (* translation from E.t *)

  let abstract_lemma hcons abstr (f: E.t) tl lem new_vars =
    try fst (abstr f)
    with Not_found ->
    try fst (snd (List.find (fun (x,_) -> E.equal f x) !lem))
    with Not_found ->
      if tl then begin
        lem := (f, (vrai, Atom.vrai_atom)) :: !lem;
        vrai
      end
      else
        let lit = E.fresh_name Ty.Tbool in
        let xlit, new_v = mk_lit hcons lit !new_vars in
        let at_lit, new_v = Atom.add_atom hcons.atoms lit new_v in
        new_vars := new_v;
        lem := (f, (xlit, at_lit)) :: !lem
               [@ocaml.ppwarning "xlit or at_lit is probably redundant"]
        ;
        xlit

  let simplify hcons f abstr new_vars =
    let lem = ref [] in
    let new_vars = ref new_vars in
    let rec simp topl ~parent_disj f =
      match E.form_view f with
      | E.Not_a_form -> assert false
      | E.Literal a ->
        let ff, l = mk_lit hcons a !new_vars in
        new_vars := l;
        ff

      | E.Lemma _   -> abstract_lemma hcons abstr f topl lem new_vars

      | E.Skolem _ ->
        mk_not (simp false ~parent_disj:false (E.neg f))

      | E.Unit(f1, f2) ->
        let x1 = simp topl ~parent_disj:false f1 in
        let x2 = simp topl ~parent_disj:false f2 in
        begin match x1.view , x2.view with
          | AND l1, AND l2 -> mk_and hcons (List.rev_append l1 l2)
          | AND l1, _      -> mk_and hcons (x2 :: l1)
          | _     , AND l2 -> mk_and hcons (x1 :: l2)
          | _              -> mk_and hcons [x1; x2]
        end

      | E.Clause(f1, f2, _) ->
        let x1 = simp false ~parent_disj:true f1 in
        let x2 = simp false ~parent_disj:true f2 in
        begin match x1.view, x2.view with
          | OR l1, OR l2 -> mk_or hcons (List.rev_append l1 l2)
          | OR l1, _     -> mk_or hcons (x2 :: l1)
          | _    , OR l2 -> mk_or hcons (x1 :: l2)
          | _            -> mk_or hcons [x1; x2]
        end

      | E.Iff(f1, f2) ->
        simp topl ~parent_disj @@
        E.elim_iff f1 f2 (E.id f) ~with_conj:(not parent_disj)

      | E.Xor(f1, f2) ->
        let g = E.neg @@ E.elim_iff f1 f2 (E.id f) ~with_conj:parent_disj in
        simp topl ~parent_disj g

      | E.Let letin ->
        simp false ~parent_disj:false (E.elim_let ~recursive:true letin)
    in
    let res = simp true ~parent_disj:false f in
    res, !lem, !new_vars

  (* CNF_ABSTR a la Tseitin *)

  let atom_of_lit hcons lit is_neg new_vars =
    let a, l = Atom.add_atom hcons.atoms lit new_vars in
    if is_neg then a.Atom.neg,l else a,l

  let mk_new_proxy n =
    let hs = Hs.make ("PROXY__" ^ (string_of_int n)) in
    let sy = Symbols.Name(hs, Symbols.Other) in
    E.mk_term sy [] Ty.Tbool

  let get_proxy_of f proxies_mp =
    try let p, _, _ = Util.MI.find f.tag proxies_mp in Some p
    with Not_found ->
    try let p, _, _ = Util.MI.find f.neg.tag proxies_mp in Some p.Atom.neg
    with Not_found -> None


  let expand_proxy_defn acc (p, l, is_and) =
    if is_and then (* p <=> (l1 and ... and l_n) *)
      let np = p.Atom.neg in
      let cl, acc =
        List.fold_left
          (fun (cl,acc) a -> (a.Atom.neg :: cl), [np; a] :: acc)([p],acc) l
      in
      cl :: acc
    else (* p <=> (l1 or ... or l_n) *)
      let acc = List.fold_left (fun acc a -> [p;a.Atom.neg]::acc) acc l in
      ((p.Atom.neg) :: l) :: acc

  let cnf_abstr hcons f proxies_mp new_vars =
    let rec abstr f new_proxies proxies_mp new_vars =
      match f.view with
      | UNIT a -> a, new_proxies, proxies_mp, new_vars
      | AND l | OR l ->
        match get_proxy_of f proxies_mp with
        | Some p -> p, new_proxies, proxies_mp, new_vars
        | None ->
          let l, new_proxies, proxies_mp, new_vars =
            List.fold_left (fun (l,new_proxies,proxies_mp,new_vars) f ->
                let f, new_proxies, proxies_mp, new_vars =
                  abstr f new_proxies proxies_mp new_vars in
                f :: l, new_proxies, proxies_mp, new_vars
              ) ([],new_proxies,proxies_mp,new_vars) l in
          let l = List.rev l in
          let p,new_vars =
            atom_of_lit hcons (mk_new_proxy f.tag) false new_vars in
          let is_and = match f.view with
            | AND _ -> true | OR _ -> false | UNIT _ -> assert false
          in
          let new_proxies = (p, l, is_and) :: new_proxies in
          let proxies_mp = Util.MI.add f.tag (p, l, is_and) proxies_mp in
          p, new_proxies, proxies_mp, new_vars
    in
    abstr f [] proxies_mp new_vars

  let get_atom hcons a = Atom.get_atom hcons.atoms a

  module Set = Set.Make(struct type t'=t type t=t' let compare=compare end)
  module Map = Map.Make(struct type t'=t type t=t' let compare=compare end)

end

module Proxy_formula = struct
  let get_proxy_of f proxies =
    try Some (ME.find f proxies)
    with Not_found -> None

  let atom_of_lit hcons lit is_neg new_vars =
    let a, l = Atom.add_atom hcons lit new_vars in
    if is_neg then a.Atom.neg,l else a,l

  let mk_new_proxy n =
    let sy = Symbols.name @@ "PROXY__" ^ (string_of_int n) in
    E.mk_term sy [] Ty.Tbool

  let rec mk_cnf hcons f ((proxies, inv_proxies, new_vars, cnf) as accu) =
    match get_proxy_of f proxies with
    | Some p -> p, accu
    | None ->
      let nf = E.neg f in
      match get_proxy_of nf proxies with (* maybe redundant *)
      | Some p -> Atom.neg p, accu
      | None ->
        let a, new_vars =
          atom_of_lit hcons (mk_new_proxy (E.hash f)) false new_vars in
        let na = Atom.neg a in
        let proxies = ME.add f a proxies in
        let proxies = ME.add nf na proxies in
        let inv_proxies =  Atom.Map.add a f inv_proxies in
        let inv_proxies =  Atom.Map.add na nf inv_proxies in
        match E.form_view f with
        | E.Unit (f1,f2) ->
          let accu = (proxies, inv_proxies, new_vars, cnf) in
          let a1, accu = mk_cnf hcons f1 accu in
          let a2, (proxies, inv_proxies, new_vars, cnf) =
            mk_cnf hcons f2 accu in
          let cnf =
            [na; a1] :: [na; a2] :: [a; Atom.neg a1; Atom.neg a2] :: cnf in
          a, (proxies, inv_proxies, new_vars, cnf)

        | E.Clause (f1, f2, _) ->
          let accu = (proxies, inv_proxies, new_vars, cnf) in
          let a1, accu = mk_cnf hcons f1 accu in
          let a2, (proxies, inv_proxies, new_vars, cnf) =
            mk_cnf hcons f2 accu in
          let cnf =
            [a; Atom.neg a1] :: [a; Atom.neg a2] :: [na; a1; a2] :: cnf in
          a,  (proxies, inv_proxies, new_vars, cnf)

        | E.Let _ | E.Skolem _ | E.Lemma _ | E.Literal _ | E.Iff _
        | E.Xor _ ->
          a, (proxies, inv_proxies, new_vars, cnf)

        | E.Not_a_form -> assert false
end
