(******************************************************************************)
(*                                                                            *)
(*     Alt-Ergo: The SMT Solver For Software Verification                     *)
(*     Copyright (C) 2013-2017 --- OCamlPro SAS                               *)
(*                                                                            *)
(*     This file is distributed under the terms of the license indicated      *)
(*     in the file 'License.OCamlPro'. If 'License.OCamlPro' is not           *)
(*     present, please contact us to clarify licensing.                       *)
(*                                                                            *)
(******************************************************************************)

open Format
open Options

module F = Formula
module A = Literal.LT
module T = Term
module Hs = Hstring

module Iheap : sig

  type t

  val init : int -> t
  val in_heap : t -> int -> bool
  val decrease : (int -> int -> bool) -> t -> int -> unit
(*val increase : (int -> int -> bool) -> t -> int -> unit*)
  val size : t -> int
  val is_empty : t -> bool
  val insert : (int -> int -> bool) -> t -> int -> unit
  val grow_to_by_double: t -> int -> unit
(*val update : (int -> int -> bool) -> t -> int -> unit*)
  val remove_min : (int -> int -> bool) -> t -> int
  val filter : t -> (int -> bool) -> (int -> int -> bool) -> unit

end = struct
  type t = {heap : int Vec.t; indices : int Vec.t }

  let dummy = -100

  let init sz =
    { heap    =  Vec.init sz (fun i -> i) dummy;
      indices =  Vec.init sz (fun i -> i) dummy}

  let left i   = (i lsl 1) + 1 (* i*2 + 1 *)
  let right i  = (i + 1) lsl 1 (* (i+1)*2 *)
  let parent i = (i - 1) asr 1 (* (i-1) / 2 *)

(*
  let rec heap_property cmp ({heap=heap} as s) i =
  i >= (Vec.size heap)  ||
  ((i = 0 || not(cmp (Vec. get heap i) (Vec.get heap (parent i))))
  && heap_property cmp s (left i) && heap_property cmp s (right i))

  let heap_property cmp s = heap_property cmp s 1
*)

  let percolate_up cmp {heap=heap;indices=indices} i =
    let x = Vec.get heap i in
    let pi = ref (parent i) in
    let i = ref i in
    while !i <> 0 && cmp x (Vec.get heap !pi) do
      Vec.set heap !i (Vec.get heap !pi);
      Vec.set indices (Vec.get heap !i) !i;
      i  := !pi;
      pi := parent !i
    done;
    Vec.set heap !i x;
    Vec.set indices x !i

  let percolate_down cmp {heap=heap;indices=indices} i =
    let x = Vec.get heap i in
    let sz = Vec.size heap in
    let li = ref (left i) in
    let ri = ref (right i) in
    let i = ref i in
    (try
       while !li < sz do
         let child =
           if !ri < sz && cmp (Vec.get heap !ri) (Vec.get heap !li) then !ri
           else !li
         in
         if not (cmp (Vec.get heap child) x) then raise Exit;
         Vec.set heap !i (Vec.get heap child);
         Vec.set indices (Vec.get heap !i) !i;
         i  := child;
         li := left !i;
         ri := right !i
       done;
     with Exit -> ());
    Vec.set heap !i x;
    Vec.set indices x !i

  let in_heap s n =
    try n < Vec.size s.indices && Vec.get s.indices n >= 0
    with Not_found -> false

  let decrease cmp s n =
    assert (in_heap s n); percolate_up cmp s (Vec.get s.indices n)

  let increase cmp s n =
    assert (in_heap s n); percolate_down cmp s (Vec.get s.indices n)

  let filter s filt cmp =
    let j = ref 0 in
    let lim = Vec.size s.heap in
    for i = 0 to lim - 1 do
      if filt (Vec.get s.heap i) then begin
        Vec.set s.heap !j (Vec.get s.heap i);
        Vec.set s.indices (Vec.get s.heap i) !j;
        incr j;
      end
      else Vec.set s.indices (Vec.get s.heap i) (-1);
    done;
    Vec.shrink s.heap (lim - !j) true;
    for i = (lim / 2) - 1 downto 0 do
      percolate_down cmp s i
    done

  let size s = Vec.size s.heap

  let is_empty s = Vec.is_empty s.heap

  let insert cmp s n =
    if not (in_heap s n) then
      begin
        Vec.set s.indices n (Vec.size s.heap);
        Vec.push s.heap n;
        percolate_up cmp s (Vec.get s.indices n)
      end

  let grow_to_by_double s sz =
    Vec.grow_to_by_double s.indices sz;
    Vec.grow_to_by_double s.heap sz

(*
  let update cmp s n =
  assert (heap_property cmp s);
  begin
  if in_heap s n then
  begin
  percolate_up cmp s (Vec.get s.indices n);
  percolate_down cmp s (Vec.get s.indices n)
  end
  else insert cmp s n
  end;
  assert (heap_property cmp s)
*)

  let remove_min cmp ({heap=heap; indices=indices} as s) =
    let x = Vec.get heap 0 in
    Vec.set heap 0 (Vec.last heap); (*heap.last()*)
    Vec.set indices (Vec.get heap 0) 0;
    Vec.set indices x (-1);
    Vec.pop s.heap;
    if Vec.size s.heap > 1 then percolate_down cmp s 0;
    x

end

module type STT = sig
  type var =
      { vid : int;
        pa : atom;
        na : atom;
        mutable weight : float;
        mutable sweight : int;
        mutable seen : bool;
        mutable level : int;
        mutable index : int;
        mutable reason : reason;
        mutable vpremise : premise }

  and atom =
      { var : var;
        lit : Literal.LT.t;
        neg : atom;
        mutable watched : clause Vec.t;
        mutable is_true : bool;
        mutable timp : bool;
        aid : int }

  and clause =
      { name : string;
        mutable atoms : atom Vec.t;
        mutable activity : float;
        mutable removed : bool;
        learnt : bool;
        cpremise : premise;
        form : Formula.t}

  and reason = clause option

  and premise = clause list

  (*module Make (Dummy : sig end) : sig*)

  val literal : atom -> Literal.LT.t
  val weight : atom -> float
  val is_true : atom -> bool
  val level : atom -> int
  val index : atom -> int
  val neg : atom -> atom

  val cpt_mk_var : int ref
  val ma : var Literal.LT.Map.t ref

  val dummy_var : var
  val dummy_atom : atom
  val dummy_clause : clause

  val make_var : Literal.LT.t -> var * bool

  val add_atom : Literal.LT.t -> atom
  val get_atom : Literal.LT.t -> atom (* get existing atom of a lit *)
  val vrai_atom  : atom
  val faux_atom  : atom

  val make_clause : string -> atom list -> Formula.t -> int -> bool ->
    premise-> clause

  val fresh_name : unit -> string

  val fresh_lname : unit -> string

  val fresh_dname : unit -> string

  val to_float : int -> float

  val to_int : float -> int
  val made_vars_info : unit -> int * var list
  val clear : unit -> unit

  (****)

  val cmp_atom : atom -> atom -> int
  val eq_atom   : atom -> atom -> bool
  val hash_atom  : atom -> int
  val tag_atom   : atom -> int

  val cmp_var : var -> var -> int
  val eq_var   : var -> var -> bool
  val h_var    : var -> int
  val tag_var  : var -> int

  (*end*)

  val pr_atom : Format.formatter -> atom -> unit

  val pr_clause : Format.formatter -> clause -> unit

  val iter_atoms_of_clauses : clause Vec.t -> (atom -> unit) -> unit
end
module Types (*: STT*) = struct

  let ale = Hstring.make "<="
  let alt = Hstring.make "<"
  let agt = Hstring.make ">"

  let is_le n = Hstring.compare n ale = 0
  let is_lt n = Hstring.compare n alt = 0
  let is_gt n = Hstring.compare n agt = 0


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
        lit : Literal.LT.t;
        neg : atom;
        mutable watched : clause Vec.t;
        mutable is_true : bool;
        mutable timp : bool;
        aid : int }

  and clause =
      { name : string;
        mutable atoms : atom Vec.t ;
        mutable activity : float;
        mutable removed : bool;
        learnt : bool;
        cpremise : premise;
        form : Formula.t}

  and reason = clause option

  and premise = clause list

  (*module Make (Dummy : sig end) = struct*)

  let dummy_lit = Literal.LT.vrai

  let vraie_form = Formula.mk_lit dummy_lit 0

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
      timp = false;
      lit = dummy_lit;
      watched = {Vec.dummy=dummy_clause; data=[||]; sz=0};
      neg = dummy_atom;
      is_true = false;
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

    let value_ms_like a =
      if a.is_true then sprintf ":1%s" (level a)
      else if a.neg.is_true then sprintf ":0%s" (level a)
      else ":X"

    let premise fmt v =
      List.iter (fun {name=name} -> fprintf fmt "%s," name) v

    let atom fmt a =
      fprintf fmt "%s%d%s [index=%d | lit:%a] vpremise={{%a}}"
        (sign a) (a.var.vid+1) (value a) a.var.index Literal.LT.print a.lit
        premise a.var.vpremise


    let atoms_list fmt l = List.iter (fprintf fmt "%a ; " atom) l
    let atoms_array fmt arr = Array.iter (fprintf fmt "%a ; " atom) arr

    let atoms_vec fmt vec =
      for i = 0 to Vec.size vec - 1 do
        fprintf fmt "%a ; " atom (Vec.get vec i)
      done

    let clause fmt {name=name; atoms=arr; cpremise=cp} =
      fprintf fmt "%s:{ %a} cpremise={{%a}}" name atoms_vec arr premise cp

  end

  let pr_atom = Debug.atom
  let pr_clause = Debug.clause

  module MA = Literal.LT.Map

  let ale = Hstring.make "<="
  let alt = Hstring.make "<"
  let agt = Hstring.make ">"
  let is_le n = Hstring.compare n ale = 0
  let is_lt n = Hstring.compare n alt = 0
  let is_gt n = Hstring.compare n agt = 0

  let normal_form lit = (* XXX do better *)
    let av, is_neg = Literal.LT.atom_view lit in
    (if is_neg then Literal.LT.neg lit else lit), is_neg

  let max_depth a =
    let l = match Literal.LT.view a with
      | Literal.Eq (s,t) ->  [s;t]
      | Literal.Distinct(_,l) -> l
      | Literal.Builtin (_,_,l) -> l
      | Literal.Pred (p,_) -> [p]
    in
    List.fold_left (fun z t -> max z (Term.view t).Term.depth) 0 l

  let literal a = a.lit
  let weight a = a.var.weight

  let is_true a = a.is_true
  let level a = a.var.level
  let index a = a.var.index
  let neg a = a.neg

  (* tag -1 will be used for variable "vrai" *)
  let cpt_mk_var = ref (-1)

  let ma = ref MA.empty
  let make_var =
    fun lit acc ->
      let lit, negated = normal_form lit in
      try MA.find lit !ma, negated, acc
      with Not_found ->
        let cpt_fois_2 = !cpt_mk_var * 2 in
        let rec var  =
	  { vid = !cpt_mk_var;
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
            timp = false;
	    aid = cpt_fois_2 (* aid = vid*2 *) }
        and na =
	  { var = var;
	    lit = Literal.LT.neg lit;
	    watched = Vec.make 10 dummy_clause;
	    neg = pa;
	    is_true = false;
            timp = false;
	    aid = cpt_fois_2 + 1 (* aid = vid*2+1 *) } in
        ma := MA.add lit var !ma;
        incr cpt_mk_var;
        var, negated, var :: acc

  let add_atom lit acc =
    let var, negated, acc = make_var lit acc in
    (if negated then var.na else var.pa), acc

  let vrai_atom =
    let a, _ = add_atom Literal.LT.vrai [] in
    assert (!cpt_mk_var = 0);
    a.is_true <- true;
    a.var.level <- 0;
    a.var.reason <- None;
    a

  let get_atom lit =
    try (MA.find lit !ma).pa
    with Not_found ->
      try (MA.find (Literal.LT.neg lit) !ma).na with Not_found -> assert false

  let made_vars_info () =
    !cpt_mk_var, MA.fold (fun lit var acc -> var::acc)!ma []

  let get_var lit =
    let lit, negated = normal_form lit in
    try MA.find lit !ma, negated
    with Not_found -> assert false

  let faux_atom = vrai_atom.neg

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

  let clear () =
    cpt_mk_var := 0;
    ma := MA.empty

  (*end*)

  let cmp_var v1 v2 = v1.vid - v2.vid
  let eq_var v1 v2 = v1.vid - v2.vid = 0
  let tag_var v = v.vid
  let h_var v = v.vid

  let cmp_atom a1 a2 = a1.aid - a2.aid
  let eq_atom   a1 a2 = a1.aid - a2.aid = 0
  let hash_atom a1 = a1.aid
  let tag_atom  a1 = a1.aid

  let iter_atoms_of_clauses cls f =
    Vec.iter cls (fun c -> Vec.iter c.atoms f)


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
        fprintf fmt "cpt = %d@." !cpt;
        fprintf fmt "a = %a@." pr_atom a;
        fprintf fmt "c = %a@." pr_clause c;
        assert false
      end;
      !l

end

(******************************************************************************)
module type FF_SIG = sig
  type t
  type view = private UNIT of Types.atom | AND of t list | OR of t list

  val equal   : t -> t -> bool
  val compare : t -> t -> int
  val print   : Format.formatter -> t -> unit
  val print_stats : Format.formatter -> unit
  val vrai    : t
  val faux    : t
  val view    : t -> view
  val mk_lit  : Literal.LT.t -> Types.var list -> t * Types.var list
  val mk_and  : t list -> t
  val mk_or   : t list -> t
  val mk_not  : t -> t

  val simplify :
    Formula.t ->
    (Formula.t -> t * 'a) ->
    Types.var list ->
    t * (Formula.t * (t * Types.atom)) list
    * Types.var list

  val get_proxy_of : t ->
    (Types.atom * Types.atom list * bool) Util.MI.t -> Types.atom option

  val cnf_abstr : t ->
    (Types.atom * Types.atom list * bool) Util.MI.t ->
    Types.var list ->
    Types.atom
    * (Types.atom * Types.atom list * bool) list
    * (Types.atom * Types.atom list * bool) Util.MI.t
    * Types.var list

  val expand_proxy_defn :
    Types.atom list list ->
    Types.atom * Types.atom list * bool -> Types.atom list list

  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end

module Flat_Formula : FF_SIG = struct

  type view = UNIT of Types.atom | AND  of t list | OR of t list
  and t = { pos : view ; neg : view; tpos : int; tneg : int }

  let mk_not {pos=pos; neg=neg;tpos=tpos; tneg=tneg} =
    {pos=neg; neg=pos;tpos=tneg; tneg=tpos}

  module HC =
    Hconsing.Make
      (struct
        type elt = t

        let set_id tag f = { f with tpos = 2*tag; tneg = 2*tag+1 }

        let eq f1 f2 =
          let eq_aux c1 c2 = match c1, c2 with
            | UNIT x , UNIT y -> Types.eq_atom x y
            | AND u  , AND v | OR u , OR v  ->
              (try
                 List.iter2
                   (fun x y -> if x.tpos <> y.tpos then raise Exit) u v; true
               with
               | Exit -> false
               | Invalid_argument s ->
                 assert (String.compare s "List.iter2" = 0);
                 false)

            | _, _ -> false
	  in
          eq_aux f1.pos f2.pos

        let hash f =
          let h_aux f = match f with
            | UNIT a -> Types.hash_atom a
            | AND l  -> List.fold_left (fun acc f -> acc * 19 + f.tpos) 1 l
            | OR l   -> List.fold_left (fun acc f -> acc * 23 + f.tpos) 1 l
          in
          let h = h_aux f.pos in
          match f.pos with
            | UNIT _ -> abs (3 * h)
            | AND _  -> abs (3 * h + 1)
            | OR _   -> abs (3 * h + 2)

        let neg f = mk_not f

        let initial_size = 4096
        let disable_weaks () = Options.disable_weaks ()
       end)

  let cpt = ref 0

  let sp() = let s = ref "" in for _ = 1 to !cpt do s := " " ^ !s done; !s ^ !s

  let rec print fmt fa = match fa.pos with
    | UNIT a -> fprintf fmt "%a" Types.pr_atom a
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

  let print_stats fmt = ()

  let compare f1 f2 = f1.tpos - f2.tpos

  let equal f1 f2 = f1.tpos - f2.tpos = 0
  let hash f = f.tpos
  let tag  f = f.tpos
  let view f = f.pos

  let is_positive pos = match pos with
    | AND _ -> true
    | OR  _ -> false
    | UNIT at -> at == at.Types.var.Types.pa

  let make pos neg =
    let is_pos = is_positive pos in
    if is_pos then HC.make {pos=pos ; neg=neg; tpos= -1; tneg= -1 (*dump*)}
    else mk_not (HC.make {pos=neg ; neg=pos; tpos= -1; tneg= -1 (*dump*)})

  let aaz a = assert (a.Types.var.Types.level = 0)

  let complements f1 f2 = f1.tpos - f2.tneg = 0

  let mk_lit a acc =
    let at, acc = Types.add_atom a acc in
    let at =
      if disable_flat_formulas_simplification () then at
      else
        if at.Types.var.Types.level = 0 then
          if at.Types.is_true then Types.vrai_atom
          else begin
            if at.Types.neg.Types.is_true then Types.faux_atom else at
          end
        else at
    in
    make (UNIT at) (UNIT at.Types.neg), acc

  let vrai = mk_lit Literal.LT.vrai [] |> fst
  let faux = mk_not vrai

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
      | h1 :: t1, h2 :: t2 ->
        let c = compare h1 h2 in
        if c = 0 then merge_rec t1 l2 h1
        else
          if compare h1 h2 < 0
          then merge_rec l1 l2 h1
          else merge_rec l1 l2 h2

  let mk_and l =
    try
      let so, nso =
        List.fold_left
          (fun ((so,nso) as acc) e ->
            match e.pos with
              | AND l -> merge_and_check so l, nso
              | UNIT a when
                  not (disable_flat_formulas_simplification ()) &&
                    a.Types.var.Types.level = 0 ->
                begin
                  if a.Types.neg.Types.is_true then (aaz a; raise Exit); (* XXX*)
                  if a.Types.is_true then (aaz a; acc)
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
        | l -> make (AND l) (OR (List.rev (List.rev_map mk_not l)))
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
            | UNIT a -> f::atoms, ands
            | AND l  -> atoms, l::ands
        )([],[]) l
    in
    match atoms, ands with
      | [], [] -> assert false

      | _::_::_, _ ->
        if debug () then
          fprintf fmt "Failure: many distinct atoms@.";
        None

      | [_] as common, _ ->
        if debug () then
          fprintf fmt "TODO: Should have one toplevel common atom@.";
        begin
          try
            (*  a + (a . B_1) + ... (a . B_n) = a *)
            ignore (List.rev_map (diff_list common) ands);
            Some (common, [[]])
          with Not_included -> None
        end

      | [], ad::ands' ->
        if debug () then
          fprintf fmt "Should look for internal common parts@.";
        let common = List.fold_left intersect_list ad ands' in
        match common with
            [] -> None
          | _ ->
            try Some (common, List.rev_map (diff_list common) ands)
            with Not_included -> assert false

  let rec mk_or l =
    try
      let so, nso =
        List.fold_left
          (fun ((so,nso) as acc) e ->
            match e.pos with
              | OR l  -> merge_and_check so l, nso
              | UNIT a  when
                  not (disable_flat_formulas_simplification ()) &&
                    a.Types.var.Types.level = 0 ->
                begin
                  if a.Types.is_true then (aaz a; raise Exit); (* XXX *)
                  if a.Types.neg.Types.is_true then (aaz a; acc)
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
                | [{pos=UNIT _} as fa;{pos=AND ands}] ->
                  begin
                    try mk_or [fa ; (mk_and (remove_elt (mk_not fa) ands))]
                    with Not_included ->
                      make (OR l) (AND (List.rev (List.rev_map mk_not l)))
                  end
                | _ -> make (OR l) (AND (List.rev (List.rev_map mk_not l)))
              end
            | Some (com,ands) ->
              let ands = List.rev_map mk_and ands in
              mk_and ((mk_or ands) :: com)
    with Exit -> vrai

  (* translation from Formula.t *)

  let abstract_lemma abstr f tl lem new_vars =
    try fst (abstr f)
    with Not_found ->
      try fst (List.assoc f !lem)
      with Not_found ->
        if tl then begin
          lem := (f, (vrai, Types.vrai_atom)) :: !lem;
          vrai
        end
        else
          let lit = A.mk_pred (T.fresh_name Ty.Tbool) false in
          let xlit, new_v = mk_lit lit !new_vars in
          let at_lit, new_v = Types.add_atom lit new_v in
          new_vars := new_v;
          lem := (f, (xlit, at_lit)) :: !lem
            [@ocaml.ppwarning "xlit or at_lit is probably redundant"]
          ;
          xlit

  let simplify f abstr new_vars =
    let lem = ref [] in
    let new_vars = ref new_vars in
    let rec simp topl f =
      match F.view f with
        | F.Literal a ->
          let ff, l = mk_lit a !new_vars in
          new_vars := l;
          ff

        | F.Lemma _   -> abstract_lemma abstr f topl lem new_vars

        | F.Skolem _ ->
          mk_not (simp false (F.mk_not f))

        | F.Unit(f1, f2) ->
          let x1 = simp topl f1 in
          let x2 = simp topl f2 in
          begin match x1.pos , x2.pos with
            | AND l1, AND l2 -> mk_and (List.rev_append l1 l2)
            | AND l1, _      -> mk_and (x2 :: l1)
            | _     , AND l2 -> mk_and (x1 :: l2)
            | _              -> mk_and [x1; x2]
          end

        | F.Clause(f1, f2, _) ->
          let x1 = simp false f1 in
          let x2 = simp false f2 in
          begin match x1.pos, x2.pos with
            | OR l1, OR l2 -> mk_or (List.rev_append l1 l2)
            | OR l1, _     -> mk_or (x2 :: l1)
            | _    , OR l2 -> mk_or (x1 :: l2)
            | _            -> mk_or [x1; x2]
          end


        | F.Let {F.let_var=lvar; let_term=lterm; let_subst=s; let_f=lf} ->
          let f' = F.apply_subst s lf in
          let v = Symbols.Map.find lvar (fst s) in
          let at, new_v = mk_lit (A.mk_eq v lterm) !new_vars in
          new_vars := new_v;
          let res = simp topl f' in
          begin match res.pos with
            | AND l -> mk_and (at :: l)
            | _     -> mk_and [at; res]
          end
    in
    let res = simp true f in
    res, !lem, !new_vars

  (* CNF_ABSTR a la Tseitin *)

  let atom_of_lit lit is_neg new_vars =
    let a, l = Types.add_atom lit !new_vars in
    new_vars := l;
    if is_neg then a.Types.neg else a

  let mk_new_proxy n =
    let hs = Hs.make ("PROXY__" ^ (string_of_int n)) in
    let sy = Symbols.Name(hs, Symbols.Other) in
    A.mk_pred (Term.make sy [] Ty.Tbool) false

  let get_proxy_of f proxies_mp =
    try let p, _, _ = Util.MI.find f.tpos proxies_mp in Some p
    with Not_found ->
      try let p, _, _ = Util.MI.find f.tneg proxies_mp in Some p.Types.neg
      with Not_found -> None


  let expand_proxy_defn acc (p, l, is_and) =
    if is_and then (* p <=> (l1 and ... and l_n) *)
      let np = p.Types.neg in
      let cl, acc =
        List.fold_left
          (fun (cl,acc) a -> (a.Types.neg :: cl), [np; a] :: acc)([p],acc) l
      in
      cl :: acc
    else (* p <=> (l1 or ... or l_n) *)
      let acc = List.fold_left (fun acc a -> [p;a.Types.neg]::acc) acc l in
      ((p.Types.neg) :: l) :: acc

  let cnf_abstr f proxies_mp new_vars =
    let proxies_mp = ref proxies_mp in
    let new_proxies = ref [] in
    let new_vars = ref new_vars in
    let rec abstr f = match f.pos with
      | UNIT a -> a
      | AND l | OR l ->
        match get_proxy_of f !proxies_mp with
        | Some p -> p
        | None ->
          let l = List.rev (List.rev_map abstr l) in
          let p = atom_of_lit (mk_new_proxy f.tpos) false new_vars in
          let is_and = match f.pos with
            | AND _ -> true | OR _ -> false | UNIT _ -> assert false
          in
          new_proxies := (p, l, is_and) :: !new_proxies;
          proxies_mp := Util.MI.add f.tpos (p, l, is_and) !proxies_mp;
          p
    in
    let abstr_f = abstr f in
    abstr_f, !new_proxies, !proxies_mp, !new_vars


  module Set = Set.Make(struct type t'=t type t=t' let compare=compare end)
  module Map = Map.Make(struct type t'=t type t=t' let compare=compare end)

end

(******************************************************************************)

open Types

module Ex = Explanation

exception Sat
exception Unsat of clause list option
exception Restart

let vraie_form = Formula.vrai


module type SAT_ML = sig
  (*module Make (Dummy : sig end) : sig*)
  type state
  type th

  val solve : unit -> unit

  val set_new_proxies :
    (Types.atom * Types.atom list * bool) Util.MI.t -> unit

  val new_vars :
    var list ->
    atom list list -> atom list list ->
    atom list list * atom list list

  val assume :
    Types.atom list list -> Types.atom list list -> Formula.t ->
    cnumber : int ->
    Types.atom option Flat_Formula.Map.t -> dec_lvl:int ->
    unit

  val boolean_model : unit -> Types.atom list
  val theory_assumed : unit -> Literal.LT.Set.t
  val current_tbox : unit -> th
  val set_current_tbox : th -> unit
  val empty : unit -> unit
  val clear : unit -> unit

  val save : unit -> state
  val restore : state -> unit

  val reset_steps : unit -> unit
  val get_steps : unit -> int64

  val assume_th_elt : Commands.th_elt -> unit
  val decision_level : unit -> int
  val cancel_until : int -> unit

  val update_lazy_cnf :
    do_bcp : bool ->
    Types.atom option Flat_Formula.Map.t -> dec_lvl:int -> unit
  val exists_in_lazy_cnf : Flat_Formula.t -> bool

  val known_lazy_formulas : unit -> int Flat_Formula.Map.t
(*end*)
end

module MFF = Flat_Formula.Map
module SFF = Flat_Formula.Set

module Make (Th : Theory.S) : SAT_ML with type th = Th.t = struct


  type th = Th.t
  type env =
      {
      (* si vrai, les contraintes sont deja fausses *)
        mutable is_unsat : bool;

        mutable unsat_core : clause list option;

      (* clauses du probleme *)
        mutable clauses : clause Vec.t;

      (* clauses apprises *)
        mutable learnts : clause Vec.t;

      (* valeur de l'increment pour l'activite des clauses *)
        mutable clause_inc : float;

      (* valeur de l'increment pour l'activite des variables *)
        mutable var_inc : float;

      (* un vecteur des variables du probleme *)
        mutable vars : var Vec.t;

      (* la pile de decisions avec les faits impliques *)
        mutable trail : atom Vec.t;

      (* une pile qui pointe vers les niveaux de decision dans trail *)
        mutable trail_lim : int Vec.t;

      (* Tete de la File des faits unitaires a propager.
	 C'est un index vers le trail *)
        mutable qhead : int;

      (* Nombre des assignements top-level depuis la derniere
         execution de 'simplify()' *)
        mutable simpDB_assigns : int;

      (* Nombre restant de propagations a faire avant la prochaine
         execution de 'simplify()' *)
        mutable simpDB_props : int;

      (* Un tas ordone en fonction de l'activite des variables *)
        mutable order : Iheap.t;

      (* estimation de progressions, mis a jour par 'search()' *)
        mutable progress_estimate : float;

      (* *)
        remove_satisfied : bool;

      (* inverse du facteur d'acitivte des variables, vaut 1/0.999 par defaut *)
        var_decay : float;

      (* inverse du facteur d'activite des clauses, vaut 1/0.95 par defaut *)
        clause_decay : float;

      (* la limite de restart initiale, vaut 100 par defaut *)
        mutable restart_first : int;

      (* facteur de multiplication de restart limite, vaut 1.5 par defaut*)
        restart_inc : float;

      (* limite initiale du nombre de clause apprises, vaut 1/3
         des clauses originales par defaut *)
        mutable learntsize_factor : float;

      (* multiplier learntsize_factor par cette valeur a chaque restart,
         vaut 1.1 par defaut *)
        learntsize_inc : float;

      (* controler la minimisation des clauses conflit, vaut true par defaut *)
        expensive_ccmin : bool;

      (* controle la polarite a choisir lors de la decision *)
        polarity_mode : bool;

        mutable starts : int;

        mutable decisions : int;

        mutable propagations : int;

        mutable conflicts : int;

        mutable clauses_literals : int;

        mutable learnts_literals : int;

        mutable max_literals : int;

        mutable tot_literals : int;

        mutable nb_init_vars : int;

        mutable nb_init_clauses : int;

        mutable model : var Vec.t;

        mutable tenv : Th.t;

        mutable unit_tenv : Th.t;

        mutable tenv_queue : Th.t Vec.t;

        mutable tatoms_queue : atom Queue.t;

        mutable cpt_current_propagations : int;

        mutable proxies : (Types.atom * Types.atom list * bool) Util.MI.t;

        mutable lazy_cnf : Flat_Formula.t list;

        lazy_cnf_queue : Flat_Formula.t list Vec.t;

        mutable ff_lvl : int MFF.t;

        mutable lvl_ff : SFF.t Util.MI.t;
      }

  type conflict_origin =
    | C_none
    | C_bool of clause
    | C_theory of Ex.t

  exception Conflict of clause
  (*module Make (Dummy : sig end) = struct*)

  module Solver_types = Types(*.Make(struct end)*)

  let steps = ref 0L

  let reset_steps () = steps := 0L
  let get_steps () = !steps

  open Solver_types

  type state =
      {
        env : env;
        st_cpt_mk_var: int;
        st_ma : var Literal.LT.Map.t;
      }


  let env =
    {
      is_unsat = false;

      unsat_core = None;

      clauses = Vec.make 0 dummy_clause; (*sera mis a jour lors du parsing*)

      learnts = Vec.make 0 dummy_clause; (*sera mis a jour lors du parsing*)

      clause_inc = 1.;

      var_inc = 1.;

      vars = Vec.make 0 dummy_var; (*sera mis a jour lors du parsing*)

      trail = Vec.make 601 dummy_atom;

      trail_lim = Vec.make 601 (-105);

      qhead = 0;

      simpDB_assigns = -1;

      simpDB_props = 0;

      order = Iheap.init 0; (* sera mis a jour dans solve *)

      progress_estimate = 0.;

      remove_satisfied = true;

      var_decay = 1. /. 0.95;

      clause_decay = 1. /. 0.999;

      restart_first = 100;

      restart_inc = 1.5;

      learntsize_factor = 1. /. 3. ;

      learntsize_inc = 1.1;

      expensive_ccmin = true;

      polarity_mode = false;

      starts = 0;

      decisions = 0;

      propagations = 0;

      conflicts = 0;

      clauses_literals = 0;

      learnts_literals = 0;

      max_literals = 0;

      tot_literals = 0;

      nb_init_vars = 0;

      nb_init_clauses = 0;

      model = Vec.make 0 dummy_var;

      tenv = Th.empty();

      unit_tenv = Th.empty();

      tenv_queue = Vec.make 100 (Th.empty());

      tatoms_queue = Queue.create ();

      cpt_current_propagations = 0;

      proxies = Util.MI.empty;

      lazy_cnf = [];

      lazy_cnf_queue = Vec.make 10 [];

      ff_lvl = MFF.empty;

      lvl_ff = Util.MI.empty;
}


(*
  module SA = Set.Make
  (struct
  type t = Types.atom
  let compare a b = a.Types.aid - b.Types.aid
  end)

  module SSA = Set.Make(SA)


  let ssa = ref SSA.empty

  let clause_exists atoms =
  try
(*List.iter
  (fun a -> if a.is_true then raise Exit) atoms;*)
  let sa = List.fold_left (fun s e -> SA.add e s) SA.empty atoms in
  if SSA.mem sa !ssa then true
  else begin
  ssa := SSA.add sa !ssa;
  false
  end
  with Exit -> true

  let f_weight i j =
  let vj = Vec.get env.vars j in
  let vi = Vec.get env.vars i in
(*if vi.sweight <> vj.sweight then vi.sweight < vj.sweight
  else*) vj.weight < vi.weight
*)

  let f_weight i j =
    Pervasives.(<) (Vec.get env.vars j).weight (Vec.get env.vars i).weight

  let f_filter i = (Vec.get env.vars i).level < 0

  let insert_var_order v =
    Iheap.insert f_weight env.order v.vid

  let var_decay_activity () = env.var_inc <- env.var_inc *. env.var_decay

  let clause_decay_activity () =
    env.clause_inc <- env.clause_inc *. env.clause_decay

  let var_bump_activity v =
    v.weight <- v.weight +. env.var_inc;
    if Pervasives.(>) v.weight 1e100 then begin
      for i = 0 to env.vars.Vec.sz - 1 do
        (Vec.get env.vars i).weight <- (Vec.get env.vars i).weight *. 1e-100
      done;
      env.var_inc <- env.var_inc *. 1e-100;
    end;
    if Iheap.in_heap env.order v.vid then
      Iheap.decrease f_weight env.order v.vid


  let clause_bump_activity c =
    c.activity <- c.activity +. env.clause_inc;
    if Pervasives.(>) c.activity 1e20 then begin
      for i = 0 to env.learnts.Vec.sz - 1 do
        (Vec.get env.learnts i).activity <-
          (Vec.get env.learnts i).activity *. 1e-20;
      done;
      env.clause_inc <- env.clause_inc *. 1e-20
    end

  let decision_level () = Vec.size env.trail_lim

  let nb_assigns () = Vec.size env.trail
  let nb_clauses () = Vec.size env.clauses
  let nb_learnts () = Vec.size env.learnts
  let nb_vars    () = Vec.size env.vars

  let new_decision_level () =
    env.decisions <- env.decisions + 1;
    Vec.push env.trail_lim (Vec.size env.trail);
    if Options.profiling() then Profiling.decision (decision_level()) "<none>";
    Vec.push env.tenv_queue env.tenv; (* save the current tenv *)
    if Options.lazy_sat () then Vec.push env.lazy_cnf_queue env.lazy_cnf

  let attach_clause c =
    Vec.push (Vec.get c.atoms 0).neg.watched c;
    Vec.push (Vec.get c.atoms 1).neg.watched c;
    if c.learnt then
      env.learnts_literals <- env.learnts_literals + Vec.size c.atoms
    else
      env.clauses_literals <- env.clauses_literals + Vec.size c.atoms

  let detach_clause c =
    c.removed <- true;
  (*
    Vec.remove (Vec.get c.atoms 0).neg.watched c;
    Vec.remove (Vec.get c.atoms 1).neg.watched c;
  *)
    if c.learnt then
      env.learnts_literals <- env.learnts_literals - Vec.size c.atoms
    else
      env.clauses_literals <- env.clauses_literals - Vec.size c.atoms

  let remove_clause c = detach_clause c

  let satisfied c =
    try
      for i = 0 to Vec.size c.atoms - 1 do
        let a = Vec.get c.atoms i in
        if a.is_true && a.var.level ==0 then raise Exit
      done;
      false
    with Exit -> true

  let unassign_atom a =
    a.is_true <- false;
    a.neg.is_true <- false;
    a.timp <- false;
    a.neg.timp <- false;
    a.var.level <- -1;
    a.var.index <- -1;
    a.var.reason <- None;
    a.var.vpremise <- []

  let enqueue_assigned a =
    assert (a.is_true || a.neg.is_true);
    assert (a.var.level >= 0);
    Vec.push env.trail a

  let cancel_ff_lvls_until lvl =
    for i = decision_level () downto lvl + 1 do
      try
        let s = Util.MI.find i env.lvl_ff in
        SFF.iter (fun f' -> env.ff_lvl <- MFF.remove f' env.ff_lvl) s;
        env.lvl_ff <- Util.MI.remove i env.lvl_ff;
      with Not_found -> ()
    done

(* annule tout jusqu'a lvl *exclu*  *)
  let cancel_until lvl =
    cancel_ff_lvls_until lvl;
    let repush = ref [] in
    if decision_level () > lvl then begin
      env.qhead <- Vec.get env.trail_lim lvl;
      for c = Vec.size env.trail - 1 downto env.qhead do
        let a = Vec.get env.trail c in
        if Options.minimal_bj () && a.var.level <= lvl then begin
          assert (a.var.level = 0 || a.var.reason != None);
          repush := a :: !repush
        end
        else begin
          unassign_atom a;
          insert_var_order a.var
        end
      done;
      Queue.clear env.tatoms_queue;
      env.tenv <- Vec.get env.tenv_queue lvl; (* recover the right tenv *)
      if Options.lazy_sat () then env.lazy_cnf <- Vec.get env.lazy_cnf_queue lvl;
      Vec.shrink env.trail ((Vec.size env.trail) - env.qhead) true;
      Vec.shrink env.trail_lim ((Vec.size env.trail_lim) - lvl) true;
      Vec.shrink env.tenv_queue ((Vec.size env.tenv_queue) - lvl) true;
      if Options.lazy_sat () then
        Vec.shrink env.lazy_cnf_queue ((Vec.size env.lazy_cnf_queue) - lvl) true;
      (try
         let last_dec =
           if Vec.size env.trail_lim = 0 then 0 else Vec.last env.trail_lim in
         env.cpt_current_propagations <- (Vec.size env.trail) - last_dec
       with e -> assert false
      );
    end;
    if Options.profiling() then Profiling.reset_dlevel (decision_level());
    assert (Vec.size env.trail_lim = Vec.size env.tenv_queue);
    assert (Options.minimal_bj () || (!repush == []));
    List.iter enqueue_assigned !repush

  let rec pick_branch_var () =
    if Iheap.size env.order = 0 then raise Sat;
    let max = Iheap.remove_min f_weight env.order in
    let v = Vec.get env.vars max in
    if v.level>= 0 then begin
      assert (v.pa.is_true || v.na.is_true);
      pick_branch_var ()
    end
    else v

  let pick_branch_lit () =
    let v = pick_branch_var () in
    v.na

  let debug_enqueue_level a lvl reason =
    match reason with
    | None -> ()
    | Some c ->
      let maxi = ref min_int in
      for i = 0 to Vec.size c.atoms - 1 do
        let b = Vec.get c.atoms i in
        if not (eq_atom a b) then maxi := max !maxi b.var.level
      done;
      assert (!maxi = lvl)

  let max_level_in_clause c =
    let max_lvl = ref 0 in
    Vec.iter c.atoms (fun a ->
        max_lvl := max !max_lvl a.var.level);
    !max_lvl

  let enqueue a lvl reason =
    assert (not a.is_true && not a.neg.is_true &&
              a.var.level < 0 && a.var.reason == None && lvl >= 0);
  (* Garder la reason car elle est utile pour les unsat-core *)
  (*let reason = if lvl = 0 then None else reason in*)
    a.is_true <- true;
    a.var.level <- lvl;
    a.var.reason <- reason;
  (*eprintf "enqueue: %a@." Debug.atom a; *)
    Vec.push env.trail a;
    a.var.index <- Vec.size env.trail;
    if Options.enable_assertions() then  debug_enqueue_level a lvl reason

  let progress_estimate () =
    let prg = ref 0. in
    let nbv = to_float (nb_vars()) in
    let lvl = decision_level () in
    let _F = 1. /. nbv in
    for i = 0 to lvl do
      let _beg = if i = 0 then 0 else Vec.get env.trail_lim (i-1) in
      let _end =
        if i=lvl then Vec.size env.trail
        else Vec.get env.trail_lim i in
      prg := !prg +. _F**(to_float i) *. (to_float (_end - _beg))
    done;
    !prg /. nbv

  let check_levels propag_lvl current_lvl =
    assert (propag_lvl <= current_lvl);
    assert (propag_lvl == current_lvl || (Options.minimal_bj ()))

  let best_propagation_level c =
    let mlvl =
      if Options.minimal_bj () then max_level_in_clause c
      else decision_level ()
    in
    check_levels mlvl (decision_level ());
    mlvl

  let propagate_in_clause a c i watched new_sz =
    let atoms = c.atoms in
    let first = Vec.get atoms 0 in
    if first == a.neg then begin (* le literal faux doit etre dans .(1) *)
      Vec.set atoms 0 (Vec.get atoms 1);
      Vec.set atoms 1 first
    end;
    let first = Vec.get atoms 0 in
    if first.is_true then begin
      (* clause vraie, la garder dans les watched *)
      Vec.set watched !new_sz c;
      incr new_sz;
      if Options.profiling() then Profiling.elim true;
    end
    else
      try (* chercher un nouveau watcher *)
        for k = 2 to Vec.size atoms - 1 do
          let ak = Vec.get atoms k in
          if not (ak.neg.is_true) then begin
          (* Watcher Trouve: mettre a jour et sortir *)
            Vec.set atoms 1 ak;
            Vec.set atoms k a.neg;
            Vec.push ak.neg.watched c;
            raise Exit
          end
        done;
          (* Watcher NON Trouve *)
          if first.neg.is_true then begin
            (* la clause est fausse *)
            env.qhead <- Vec.size env.trail;
            for k = i to Vec.size watched - 1 do
              Vec.set watched !new_sz (Vec.get watched k);
              incr new_sz;
            done;
            if Options.profiling() then Profiling.bcp_conflict true true;
            raise (Conflict c)
          end
          else begin
            (* la clause est unitaire *)
            Vec.set watched !new_sz c;
            incr new_sz;
            let mlvl = best_propagation_level c in
            enqueue first mlvl (Some c);
            if Options.profiling() then Profiling.red true;
          end
      with Exit -> ()

  let propagate_atom a res =
    let watched = a.watched in
    let new_sz_w = ref 0 in
    begin
      try
        for i = 0 to Vec.size watched - 1 do
          let c = Vec.get watched i in
          if not c.removed then propagate_in_clause a c i watched new_sz_w
        done;
      with Conflict c -> assert (!res == C_none); res := C_bool c
    end;
    let dead_part = Vec.size watched - !new_sz_w in
    Vec.shrink watched dead_part true


  let do_case_split origin =
    if Options.case_split_policy () != Util.AfterTheoryAssume then
      failwith
        "Only AfterTheoryAssume case-split policy is supported by satML";
    if Options.case_split_policy () == origin then
      try
        let tenv, _ = Th.do_case_split env.tenv in
        env.tenv <- tenv;
        C_none
      with Exception.Inconsistent (expl, classes) ->
        C_theory expl
    else C_none

  module SA =
    Set.Make
      (struct
        type t = Types.atom
        let compare a b =
          let c = a.var.level - b.var.level in
          if c <> 0 then c
          else Types.cmp_atom a b
      end)

  let get_atom_or_proxy f proxies =
    let open Flat_Formula in
    match view f with
    | UNIT a -> a
    | _ ->
      match get_proxy_of f proxies with
      | Some a -> a
      | None -> assert false

  let compute_facts_for_theory_propagate () =
    let open Flat_Formula in
    let tat = ref SA.empty in
    let accu = ref [] in
      accu := env.lazy_cnf;
      let continue = ref true in
      while !continue do
        continue := false;
        let next =
          List.fold_left (fun next f ->
              let proxy_f = get_atom_or_proxy f env.proxies in
                if not proxy_f.Types.is_true then f :: next
                else
                  match view f with
                  | UNIT a ->
                    tat := SA.add a !tat;
                    next

                  | AND l ->
                    continue := true;
                    List.fold_left (fun next e -> e :: next) next l

                  | OR l ->
                    let res =
                      List.find_opt (fun e ->
                          let proxy_e = get_atom_or_proxy e env.proxies in
                          proxy_e.Types.is_true
                        ) l in
                    match res with
                    | None -> f ::next
                    | Some e ->
                      continue := true;
                      e :: next
            ) [] !accu
        in
        accu := next
      done;
      let tatoms_queue = Queue.create () in
      SA.iter (fun a -> Queue.push a tatoms_queue) !tat;
      env.lazy_cnf <- !accu;
      tatoms_queue

  let expensive_theory_propagate () = None
(* try *)
(*   if D1.d then eprintf "expensive_theory_propagate@."; *)
(*   ignore(Th.expensive_processing env.tenv); *)
(*   if D1.d then eprintf "expensive_theory_propagate => None@."; *)
(*   None *)
(* with Exception.Inconsistent dep ->  *)
(*   if D1.d then eprintf "expensive_theory_propagate => Inconsistent@."; *)
(*   Some dep *)

  let unit_theory_propagate full_q lazy_q =
    let facts =
      Queue.fold
        (fun acc ta ->
          assert (ta.is_true);
          assert (ta.var.level >= 0);
          if ta.var.level = 0 then
            (ta.lit, Ex.empty, 0, env.cpt_current_propagations) :: acc
          else acc
        )[] lazy_q
    in
    if facts == [] then C_none
    else
      try
        (*let full_model = nb_assigns() = env.nb_init_vars in*)
        (* XXX what to do with the other results of Th.assume ? *)
        let t,_,cpt =
          Th.assume ~ordered:false
            (List.rev facts) env.unit_tenv
        in
        steps := Int64.add (Int64.of_int cpt) !steps;
        if steps_bound () <> -1
	  && Int64.compare !steps (Int64.of_int (steps_bound ())) > 0 then
	  begin
	    printf "Steps limit reached: %Ld@." !steps;
	    exit 1
	  end;
        env.unit_tenv <- t;
        C_none
      with Exception.Inconsistent (dep, terms) ->
        (* XXX what to do with terms ? *)
	(* eprintf "th inconsistent : %a @." Ex.print dep; *)
        if Options.profiling() then Profiling.theory_conflict();
        C_theory dep

  let theory_propagate () =
    let facts = ref [] in
    let dlvl = decision_level () in
    let tatoms_queue =
      if Options.lazy_sat () then compute_facts_for_theory_propagate ()
      else env.tatoms_queue
    in
    match unit_theory_propagate env.tatoms_queue tatoms_queue with
    | C_theory dep as res -> res
    | C_bool _ -> assert false
    | C_none ->
    while not (Queue.is_empty tatoms_queue) do
      let a = Queue.pop tatoms_queue in
      let ta =
        if a.is_true then a
        else if a.neg.is_true then a.neg (* TODO: useful ?? *)
        else assert false
      in
      let ex =
        if proof () || ta.var.level > 0 then Ex.singleton (Ex.Literal ta.lit)
        else Ex.empty
      in
      assert (Literal.LT.is_ground ta.lit);
      if ta.timp then
        ()
          [@ocaml.ppwarning "XXX: only do this for instantiation ?"]
      else
        facts := (ta.lit, ex, dlvl,env.cpt_current_propagations) :: !facts;
      env.cpt_current_propagations <- env.cpt_current_propagations + 1
    done;
    if !facts == [] then C_none
    else
      try
        (*let full_model = nb_assigns() = env.nb_init_vars in*)
        (* XXX what to do with the other results of Th.assume ? *)
        let t,_,cpt =
          Th.assume ~ordered:(not (Options.lazy_sat ()))
            (List.rev !facts) env.tenv
        in
        steps := Int64.add (Int64.of_int cpt) !steps;
        if steps_bound () <> -1
	  && Int64.compare !steps (Int64.of_int (steps_bound ())) > 0 then
	  begin
	    printf "Steps limit reached: %Ld@." !steps;
	    exit 1
	  end;
        env.tenv <- t;
        do_case_split Util.AfterTheoryAssume
      (*if full_model then expensive_theory_propagate ()
        else None*)
      with Exception.Inconsistent (dep, terms) ->
        (* XXX what to do with terms ? *)
	(* eprintf "th inconsistent : %a @." Ex.print dep; *)
        if Options.profiling() then Profiling.theory_conflict();
        C_theory dep

  let propagate () =
    let num_props = ref 0 in
    let res = ref C_none in
    (*assert (Queue.is_empty env.tqueue);*)
    while env.qhead < Vec.size env.trail do
      let a = Vec.get env.trail env.qhead in
      env.qhead <- env.qhead + 1;
      incr num_props;
      propagate_atom a res;
      Queue.push a env.tatoms_queue;
    done;
    env.propagations <- env.propagations + !num_props;
    env.simpDB_props <- env.simpDB_props - !num_props;
    !res

  let f_sort_db c1 c2 =
    let sz1 = Vec.size c1.atoms in
    let sz2 = Vec.size c2.atoms in
    let c = Pervasives.compare c1.activity c2.activity in
    if sz1 = sz2 && c = 0 then 0
    else
      if sz1 > 2 && (sz2 = 2 || c < 0) then -1
      else 1

  let locked c = false(*
                        try
                        for i = 0 to Vec.size env.vars - 1 do
                        match (Vec.get env.vars i).reason with
	                | Some c' when c ==c' -> raise Exit
	                | _ -> ()
                        done;
                        false
                        with Exit -> true*)

  let reduce_db () = ()
(*
  let extra_lim = env.clause_inc /. (to_float (Vec.size env.learnts)) in
  Vec.sort env.learnts f_sort_db;
  let lim2 = Vec.size env.learnts in
  let lim1 = lim2 / 2 in
  let j = ref 0 in
  for i = 0 to lim1 - 1 do
  let c = Vec.get env.learnts i in
  if Vec.size c.atoms > 2 && not (locked c) then
  remove_clause c
  else
  begin Vec.set env.learnts !j c; incr j end
  done;
  for i = lim1 to lim2 - 1 do
  let c = Vec.get env.learnts i in
  if Vec.size c.atoms > 2 && not (locked c) && c.activity < extra_lim then
  remove_clause c
  else
  begin Vec.set env.learnts !j c; incr j end
  done;
  Vec.shrink env.learnts (lim2 - !j) true
*)

  let remove_satisfied vec =
    let j = ref 0 in
    let k = Vec.size vec - 1 in
    for i = 0 to k do
      let c = Vec.get vec i in
      if satisfied c then remove_clause c
      else begin
        Vec.set vec !j (Vec.get vec i);
        incr j
      end
    done;
    Vec.shrink vec (k + 1 - !j) true


  module HUC = Hashtbl.Make
    (struct type t = clause let equal = (==) let hash = Hashtbl.hash end)


  let report_b_unsat linit =
    if not (Options.proof ()) then begin
      env.is_unsat <- true;
      env.unsat_core <- None;
      raise (Unsat None)
    end
    else
      match linit with
      | [] | _::_::_ ->
        (* currently, report_b_unsat called with a singleton if proof = true *)
        assert false

      | [{atoms=atoms}] ->
        assert (Options.proof ());
        let l = ref linit in
        for i = 0 to Vec.size atoms - 1 do
          let v = (Vec.get atoms i).var in
          l := List.rev_append v.vpremise !l;
          match v.reason with None -> () | Some c -> l := c :: !l
        done;
        if false then begin
          eprintf "@.>>UNSAT Deduction made from:@.";
          List.iter
            (fun hc ->
              eprintf "    %a@." Types.pr_clause hc
            )!l;
        end;
        let uc = HUC.create 17 in
        let rec roots todo =
          match todo with
          | [] -> ()
          | c::r ->
	    for i = 0 to Vec.size c.atoms - 1 do
	      let v = (Vec.get c.atoms i).var in
	      if not v.seen then begin
	        v.seen <- true;
	        roots v.vpremise;
	        match v.reason with None -> () | Some r -> roots [r];
	      end
	    done;
            match c.cpremise with
            | []    -> if not (HUC.mem uc c) then HUC.add uc c (); roots r
            | prems -> roots prems; roots r
        in roots !l;
        let unsat_core = HUC.fold (fun c _ l -> c :: l) uc [] in
        if false then begin
          eprintf "@.>>UNSAT_CORE:@.";
          List.iter
            (fun hc ->
              eprintf "    %a@." Types.pr_clause hc
            )unsat_core;
        end;
        env.is_unsat <- true;
        let unsat_core = Some unsat_core in
        env.unsat_core <- unsat_core;
        raise (Unsat unsat_core)


  let report_t_unsat dep =
    if not (Options.proof ()) then begin
      env.is_unsat <- true;
      env.unsat_core <- None;
      raise (Unsat None)
    end
    else
      let l =
        Ex.fold_atoms
          (fun ex l ->
            match ex with
            | Ex.Literal lit ->
              let {var=v} = Types.get_atom lit in
              let l = List.rev_append v.vpremise l in
              begin match v.reason with
              | None -> l
              | Some c -> c :: l
              end
            | _ -> assert false (* TODO *)
          ) dep []
      in
      if false then begin
        eprintf "@.>>T-UNSAT Deduction made from:@.";
        List.iter
          (fun hc ->
            eprintf "    %a@." Types.pr_clause hc
          )l;
      end;
      let uc = HUC.create 17 in
      let rec roots todo =
        match todo with
        | [] -> ()
        | c::r ->
	  for i = 0 to Vec.size c.atoms - 1 do
	    let v = (Vec.get c.atoms i).var in
	    if not v.seen then begin
	      v.seen <- true;
	      roots v.vpremise;
	      match v.reason with None -> () | Some r -> roots [r];
	    end
	  done;
          match c.cpremise with
          | []    -> if not (HUC.mem uc c) then HUC.add uc c (); roots r
          | prems -> roots prems; roots r
      in roots l;
      let unsat_core = HUC.fold (fun c _ l -> c :: l) uc [] in
      if false then begin
        eprintf "@.>>T-UNSAT_CORE:@.";
        List.iter
          (fun hc ->
            eprintf "    %a@." Types.pr_clause hc
          ) unsat_core;
      end;
      env.is_unsat <- true;
      let unsat_core = Some unsat_core in
      env.unsat_core <- unsat_core;
      raise (Unsat unsat_core)

(*** experimental: taken from ctrl-ergo-2 ********************

     let rec theory_simplify () =
     let theory_simplification = 2 in
     let assume a =
     assert (Literal.LT.is_ground ta.lit);
     ignore (Th.assume a.lit Ex.empty env.tenv)
     in
     if theory_simplification >= 2 then begin
     for i = 0 to Vec.size env.vars - 1 do
     try
     let a = (Vec.get env.vars i).pa in
     if not (a.is_true || a.neg.is_true) then
     try
     assume a;
     try assume a.neg
     with Exception.Inconsistent _ ->
     if debug () then
     eprintf "%a propagated m/theory at level 0@.@." Types.pr_atom a;
     enqueue a 0 None (* Mettre Some dep pour les unsat-core*)
     with Exception.Inconsistent _ ->
     if debug () then
     eprintf "%a propagated m/theory at level 0@.@." Types.pr_atom a.neg;
     enqueue a.neg 0 None (* Mettre Some dep pour les unsat-core*)
     with Not_found -> ()
     done;

     let head = env.qhead in
     if propagate () <> None || theory_propagate () <> None then raise (Unsat []);
     let head' = env.qhead in
     if head' > head then theory_simplify ()
     end
*)

  let all_propagations () =
    match propagate () with
    | C_bool c -> C_bool c
    | C_theory _ -> assert false
    | C_none ->
      match theory_propagate () with
      | C_bool _ -> assert false
      | C_theory dep -> C_theory dep
      | C_none -> C_none

  let report_conflict c =
    match c with
    | C_bool confl -> report_b_unsat [confl]
    | C_theory dep -> report_t_unsat dep
    | C_none -> ()

  let simplify () =
    assert (decision_level () = 0);
    if env.is_unsat then raise (Unsat env.unsat_core);
    (* report possible propagation conflict *)
    report_conflict (all_propagations ());
    if nb_assigns() <> env.simpDB_assigns && env.simpDB_props <= 0 then begin
      if debug () then fprintf fmt "simplify@.";
    (*theory_simplify ();*)
      if Vec.size env.learnts > 0 then remove_satisfied env.learnts;
      if env.remove_satisfied then remove_satisfied env.clauses;
    (*Iheap.filter env.order f_filter f_weight;*)
      env.simpDB_assigns <- nb_assigns ();
      env.simpDB_props <- env.clauses_literals + env.learnts_literals;
    end


  let record_learnt_clause ~is_T_learn blevel learnt history size =
    let curr_level = decision_level () in
    if not is_T_learn || Options.minimal_bj () ||
       blevel = curr_level then begin
      check_levels blevel curr_level;
      match learnt with
      | [] -> assert false
      | [fuip] ->
        fuip.var.vpremise <- history;
        enqueue fuip 0 None
      | fuip :: _ ->
        let name = fresh_lname () in
        let lclause = make_clause name learnt vraie_form size true history in
        Vec.push env.learnts lclause;
        attach_clause lclause;
        clause_bump_activity lclause;
        let propag_lvl = best_propagation_level lclause in
        enqueue fuip propag_lvl (Some lclause)
    end;
    if not is_T_learn then begin
      var_decay_activity ();
      clause_decay_activity()
    end

  let conflict_analyze_aux c_clause max_lvl =
    let pathC = ref 0 in
    let learnt = ref SA.empty in
    let cond = ref true in
    let blevel = ref 0 in
    let seen = ref [] in
    let c = ref c_clause in
    let tr_ind = ref (Vec.size env.trail -1) in
    let history = ref [] in
    while !cond do
      if !c.learnt then clause_bump_activity !c;
      history := !c :: !history;
      Vec.iter !c.atoms (fun a ->
          assert (a.is_true || a.neg.is_true && a.var.level >= 0);
          if not a.var.seen && a.var.level > 0 then begin
            var_bump_activity a.var;
            a.var.seen <- true;
            seen := a :: !seen;
            if a.var.level >= max_lvl then incr pathC
            else begin
              learnt := SA.add a !learnt;
              blevel := max !blevel a.var.level
            end
          end
      );

      while assert (!tr_ind >= 0);
        let v = (Vec.get env.trail !tr_ind).var in
        not v.seen || ((Options.minimal_bj ()) && v.level < max_lvl) do
        decr tr_ind
      done;

      decr pathC;
      let p = Vec.get env.trail !tr_ind in
      decr tr_ind;
      match !pathC,p.var.reason with
      | 0, _ ->
        cond := false;
        learnt := SA.add p.neg !learnt
      | n, None -> assert false
      | n, Some cl -> c := cl
    done;
    List.iter (fun q -> q.var.seen <- false) !seen;
    let learnt = SA.elements !learnt in
    let learnt = List.fast_sort (fun a b -> b.var.level - a.var.level) learnt in
    let size = List.length learnt in
    let bj_level =
      if Options.minimal_bj () then
        match learnt with
          [] -> 0
        | a :: _ -> max 0 (a.var.level - 1)
      else !blevel
    in
    bj_level, learnt, !history, size

  let fixable_with_simple_backjump confl max_lvl lv =
    if not (Options.minimal_bj ()) then None
    else
      try
        let max_v = ref None in
        let snd_max = ref (-1) in
        List.iter
          (fun v ->
            let lvl = v.level in
            if lvl == max_lvl then begin
              if !max_v != None then raise Exit;
              max_v := Some v
            end
            else begin
              assert (lvl < max_lvl);
              snd_max := max !snd_max lvl
            end
          )lv;
        match !max_v with
        | None -> assert false
        | Some v ->
          let snd_max = !snd_max in
          assert (snd_max >= 0);
          assert (snd_max < max_lvl);
          assert (not confl.removed); (* do something otherwise ?*)
          let a = if v.pa.is_true then v.na else v.pa in
          assert (a.neg.is_true);
          assert (max_lvl > 0);
          Some (a, max_lvl - 1, snd_max)
      with Exit -> None

  let conflict_analyze_and_fix confl =
    match confl with
    | C_none -> assert false
    | C_theory dep ->
      let atoms, sz, max_lvl, c_hist =
        Ex.fold_atoms
          (fun ex (acc, sz, max_lvl, c_hist) ->
             match ex with
             | Ex.Literal lit ->
               let a = Types.get_atom lit in
	       let c_hist = List.rev_append a.var.vpremise c_hist in
	       let c_hist = match a.var.reason with
	         | None -> c_hist | Some r -> r:: c_hist
               in
	       if a.var.level = 0 then acc, sz, max_lvl, c_hist
	       else a.neg :: acc, sz + 1, max max_lvl a.var.level, c_hist
             | _ -> assert false (* TODO *)
          ) dep ([], 0, 0, [])
      in
      if atoms == [] || max_lvl == 0 then begin
        (* check_inconsistence_of dep; *)
        report_t_unsat dep
        (* une conjonction de faits unitaires etaient deja unsat *)
      end;
      let name = fresh_dname() in
      let c = make_clause name atoms vraie_form sz false c_hist in
      c.removed <- true;
      let blevel, learnt, history, size = conflict_analyze_aux c max_lvl in
      cancel_until blevel;
      record_learnt_clause ~is_T_learn:false blevel learnt history size

    | C_bool c ->
      let max_lvl = ref 0 in
      let lv = ref [] in
      Vec.iter c.atoms (fun a ->
        max_lvl := max !max_lvl a.var.level;
        lv := a.var :: !lv
      );
      if !max_lvl == 0 then report_b_unsat [c];
      match fixable_with_simple_backjump c !max_lvl !lv with
      | None  ->
        let blevel, learnt, history, size = conflict_analyze_aux c !max_lvl in
        cancel_until blevel;
        record_learnt_clause ~is_T_learn:false blevel learnt history size
      | Some (a, blevel, propag_lvl) ->
        assert (a.neg.is_true);
        cancel_until blevel;
        assert (not a.neg.is_true);
        assert (propag_lvl >= 0 && propag_lvl <= blevel);
        enqueue a propag_lvl (Some c)


  let check_inconsistence_of dep = ()
(*
  try
  let env = ref (Th.empty()) in ();
  Ex.iter_atoms
  (fun atom ->
  let t,_,_ = Th.assume ~cs:true atom.lit (Ex.singleton atom) !env in
  env := t)
  dep;
(* ignore (Th.expensive_processing !env); *)
  assert false
  with Exception.Inconsistent _ -> ()
*)

  exception TopClause
  exception BotClause

  let partial_model () =
    Options.partial_bmodel () &&
      try
        for i = 0 to Vec.size env.clauses - 1 do
          let c = Vec.get env.clauses i in
          try
            for j = 0 to Vec.size c.atoms - 1 do
              if (Vec.get c.atoms j).is_true then raise TopClause
            done;
            raise BotClause
          with TopClause -> ()
        done;
        true
      with BotClause -> false

  let rec propagate_and_stabilize propagator conflictC =
    match propagator () with
    | C_none -> ()
    | (C_bool _ | C_theory _ ) as confl -> (* Conflict *)
      incr conflictC;
      env.conflicts <- env.conflicts + 1;
      if decision_level() = 0 then report_conflict confl;
      conflict_analyze_and_fix confl;
      propagate_and_stabilize propagator conflictC

  let clause_of_dep d fuip =
    let cpt = ref 0 in
    let l =
      Ex.fold_atoms
        (fun e acc ->
          match e with
          | Ex.Literal a ->
            incr cpt;
            (Types.get_atom a).neg :: acc
          | _ -> assert false
        )d []
    in
    fuip :: l, !cpt + 1

  let th_entailed tenv a =
    if Options.no_tcp () then None
    else
      let lit = Types.literal a in
      match Th.query lit tenv with
      | Sig.Yes (d,_) ->
        a.timp <- true;
        Some (clause_of_dep d a)
      | Sig.No  ->
        match Th.query (A.neg lit) tenv with
        | Sig.Yes (d,_) ->
          a.neg.timp <- true;
          Some (clause_of_dep d a.Types.neg)
        | Sig.No -> None

  let search n_of_conflicts n_of_learnts =
    let conflictC = ref 0 in
    env.starts <- env.starts + 1;
    while true do
      propagate_and_stabilize all_propagations conflictC;

      if nb_assigns () = env.nb_init_vars || partial_model () ||
        (Options.lazy_sat () && env.lazy_cnf == []) then
        raise Sat;
      if Options.enable_restarts ()
        && n_of_conflicts >= 0 && !conflictC >= n_of_conflicts then begin
          env.progress_estimate <- progress_estimate();
          cancel_until 0;
          raise Restart
        end;
      if decision_level() = 0 then simplify ();

      if n_of_learnts >= 0 &&
        Vec.size env.learnts - nb_assigns() >= n_of_learnts then
        reduce_db();

      let next = pick_branch_lit () in
      match th_entailed env.tenv next with
      | None ->
        new_decision_level();
        let current_level = decision_level () in
        env.cpt_current_propagations <- 0;
        assert (next.var.level < 0);
        (* eprintf "decide: %a@." Types.pr_atom next; *)
        enqueue next current_level None
      | Some(c,sz) ->
        record_learnt_clause ~is_T_learn:true (decision_level ()) c [] sz
          [@ocaml.ppwarning
              "Issue: BAD decision_level, in particular, if minimal-bj is ON"]
    done

  let check_clause c =
    let b = ref false in
    let atoms = c.atoms in
    for i = 0 to Vec.size atoms - 1 do
      let a = Vec.get atoms i in
      b := !b || a.is_true
    done;
    assert (!b)

  let check_vec vec =
    for i = 0 to Vec.size vec - 1 do check_clause (Vec.get vec i) done

  let check_model () =
    check_vec env.clauses;
    check_vec env.learnts


  let solve () =
    if env.is_unsat then raise (Unsat env.unsat_core);
    let n_of_conflicts = ref (to_float env.restart_first) in
    let n_of_learnts = ref ((to_float (nb_clauses())) *. env.learntsize_factor) in
    try
      while true do
        (try search (to_int !n_of_conflicts) (to_int !n_of_learnts);
         with Restart -> ());
        n_of_conflicts := !n_of_conflicts *. env.restart_inc;
        n_of_learnts   := !n_of_learnts *. env.learntsize_inc;
      done;
    with
      | Sat ->
        (*check_model ();*)
        remove_satisfied env.clauses;
        remove_satisfied env.learnts;
        raise Sat
      | (Unsat cl) as e ->
        (* check_unsat_core cl; *)
        raise e

  exception Trivial

  let partition atoms init =
    let rec partition_aux trues unassigned falses init = function
      | [] -> trues @ unassigned @ falses, init
      | a::r ->
        if a.is_true then
	  if a.var.level = 0 then raise Trivial
	  else (a::trues) @ unassigned @ falses @ r, init
        else if a.neg.is_true then
	  if a.var.level = 0 then
	    partition_aux trues unassigned falses
	      (List.rev_append (a.var.vpremise) init) r
	  else partition_aux trues unassigned (a::falses) init r
        else partition_aux trues (a::unassigned) falses init r
    in
    partition_aux [] [] [] init atoms


  let add_clause f ~cnumber atoms =
    if env.is_unsat then raise (Unsat env.unsat_core);
    (*if not (clause_exists atoms) then XXX TODO *)
    let init_name = string_of_int cnumber in
    let init0 =
      if Options.proof () then
        [make_clause init_name atoms f (List.length atoms) false []]
      else
        [] (* no deps if proofs generation is not enabled *)
    in
    try
      let atoms, init =
        if decision_level () = 0 then
	  let atoms, init = List.fold_left
	    (fun (atoms, init) a ->
	      if a.is_true then raise Trivial;
	      if a.neg.is_true then begin
                if Options.profiling() then Profiling.red true;
	        atoms, (List.rev_append (a.var.vpremise) init)
              end
	      else a::atoms, init
	    ) ([], init0) atoms in
	  List.fast_sort (fun a b -> a.var.vid - b.var.vid) atoms, init
        else partition atoms init0
      in
      let size = List.length atoms in
      match atoms with
        | [] ->
          report_b_unsat init0;

        | a::_::_ ->
          let name = fresh_name () in
          let clause = make_clause name atoms vraie_form size false init in
          attach_clause clause;
          Vec.push env.clauses clause;
          if debug_sat () && verbose () then
            fprintf fmt "[satML] add_clause: %a@." Types.pr_clause clause;

	  if a.neg.is_true then begin
	    let lvl = List.fold_left (fun m a -> max m a.var.level) 0 atoms in
	    cancel_until lvl;
            conflict_analyze_and_fix (C_bool clause)
	  end

        | [a]   ->
          if debug_sat () && verbose () then
            fprintf fmt "[satML] add_atom: %a@." Types.pr_atom a;
          let lvl = a.var.level in
          assert (lvl <> 0);
          begin
            if not (minimal_bj ()) then cancel_until 0
            else if a.is_true || a.neg.is_true then cancel_until (lvl - 1)
          end;
          a.var.vpremise <- init;
          enqueue a 0 None;
          propagate_and_stabilize propagate (ref 0)

    with Trivial ->
      if Options.profiling() then Profiling.elim true


  let update_lazy_cnf ~do_bcp mff ~dec_lvl =
    if Options.lazy_sat () && dec_lvl <= decision_level () then begin
      let s =
        try Util.MI.find dec_lvl env.lvl_ff
        with Not_found -> SFF.empty
      in
      let lz, s =
        MFF.fold (fun ff lz_kd (l, s) ->
          match lz_kd with
          | None ->
            assert (not (MFF.mem ff env.ff_lvl));
            assert (not (SFF.mem ff s));
            env.ff_lvl <- MFF.add ff dec_lvl env.ff_lvl;
            ff :: l, SFF.add ff s
          | Some a ->
            (* TODO for case 'Some a' *)
            assert false

        ) mff (env.lazy_cnf, s)
      in
      env.lazy_cnf <- lz;
      env.lvl_ff <- Util.MI.add dec_lvl s env.lvl_ff;
      if do_bcp then
        propagate_and_stabilize (*theory_propagate_opt*)
          all_propagations (ref 0);
    end

  let new_vars new_v unit_cnf nunit_cnf  =
    match new_v with
    | [] -> unit_cnf, nunit_cnf
    | _ ->
      let tenv0 = env.unit_tenv in
      let nbv, _ = made_vars_info () in
      Vec.grow_to_by_double env.vars nbv;
      Iheap.grow_to_by_double env.order nbv;
      let accu =
        List.fold_left
          (fun ((unit_cnf, nunit_cnf) as accu) v ->
            Vec.set env.vars v.vid v;
            insert_var_order v;
            match th_entailed tenv0 v.pa with
            | None -> accu
            | Some (c, sz) ->
              assert (sz >= 1);
              if sz = 1 then c :: unit_cnf, nunit_cnf
              else unit_cnf, c :: nunit_cnf
                [@ocaml.ppwarning
                    "Issue: BAD decision_level, in particular, if minimal-bj is ON"]
          ) (unit_cnf, nunit_cnf) new_v
      in
      env.nb_init_vars <- nbv;
      Vec.grow_to_by_double env.model nbv;
      accu

  let set_new_proxies proxies =
    env.proxies <- proxies

  let assume unit_cnf nunit_cnf f ~cnumber mff ~dec_lvl =
    begin
      match unit_cnf, nunit_cnf with
      | [], [] -> ()
      | _, _ ->
        let nbc =
          env.nb_init_clauses + List.length unit_cnf + List.length nunit_cnf in
        Vec.grow_to_by_double env.clauses nbc;
        Vec.grow_to_by_double env.learnts nbc;
        env.nb_init_clauses <- nbc;

        List.iter (add_clause f ~cnumber) unit_cnf;
        List.iter (add_clause f ~cnumber) nunit_cnf;

        if verbose () then  begin
          fprintf fmt "%d clauses@." (Vec.size env.clauses);
          fprintf fmt "%d learnts@." (Vec.size env.learnts);
        end
    end;
    (* do it after add clause and before T-propagate, disable bcp*)
    update_lazy_cnf ~do_bcp:false mff ~dec_lvl;
    propagate_and_stabilize all_propagations (ref 0) (* do bcp globally *)

  let exists_in_lazy_cnf f' =
    not (Options.lazy_sat ()) || MFF.mem f' env.ff_lvl

  let boolean_model () =
    let l = ref [] in
    for i = Vec.size env.trail - 1 downto 0 do
      l := (Vec.get env.trail i) :: !l
    done;
    !l

  let theory_assumed () = Th.get_assumed env.tenv

  let current_tbox () = env.tenv
  let set_current_tbox tb = env.tenv <- tb

  let assume_th_elt th_elt =
    assert (decision_level () == 0);
    env.tenv <- Th.assume_th_elt (current_tbox ()) th_elt

  let empty () =
    for i = 0 to Vec.size env.vars - 1 do
      try
        let var = Vec.get env.vars i in
        var.pa.is_true <- false;
        var.na.is_true <- false;
        var.level <- -1;
        var.index <- -1;
        var.reason <- None;
        var.vpremise <- [];
      with Not_found -> ()
    done;
    env.is_unsat <- false;
    env.unsat_core <- None;
    env.clauses <- Vec.make 0 dummy_clause;
    env.learnts <- Vec.make 0 dummy_clause;
    env.clause_inc <- 1.;
    env.var_inc <- 1.;
    env.vars <- Vec.make 0 dummy_var;
    env.qhead <- 0;
    env.simpDB_assigns <- -1;
    env.simpDB_props <- 0;
    env.order <- Iheap.init 0; (* sera mis a jour dans solve *)
    env.progress_estimate <- 0.;
    env.restart_first <- 100;
    env.starts <- 0;
    env.decisions <- 0;
    env.propagations <- 0;
    env.conflicts <- 0;
    env.clauses_literals <- 0;
    env.learnts_literals <- 0;
    env.max_literals <- 0;
    env.tot_literals <- 0;
    env.nb_init_vars <- 0;
    env.nb_init_clauses <- 0;
    env.tenv <- (Th.empty ());
    env.model <- Vec.make 0 dummy_var;
    env.trail <- Vec.make 601 dummy_atom;
    env.trail_lim <- Vec.make 601 (-105);
    env.tenv_queue <- Vec.make 100 (Th.empty ());
    env.tatoms_queue <- Queue.create ();
    env.lazy_cnf <- [];
    Vec.clear env.lazy_cnf_queue;
    env.ff_lvl <- MFF.empty;
    env.lvl_ff <- Util.MI.empty

  let clear () =
    empty ();
    Solver_types.clear ()


  let copy (v : 'a) : 'a = Marshal.from_string (Marshal.to_string v []) 0

  let save () =
    let sv =
      { env = env;
        st_cpt_mk_var = !Solver_types.cpt_mk_var;
        st_ma = !Solver_types.ma }
    in
    copy sv

  let restore { env = s_env; st_cpt_mk_var = st_cpt_mk_var; st_ma = st_ma } =
    env.is_unsat <- s_env.is_unsat;
    env.unsat_core <- s_env.unsat_core;
    env.clauses <- s_env.clauses;
    env.learnts <- s_env.learnts;
    env.clause_inc <- s_env.clause_inc;
    env.var_inc <- s_env.var_inc;
    env.vars <- s_env.vars;
    env.qhead <- s_env.qhead;
    env.simpDB_assigns <- s_env.simpDB_assigns;
    env.simpDB_props <- s_env.simpDB_props;
    env.order <- s_env.order;
    env.progress_estimate <- s_env.progress_estimate;
    env.restart_first <- s_env.restart_first;
    env.starts <- s_env.starts;
    env.decisions <- s_env.decisions;
    env.propagations <- s_env.propagations;
    env.conflicts <- s_env.conflicts;
    env.clauses_literals <- s_env.clauses_literals;
    env.learnts_literals <- s_env.learnts_literals;
    env.max_literals <- s_env.max_literals;
    env.tot_literals <- s_env.tot_literals;
    env.nb_init_vars <- s_env.nb_init_vars;
    env.nb_init_clauses <- s_env.nb_init_clauses;
    env.tenv <- s_env.tenv;
    env.model <- s_env.model;
    env.trail <- s_env.trail;
    env.trail_lim <- s_env.trail_lim;
    env.tenv_queue <- s_env.tenv_queue;
    env.tatoms_queue <- s_env.tatoms_queue;
    env.learntsize_factor <- s_env.learntsize_factor;
    Solver_types.cpt_mk_var := st_cpt_mk_var;
    Solver_types.ma := st_ma


  let known_lazy_formulas () = env.ff_lvl
(*end*)
end
