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

module HS = Hstring
module Sy = Symbols

let src = Logs.Src.create ~doc:"Ac" __MODULE__
module Log = (val Logs.src_log src : Logs.LOG)

module type S = sig

  (* embeded AC semantic values *)
  type r

  (* extracted AC semantic values *)
  type t = r Sig.ac

  (* builds an embeded semantic value from an AC term *)
  val make : Expr.t -> r * Expr.t list

  (* Tells whether the given symbol is AC. *)
  val is_mine_symb : Sy.t -> bool

  (* compares two AC semantic values *)
  val compare : t -> t -> int

  (* tests if two values are equal (using tags) *)
  val equal : t -> t -> bool

  (* hash function for ac values *)
  val hash : t -> int

  (* returns the type infos of the given term *)
  val type_info : t -> Ty.t

  (* prints the AC semantic value *)
  val print : Format.formatter -> t -> unit

  (* returns the leaves of the given AC semantic value *)
  val leaves : t -> r list

  (* replaces the first argument by the second one in the given AC value *)
  val subst : r -> r -> t -> r

  (* add flatten the 2nd arg w.r.t HS.t, add it to the given list
     and compact the result *)
  val add : Sy.t -> r * int -> (r * int) list -> (r * int) list

  val fully_interpreted : Sy.t -> bool

  val abstract_selectors : t -> (r * r) list -> r * (r * r) list

  val compact : (r * int) list -> (r * int) list

  val assign_value :
    r -> r list -> (Expr.t * r) list -> (Expr.t * bool) option

end

module Make (X : Sig.X) = struct

  open Sig

  type r = X.r

  type t = X.r Sig.ac

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let print_x fmt v =
      match X.leaves v with
      | [w] when X.equal v w -> Format.fprintf fmt "%a" X.print v
      | _ -> Format.fprintf fmt "(%a)" X.print v


    let rec pr_elt sep fmt (e,n) =
      assert (n >=0);
      if n = 0 then ()
      else Format.fprintf fmt "%s%a%a" sep print_x e (pr_elt sep) (e,n-1)

    let pr_xs sep fmt = function
      | [] -> assert false
      | (p,n)::l  ->
        Format.fprintf fmt "%a" print_x p;
        List.iter (Format.fprintf fmt "%a" (pr_elt sep))((p,n-1)::l)

    let print fmt { h; l; _ } =
      if Sy.equal h (Sy.Op Sy.Mult) then
        Format.fprintf fmt "%a" (pr_xs "'*'") l
      else
        Format.fprintf fmt "%a(%a)" Sy.print h (pr_xs ",") l

    let assert_compare a b c1 c2 =
      assert (
        if not (c1 = 0 && c2 = 0 ||
                c1 < 0 && c2 > 0 ||
                c1 > 0 && c2 < 0) then begin
          print_err
            "Ac.compare:@ %a vs %a@  = %d@ \
             But@ \
             Ac.compare:@ %a vs %a@  = %d"
            print a print b c1 print b print a c2;
          false
        end
        else true
      )

    let subst p v tm =
      if Options.get_debug_ac () then
        print_dbg
          "[ac] subst %a by %a in %a"
          X.print p X.print v X.print (X.ac_embed tm)

  end
  (*BISECT-IGNORE-END*)

  let print = Debug.print

  let flatten h (r,m) acc =
    match X.ac_extract r with
    | Some ac when Sy.equal ac.h h ->
      List.fold_left (fun z (e,n) -> (e,m * n) :: z) acc ac.l
    | _ -> (r,m) :: acc

  let sort = List.fast_sort (fun (x,_) (y,_) -> X.str_cmp x y)

  let compact xs =
    let rec f acc = function
      | [] -> acc
      | [(x,n)] -> (x,n) :: acc
      | (x,n) :: (y,m) :: r ->
        if X.equal x y then f acc ((x,n+m) :: r)
        else f ((x,n)::acc) ((y,m) :: r)
    in
    f [] (sort xs) (* increasing order - f's result in a decreasing order*)

  let fold_flatten sy f =
    List.fold_left (fun z (rt,n) -> flatten sy ((f rt),n) z) []

  let is_other_ac_symbol sy r =
    match X.ac_extract r with
    | Some ac -> not (Sy.equal sy ac.h)
    | None -> false

  (* This implements a variant of the term abstraction process described in
     section 6 of the AC(X) paper [1].

     The abstraction process given in the paper requires to abstract all AC
     symbols appearing in a non-AC context, but the implementation does not
     know about the context at the time the abstraction is performed (note that
     rules Abstract1 and Abstract2 are concerned with *equations* while the
     abstraction process here occurs at the time of building semantic values,
     which is earlier). Further, the implementation seems to implicitly rely on
     term ordering (older terms are ordered before newer terms, so in
     particular subterms are always smaller than terms that contains them) to
     cheaply prevent loops rather than introducing all the abstracted variables
     that the theoretical presentation in the paper would require.

     So the implementation below of the Abstract2 rules deviates from the
     presentation in the paper to accomodate those differences, globally,
     between the implementation and theoretical description of AC(X).

     More precisely, `abstract2` will abstract terms that *contain* AC leaves
     when they appear as argument of an AC symbol. This ensures that AC terms
     satisfy the T_AC definition from page 22 of the paper, although
     correctness of the corresponding abstraction process has not been proven.
     See also https://github.com/OCamlPro/alt-ergo/issues/989

     [1]: Canonized Rewriting and Ground AC Completion Modulo Shostak Theories:
            Design and Implementation.
          Sylvain Conchon, Evelyne Contejean, Mohamed Iguernelala.
          lmcs:1034 - Logical Methods in Computer Science, September 14, 2012,
            Volume 8, Issue 3.
          doi:10.2168/LMCS-8(3:16)2012
          https://arxiv.org/pdf/1207.3262.pdf *)
  let abstract2 sy t r acc =
    if List.exists (is_other_ac_symbol sy) (X.leaves r) then
      match X.ac_extract r, Expr.term_view t with
      | Some ac, { f = Name { hs; kind = Ac; _ } ; xs; ty; _ } ->
        (* It should have been abstracted when building [r] *)
        assert (not (Sy.equal sy ac.h));
        let aro_sy =
          Sy.name ~ns:Internal @@ Uid.do_mangle (fun s -> Some ("@" ^ s)) hs
        in
        let aro_t = Expr.mk_term aro_sy xs ty  in
        let eq = Expr.mk_eq ~iff:false aro_t t in
        X.term_embed aro_t, eq::acc
      | Some ac, { f = Op Mult; xs; ty; _ } ->
        (* It should have been abstracted when building [r] *)
        assert (not (Sy.equal sy ac.h));
        let aro_sy = Sy.name ~ns:Internal @@ Uid.of_string "@*" in
        let aro_t = Expr.mk_term aro_sy xs ty  in
        let eq = Expr.mk_eq ~iff:false aro_t t in
        X.term_embed aro_t, eq::acc
      | _, { ty; _ } ->
        let k = Expr.fresh_ac_name ty in
        let eq = Expr.mk_eq ~iff:false k t in
        X.term_embed k, eq::acc

    else
      r, acc

  let make t =
    match Expr.term_view t with
    | { Expr.f = sy; xs = [a;b]; ty; _ } when Sy.is_ac sy ->
      let ra, ctx1 = X.make a in
      let rb, ctx2 = X.make b in
      let ra, ctx = abstract2 sy a ra (ctx1 @ ctx2) in
      let rb, ctx = abstract2 sy b rb ctx in
      let rxs = [ ra,1 ; rb,1 ] in
      X.ac_embed {h=sy; l=compact (fold_flatten sy (fun x -> x) rxs); t=ty;
                  distribute = true},
      ctx
    | {xs; _} ->
      Printer.print_err
        "AC theory expects only terms with 2 arguments; \
         got %i (%a)." (List.length xs) Expr.print_list xs;
      assert false

  let is_mine_symb sy = (not @@ Options.get_no_ac ()) && Sy.is_ac sy

  let type_info { t = ty; _ } = ty

  let leaves { l; _ } = List.fold_left (fun z (a,_) -> (X.leaves a) @ z)[] l

  let rec mset_cmp = function
    |  []   ,  []   ->  0
    |  []   , _::_  -> -1
    | _::_  ,  []   ->  1
    | (a,m)::r  , (b,n)::s  ->
      let c = X.str_cmp a b in
      if c <> 0 then c
      else
        let c = m - n in
        if c <> 0 then c
        else mset_cmp(r,s)

  let size = List.fold_left (fun z (_,n) -> z + n) 0


  module SX = Set.Make(struct type t=r let compare = X.str_cmp end)

  let leaves_list l =
    let l =
      List.fold_left
        (fun acc (x,n) ->
           let sx = List.fold_right SX.add (X.leaves x) SX.empty in
           SX.fold (fun lv acc -> (lv, n) :: acc)  sx acc
        ) []l
    in
    compact l


  (* x et y are sorted in a decreasing order *)
  let compare { h = f; l = x; _ } { h = g; l = y; _ } =
    let c = Sy.compare f g in
    if c <> 0 then c
    else
      let llx = leaves_list x in
      let lly = leaves_list y in
      let c = size llx - size lly in
      if c <> 0 then c
      else
        let c = mset_cmp (leaves_list x , leaves_list y) in
        if c <> 0 then c
        else mset_cmp (x , y)


  let compare a b =
    let c1 = compare a b in
    let c2 = compare b a in
    Debug.assert_compare a b c1 c2;
    c1

  (*
    let mset_compare ord {h=f ; l=x} {h=g ; l=y} =
    let c = Sy.compare f g in
    if c <> 0 then c
    else assert false
  *)

  let equal { h = f; l = lx; _ } { h = g; l = ly; _ } =
    Sy.equal f g &&
    try List.for_all2 (fun (x, m) (y, n) -> m = n && X.equal x y) lx ly
    with Invalid_argument _ -> false

  let hash { h = f; l; t; _ } =
    let acc = Sy.hash f + 19 * Ty.hash t in
    abs (List.fold_left (fun acc (x, y) -> acc + 19 * (X.hash x + y)) acc l)


  let subst p v ({ h; l; _ } as tm)  =
    Options.exec_thread_yield ();
    Timers.with_timer Timers.M_AC Timers.F_subst @@ fun () ->
    Debug.subst p v tm;
    X.color {tm with l=compact (fold_flatten h (X.subst p v) l)}

  let add h arg arg_l =
    Timers.with_timer Timers.M_AC Timers.F_add @@ fun () ->
    compact (flatten h arg arg_l)

  let fully_interpreted _ = true

  let abstract_selectors ({ l = args; _ } as ac) acc =
    let args, acc =
      List.fold_left
        (fun (args, acc) (r, i) ->
           let r, acc = X.abstract_selectors r acc in
           (r, i) :: args, acc
        )([],acc) args
    in
    let xac = X.ac_embed {ac with l = compact args} in
    xac, acc

  let assign_value _r _distincts _eq =
    None
    (* Models Gen for AC symbols is not done yet.  The code below would
       work, but the way models are currently generated makes the result
       of 'assign_value' not visible in the printed models, because we
       inspect the 'make : Expr.t -> X.r' to extract the
       model. Unfortunately, some AC expressions introduced by the AC(X)
       algorithm don't have their corresponding terms and don't appear
       in the 'make' map *)

    (*
    let is_fresh (r, _) =
    match X.term_extract r with
    | Some t, true -> Expr.is_fresh t
    | _ -> false

  let assign_value =
    let cache = ref Ty.Map.empty in
    let module SX = Set.Make(struct type t=r let compare = X.hash_cmp end) in
    let exception Found of Expr.t in
    fun r distincts eq ->
      if List.exists (fun (t,(_:r)) -> Expr.is_model_term t) eq then
        None
      else
        (*match X.ac_extract r with
        | None -> assert false
        | Some ac ->
          if List.for_all is_fresh ac.Sig.l then None
            else*) begin
            let ty = X.type_info r in
            let q = ref (Queue.create ()) in
            try
              let qc = Ty.Map.find ty !cache in
              let sdist =
                List.fold_left (fun s r -> SX.add r s) SX.empty distincts in
              Queue.iter
                (fun (kt, kx) ->
                   if not (SX.mem kx sdist) then raise (Found kt)
                )qc;
              q := qc;
              raise Not_found
            with
            | Found kt ->
              Some (kt , true)
            | Not_found ->
              let fresh = Expr.fresh_name ty in
              Queue.push (fresh, X.term_embed fresh) !q;
              cache := Ty.Map.add ty !q !cache;
              Some (fresh , false)
          end
*)
end
