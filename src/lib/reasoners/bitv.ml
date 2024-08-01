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

module Sy = Symbols
module E = Expr

type sort_var = A | B | C
(* The variables used by the bitvector solver can be split into three
   categories that have associated invariants.

   These invariants are recalled in the functions that make use of them, but the
   outline is as follows. The solver works with *partitioned multi-equations*.
   A partitioned multi-equation is an equality: X == e1 = e2 = ... = en
   where X is a term (or an alien) and e1, e2, ..., en are terms in the
   bitvector algebra, that may contain variables.

   The solver maintains a system of partitioned multi-equations. In the system,
   there is at most one multi-equation for each variable X (while building the
   system, the multi-equations are initially split into binary equations [X = e]
   where this restriction does not apply technically; in this representation,
   all the right-hand side of equalities involving the same left-hand side
   should be treated as part of the same multi-equation).

   Then, we maintain the invariants that, within the system:

   - Each A variable appears at most once (this is used to represent portions
      of a term that are irrelevant to a particular constraint)

   - Each B variable appears in at most one *equation* (i.e. a single term
      [ei]), but appears *multiple times* in that equation (never only once)

   - Each C variable appears at most once in each multi-equation, but appears
      in several (more precisely, two) distinct multi-equations. *)

let pp_sort ppf = function
  | A -> Format.fprintf ppf "a"
  | B -> Format.fprintf ppf "b"
  | C -> Format.fprintf ppf "c"

(** The [tvar] and [defn] type are used to implement Tarjan's Union-Find
    algorithm with path compression but not union-by-rank.

    Note that [tvar] and [defn] values must not be created directly: instead,
    call the [s_var] and [s_cte] helpers. This is important due to the use of
    physical equality in [union]. *)
type tvar = { mutable defn : defn }

and defn =
  | Droot of {
      id : int ;
      (** Variable identifier. This is [-n] for the negation of the variable
          with identifier [n] (and in particular never [0]).  *)
      neg : tvar ;
      (** Negated variable. While this root is live, the [neg] field is
          guaranteed to be another [Droot] with negated identifier. Once the
          [Droot] is merged with an equivalence class, the [neg] field is
          merged with the negated class. *)
      sorte : sort_var ;
      (** The sort of this variable. See the type definition for {!sort_var} for
          details. *)
    }
  | Dcte of Z.t * int
  (** A [Dcte] is a variable that is forced to be equal to the specified integer
      representation in bits. The second argument is the bit width. *)
  | Dlink of tvar
  (** A [Dlink] is a defined variable. All the [Dlink] should be followed to
      arrive either at an unconstrained variable ([Droot]) or a constant
      ([Dcte]).

      [Dlink] elements are only created when calling [build_solution], they
      should not occur before that and hence the [Dlink] case can be ignored in
      the helper functions below. *)

let rec pp_defn ppf = function
  | Droot { id; sorte; _ } -> Fmt.pf ppf "%a_%d" pp_sort sorte id
  | Dcte (b, w) -> Fmt.pf ppf "%s" (Z.format ("%0" ^ string_of_int w ^ "b") b)
  | Dlink tv -> pp_tvar ppf tv

and pp_tvar ppf { defn } = pp_defn ppf defn

let equal_tvar v1 v2 =
  match v1.defn, v2.defn with
  | Droot _, _ | _, Droot _ -> v1 == v2
  | Dcte (n1, w1), Dcte (n2, w2) -> w1 = w2 && Z.equal n1 n2
  | _ ->
    (* [equal_tvar] should only be used before solving, i.e. before any unions
       are made, and so there should be no [Dlink]. *)
    assert false

(** [s_var sorte] creates a new unconstrained variable with sorte [sorte].
    The negated version of the variable is also created eagerly. *)
let s_var =
  let cnt = ref 0 in
  fun sorte ->
    let id = incr cnt; !cnt in
    let rec x = { defn = Droot { id; sorte; neg = neg } }
    and neg = { defn = Droot { id = -id; sorte; neg = x }} in
    x

let s_cte n w = { defn = Dcte (Z.extract n 0 w, w) }

let negate_tvar = function
  | { defn = Droot { neg; _ }; _ } -> neg
  | { defn = Dcte (n, w); _ } -> s_cte (Z.lognot n) w
  | { defn = Dlink _; _ } -> assert false

(** Follow the defined variables [Dlink] and return the class representative as
    either a constrained [Dcte] or unconstrained [Droot] variable.

    Ensures: the resulting [tvar] always has a [Droot] or [Dcte] as [defn],
      never a [Dlink]. *)
let rec find v =
  match v.defn with
  | Dcte _ | Droot _ -> v
  | Dlink v' ->
    let v' = find v' in
    v.defn <- Dlink v';
    v'

(** Raises [Util.Unsolvable] if distinct constants are merged, or a variable is
    merged with its negation. *)
let union v1 v2 =
  let v1 = find v1 and v2 = find v2 in
  if v1 == v2 then () else
    match v1.defn, v2.defn with
    | Dlink _, _ | _, Dlink _ ->
      (* [find] invariant *)
      assert false
    | Dcte (n1, w1), Dcte (n2, w2) ->
      if w1 = w2 && Z.equal n1 n2 then (
        (* We don't require physical equality of [Dcte] constructors, but we
           still merge the corresponding nodes. *)
        v1.defn <- Dlink v2;
      ) else
        raise Util.Unsolvable
    | Droot r1, Droot r2 ->
      if r1.neg == v2 then raise Util.Unsolvable
      else (
        v1.defn <- Dlink v2;
        r1.neg.defn <- Dlink r2.neg;
      )
    | Droot r1, Dcte (n, w) ->
      v1.defn <- Dlink v2;
      r1.neg.defn <- Dlink (s_cte (Z.lognot n) w)
    | Dcte (n, w), Droot r2 ->
      v2.defn <- Dlink v1;
      r2.neg.defn <- Dlink (s_cte (Z.lognot n) w)

type 'a alpha_term = {
  bv : 'a;
  sz : int;
}

let pp_alpha_term pp ppf { bv; sz } =
  Fmt.pf ppf "%a[%d]" pp bv sz

let equal_alpha_term eq { bv = bv1; sz = sz1 } {bv = bv2; sz = sz2 } =
  Int.equal sz1 sz2 && eq bv1 bv2

let compare_alpha_term cmp a1 a2 =
  if a1.sz <> a2.sz then a1.sz - a2.sz else cmp a1.bv a2.bv

let hash_alpha_term hash { bv; sz } = sz + hash bv

(** The ['a signed] type represents possibly negated values of type ['a]. It is
    used for [bvnot] at the leaves ([Other] and [Ext] below). *)
type 'a signed = { value : 'a ; negated : bool }

let pp_signed pp ppf { value; negated } =
  if negated then Fmt.pf ppf "@[<1>(bvnot %a@])" pp value else pp ppf value

let equal_signed eq s1 s2 =
  eq s1.value s2.value && Bool.equal s1.negated s2.negated

let compare_signed cmp s1 s2 =
  let c = cmp s1.value s2.value in
  if c <> 0 then c else Bool.compare s1.negated s2.negated

let hash_signed hash { value; negated } =
  if negated then 3 * hash value else hash value

let negate_signed ({ negated; _ } as signed) =
  { signed with negated = not negated }

let positive value = { value; negated = false }

let negative value = { value; negated = true }

type 'a simple_term_aux =
  | Cte of Z.t
  | Other of 'a signed
  | Ext of 'a signed * int * int * int (*// id * size * i * j //*)

let equal_simple_term_aux eq l r =
  match l, r with
  | Cte b1, Cte b2 -> Z.equal b1 b2
  | Other o1, Other o2 -> equal_signed eq o1 o2
  | Ext (o1, s1, i1, j1), Ext (o2, s2, i2, j2) ->
    i1 = i2 && j1 = j2 && s1 = s2 && equal_signed eq o1 o2
  | _, _ -> false

let compare_simple_term_aux cmp st1 st2 =
  match st1, st2 with
  | Cte b1, Cte b2 -> Z.compare b1 b2
  | Cte _, _ -> -1
  | _, Cte _ -> 1

  | Other t1 , Other t2 -> compare_signed cmp t1 t2
  | _ , Other _ -> -1
  | Other _ , _ -> 1

  | Ext(t1,s1,i1,_) , Ext(t2,s2,i2,_) ->
    let c1 = compare s1 s2 in
    if c1<>0 then c1
    else let c2 = compare i1 i2 in
      if c2 <> 0 then c2 else compare_signed cmp t1 t2

let hash_simple_term_aux hash = function
  | Cte b -> 11 * Z.hash b
  | Other x -> 17 * hash_signed hash x
  | Ext (x, a, b, c) ->
    hash_signed hash x + 19 * (a + b + c)

let negate_simple_term_aux sz = function
  | Cte b -> Cte (Z.extract (Z.lognot b) 0 sz)
  | Other o -> Other (negate_signed o)
  | Ext (o, sz, i, j) -> Ext (negate_signed o, sz, i, j)

type 'a simple_term = ('a simple_term_aux) alpha_term

let equal_simple_term eq = equal_alpha_term (equal_simple_term_aux eq)

let compare_simple_term cmp = compare_alpha_term (compare_simple_term_aux cmp)

let hash_simple_term hash = hash_alpha_term (hash_simple_term_aux hash)

let negate_simple_term st = { st with bv = negate_simple_term_aux st.sz st.bv }

type 'a abstract = 'a simple_term list

let rec to_Z_opt_aux acc = function
  | [] -> Some acc
  | { bv = Cte n; sz } :: sts ->
    to_Z_opt_aux Z.((acc lsl sz) + n) sts
  | _ -> None

let to_Z_opt r = to_Z_opt_aux Z.zero r

let int2bv_const n z =
  [ { bv = Cte (Z.extract z 0 n) ; sz = n } ]

let equal_abstract eq = Compat.List.equal (equal_simple_term eq)

let compare_abstract cmp = Compat.List.compare (compare_simple_term cmp)

let hash_abstract hash =
  List.fold_left (fun acc e -> acc + 19 * hash_simple_term hash e) 19

let negate_abstract xs = List.map negate_simple_term xs

let lognot = negate_abstract

type solver_simple_term = tvar alpha_term

let pp_solver_simple_term = pp_alpha_term pp_tvar

let negate_solver_simple_term (st : solver_simple_term) : solver_simple_term =
  { st with bv = negate_tvar st.bv }

type bitv = solver_simple_term list

let pp_bitv = Fmt.(list ~sep:(any " @@@ ") pp_solver_simple_term |> box)

let fresh_bitv genre sz : bitv =
  if sz <= 0 then [] else [ { bv = s_var genre ; sz } ]

let negate_bitv : bitv -> bitv = List.map negate_solver_simple_term

let extract_st i j { bv; sz } =
  if sz = j - i + 1 then
    { bv ; sz }
  else
    match bv with
    | Cte b -> { bv = Cte (Z.extract b i (j - i + 1)); sz = j - i + 1 }
    | Other r -> { bv = Ext (r, sz, i, j) ; sz = j - i + 1 }
    | Ext (r, sz, k, _) ->
      { bv = Ext (r, sz, i + k, j + k) ; sz = j - i + 1 }

(* extract [i..j] from a composition of size [size]

    an element of size [sz] at the head of the composition contains the bits
    [size - 1 .. size - sz] inclusive *)
let rec extract size i j = function
  | [] ->
    (* We can't extract from a bv of length 0! *)
    assert false
  | [ st ] ->
    assert (st.sz = size);
    [ extract_st i j st ]
  | { sz; _ } :: sts when j < size - sz ->
    extract (size - sz) i j sts
  | ({ sz; _ } as st) :: _ when i >= size - sz ->
    [ extract_st (i - (size - sz)) (j - (size - sz)) st ]
  | ({ sz; _ } as st) :: sts ->
    extract_st 0 (j - (size - sz)) st ::
    extract (size - sz) i (size - sz - 1) sts

(* [repeat n b] concatenates [n] copies of [b] *)
let repeat n b =
  assert (n > 0);
  let rec loop b n acc =
    if n = 0 then acc
    else loop b (n - 1) (b @ acc)
  in
  loop b (n - 1) b

(* [sign_extend n sts] is [concat (repeat n (sign sts)) sts]. *)
let sign_extend n sts =
  match n, sts with
  | _, [] -> assert false
  | 0, sts -> sts
  | n, ({ sz; bv } as st) :: sts ->
    match bv with
    | Cte b ->
      int2bv_const (n + sz) (Z.signed_extract b 0 sz) @ sts
    | _ ->
      List.rev_append
        (repeat n [ extract_st (sz - 1) (sz - 1) st ])
        (st :: sts)

module type ALIEN = sig
  include Sig.X
  val embed : r abstract -> r
  val extract : r -> (r abstract) option
end

module Shostak(X : ALIEN) = struct

  type t = X.r abstract
  type r = X.r

  let name = "bitv"

  let timer = Timers.M_Bitv

  let is_mine_symb sy =
    match sy with
    | Sy.Bitv _
    | Op (
        Concat | Extract _ | Sign_extend _ | Repeat _
        | BV2Nat
        | BVnot | BVand | BVor | BVxor
        | BVadd | BVsub | BVmul | BVudiv | BVurem
        | BVshl | BVlshr)
      -> true
    | _ -> false

  let embed r =
    match X.extract r with
    | None ->
      begin
        match X.type_info r with
        | Ty.Tbitv n -> [{bv = Other (positive r) ; sz = n}]
        | _  -> assert false
      end
    | Some b -> b

  module Canon = struct
    type 'a view_descr =
      | Vcte of Z.t
      | Vother of 'a
      | Vextract of 'a * int * int
      | Vconcat of 'a * 'a
      | Vsign_extend of int * 'a
      | Vrepeat of int * 'a
      | Vnot of 'a

    type 'a view = { descr : 'a view_descr ; size : int }

    let view t =
      match E.term_view t with
      | { f = Bitv (_, s); ty = Tbitv size; _ } ->
        { descr = Vcte s; size }
      | { f = Op Concat; xs = [ t1; t2 ]; ty = Tbitv size; _ } ->
        { descr = Vconcat (t1, t2); size }
      | { f = Op (Sign_extend n) ; xs = [ t ] ; ty = Tbitv size; _ } ->
        { descr = Vsign_extend (n, t); size }
      | { f = Op (Repeat n) ; xs = [ t ] ; ty = Tbitv size; _ } ->
        { descr = Vrepeat (n, t) ; size }
      | { f = Op Extract (i, j); xs = [ t' ]; ty = Tbitv size; _ } ->
        assert (size = j - i + 1);
        { descr = Vextract (t', i, j); size }
      | { f = Op BVnot; xs = [ t ]; ty = Tbitv size; _ } ->
        { descr = Vnot t; size }
      | { ty = Tbitv size; _ } ->
        { descr = Vother t; size }
      | _ -> assert false

    let run ctx f = f ctx
    let (let*) x f ctx =
      let x, ctx = x ctx in
      f x ctx
    let ret x ctx = x, ctx
    let (and*) x y =
      let* x = x in
      let* y = y in
      ret (x, y)
    let (let+) x f ctx =
      let x, ctx = x ctx in
      f x, ctx
    let (and+) = (and*)

    let other ~neg t _sz ctx =
      let r, ctx' =
        match E.term_view t with
        | { f = Op (
            BVand | BVor | BVxor
            | BVadd | BVsub | BVmul | BVudiv | BVurem
            | BVshl | BVlshr
          ); _ } ->
          X.term_embed t, []
        | _ -> X.make t
      in
      let ctx = List.rev_append ctx' ctx in
      let bv = embed r in
      if neg then negate_abstract bv, ctx else bv, ctx

    let normalize_st st =
      match st.bv with
      | Ext (o, sz, i, j) when sz = j - i + 1 ->
        assert (sz = st.sz && i = 0);
        { st with bv = Other o }
      | _ -> st

    let rec normalize = function
      | [] -> []
      | [s] -> [normalize_st s]
      | s :: (t :: ts as tts) ->
        begin match s.bv, t.bv with
          | Cte bs, Cte bt ->
            normalize @@
            { bv = Cte Z.(bs lsl t.sz + bt); sz = s.sz + t.sz } :: ts
          | Ext (d1, ds, i, j), Ext (d2, _, k, l)
            when equal_signed X.equal d1 d2 && l = i - 1 ->
            let d = { bv = Ext (d1, ds, k, j); sz = s.sz + t.sz } in
            if k = 0 then normalize_st d :: normalize ts
            else normalize (d :: ts)
          | _ -> normalize_st s :: normalize tts
        end

    let rec make ~neg t = vmake ~neg (view t)
    and vextract ~neg i j tv =
      let size = j - i + 1 in
      match tv.descr with
      | Vcte z ->
        vmake ~neg { descr = Vcte (Z.extract z i size); size }
      | Vother t ->
        let+ o = other ~neg t tv.size in
        extract tv.size i j o
      | Vextract (t'', k, _) ->
        vmake ~neg { descr = Vextract (t'', i + k, j + k); size }
      | Vconcat (u, v) ->
        let vu = view u and vv = view v in
        if j < vv.size then
          vextract ~neg i j vv
        else if i >= vv.size then
          vextract ~neg (i - vv.size) (j - vv.size) vu
        else
          let+ u = vextract ~neg 0 (j - vv.size) vu
          and+ v = vextract ~neg i (vv.size - 1) vv
          in u @ v
      | Vsign_extend (_, u) ->
        let vu = view u in
        if j < vu.size then
          (* extraction from the original vector *)
          vextract ~neg i j vu
        else if i >= vu.size then
          (* extraction from the repeated sign part *)
          let+ sgn = vextract ~neg (vu.size - 1) (vu.size - 1) vu in
          repeat size sgn
        else
          (* extraction from both repeated sign and original vector *)
          let+ u = vextract ~neg i (vu.size - 1) vu in
          sign_extend (j - vu.size + 1) u
      | Vrepeat (_, u) ->
        let vu = view u in
        (* i = ib * vu.size + il
           j = jb * vu.size + jl *)
        let ib = i / vu.size and jb = j / vu.size in
        let il = i mod vu.size and jl = j mod vu.size in
        if ib = jb then (
          (* extraction from within a single repetition *)
          assert (il <= jl);
          vextract ~neg il jl vu
        ) else
          (* extraction across consecutive repetitions *)
          let+ u = vmake ~neg vu in
          let suffix =
            if il = 0 then []
            else extract vu.size il (vu.size - 1) u
          and prefix =
            if jl = 0 then []
            else extract vu.size 0 jl u
          in
          prefix @ repeat (jb - ib - 1) u @ suffix
      | Vnot t ->
        vextract ~neg:(not neg) i j (view t)
    and vmake ~neg tv ctx =
      match tv.descr with
      | Vcte z ->
        let z = if neg then Z.lognot z else z in
        int2bv_const tv.size z, ctx
      | Vother t -> other ~neg t tv.size ctx
      | Vextract (t', i, j) ->
        run ctx @@ vextract ~neg i j (view t')
      | Vsign_extend (n, t) ->
        run ctx @@
        let+ r = make ~neg t in
        let sz = tv.size - n in
        let b = extract sz (sz - 1) (sz - 1) r in
        repeat n b @ r
      | Vrepeat (n, t) ->
        run ctx @@
        let+ r = make ~neg t in
        repeat n r
      | Vconcat (t1, t2) ->
        run ctx @@
        let+ t1 = make ~neg t1 and+ t2 = make ~neg t2 in
        t1 @ t2
      | Vnot t ->
        run ctx @@ make ~neg:(not neg) t

    let make t =
      let r, ctx = make ~neg:false t [] in
      normalize r, ctx
  end

  (*BISECT-IGNORE-BEGIN*)
  module Debug = struct
    open Printer

    let print fmt ast =
      let open Format in
      match ast.bv with
      | Cte b ->
        fprintf fmt "%s[%d]"
          (Z.format ("%0" ^ string_of_int ast.sz ^ "b") b)
          ast.sz
      | Other t -> fprintf fmt "%a[%d]" (pp_signed X.print) t ast.sz
      | Ext (t,sz,i,j) ->
        fprintf fmt "%a[%d]" (pp_signed X.print) t sz;
        fprintf fmt "<%d,%d>" i j

    let print_X ppf ast =
      Format.fprintf ppf "%a[%d]" X.print ast.bv ast.sz

    let print_C_ast fmt = function
        [] -> assert false
      | x::l -> print fmt x; List.iter (Format.fprintf fmt " @@ %a" print) l

    let print_sliced_sys l =
      let print fmt (a,b) =
        Format.fprintf fmt " %a == %a@ " print a print b
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"slicing"
          "%a" (pp_list_no_space print) l

    let print_c_solve_res l =
      let print fmt (a,b) =
        Format.fprintf fmt " %a == %a@ " print_X a pp_bitv b
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"c_solve"
          "(map)c_solve :@ %a" (pp_list_no_space print) l

    let print_partition_res l =
      let print fmt (t,cte_l) =
        Format.fprintf fmt " %a%a@ " print_X t
          (fun fmt ->
             List.iter (fun l' -> Format.fprintf fmt " == %a" pp_bitv l'))
          cte_l
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"partition"
          "%a" (pp_list_no_space print) l

    let print_final_solution l =
      let print fmt (a,value) =
        Format.fprintf fmt " %a = %a@ " print_X a print_C_ast value
      in
      if Options.get_debug_bitv () then
        Printer.print_dbg
          ~module_name:"Bitv"
          ~function_name:"solution"
          "%a" (pp_list_no_space print) l
  end
  (*BISECT-IGNORE-END*)

  module Solver = struct

    exception Valid

    let add elt l =
      if List.exists (equal_signed X.equal elt) l then l else elt::l

    let get_vars = List.fold_left
        (fun ac st -> match st.bv with
           |Other v |Ext(v,_,_,_) -> add v ac  |_ -> ac )[]

    (* [st_slice st siz] splits the simple term [st] in two parts, the first of
       which has size |siz|.

       If [st] is [[b0; ..; bn]] then [st_slice st size] is [(x, y)] where:

       - [x] is [[b0; ..; b(siz-1)]]
       - [y] is [[b(siz); ..; bn]] *)
    let st_slice st siz =
      let siz_bis = st.sz - siz in match st.bv with
      |Cte b ->
        {bv = Cte (Z.extract b siz_bis siz); sz = siz},
        {bv = Cte (Z.extract b 0 siz_bis) ; sz = siz_bis}
      |Other x ->
        let s1 = Ext(x,st.sz, siz_bis, st.sz - 1) in
        let s2 = Ext(x,st.sz, 0, siz_bis - 1) in
        {bv = s1 ; sz = siz},{bv = s2 ; sz = siz_bis}
      |Ext(x,s,p,q) ->
        let s1 = Ext(x,s,p+siz_bis,q) in
        let s2 = Ext(x,s,p,p+siz_bis-1) in
        {bv = s1 ; sz = siz},{bv = s2 ; sz = siz_bis}

    (* [slice t u] transforms the equality [t = u] between abstract terms (i.e.
       concatenations of simple terms) into an equivalent conjunction of
       equalities between simple terms.

       Requires: [t] and [u] must have the same total size.
       Ensures: there are no duplicates in the result (in particular, [x = y]
                and [y = x] cannot be both present)
       Ensures: there are no trivial equalities [x = x] in the result. *)

    let equal_pair_simple_term (a1, b1) (a2, b2) =
      let eq = equal_simple_term X.equal in
      eq a1 a2 && eq b1 b2

    let slice t u  =
      let f_add (s1,s2) acc =
        let b =
          equal_simple_term X.equal s1 s2
          || List.exists (equal_pair_simple_term (s1,s2)) acc
          || List.exists (equal_pair_simple_term (s2,s1)) acc
        in
        if b then acc else (s1,s2)::acc
      in let rec f_rec acc = function
          |[],[] | _,[] | [],_ -> assert false
          |[s1],[s2] ->if s1.sz<>s2.sz then assert false else f_add (s1,s2) acc
          |s1::r1,s2::r2  ->
            if s1.sz = s2.sz then f_rec (f_add (s1,s2) acc) (r1,r2)
            else begin
              if s1.sz > s2.sz then
                let (s11,s12) = st_slice s1 s2.sz
                in f_rec (f_add (s11,s2) acc) (s12::r1,r2)
              else
                let (s21,s22) = st_slice s2 s1.sz
                in f_rec (f_add (s1,s21) acc) (r1,s22::r2)
            end
      in f_rec [] (t,u)

    (* Orient the equality [b = r] where [b] is a bitvector constant and [r] is
       an uninterpreted ("Other") term, possibly negated. *)
    let cte_vs_other bol r sz =
      let bol = if r.negated then Z.lognot bol else bol in
      { bv = r.value; sz } , [{bv = s_cte bol sz ; sz }]

    (* Orient the equality [b = xt[s_xt]^{i,j}] where [b] is a bitvector
       constant and [xt] is uninterpreted of size [s_xt], possibly negated.

       We introduce two A-variables [a1[i]] and [a2[s_xt-1-j]] and orient:

        [alien(xt) = a1 @ b'[j - i + 1] @ a2]

       where [b'] is [not b] if [xt] is negated and [b] otherwise.

       [alien(xt)] is [not(xt)] if [xt] is negated and [xt] otherwise, i.e.
       [alien(xt)] is the underlying alien.

       The A-variables are unconstrained by this equation and represent the
       remainder of the uninterpreted symbol before/after the extraction.

       (Note: [fresh_bitv] ensures that if either [a1] or [a2] has size [0], no
       variable is actually generated.) *)
    let cte_vs_ext bol xt s_xt i j =
      let a1  = fresh_bitv A i in
      let a2  = fresh_bitv A (s_xt - 1 - j) in
      let b_sz = j - i + 1 in
      let bol = if xt.negated then Z.lognot bol else bol in
      let cte = [ {bv = s_cte bol b_sz ; sz = b_sz } ] in
      let var = { bv = xt.value ; sz = s_xt }
      in var, a2@cte@a1

    (* Orient the equality [r1 = r2] where both [r1] and [r2] are
       uninterpreted ("Other") of size [sz], possibly negated.

       We introduce a new C-variable [c] and orient:

        [alien(r1) = c] and [alien(r2) = c']

       where [c'] is [c] if [r1] and [r2] have same polarity, and [not c]
       otherwise.

       Requires: [r1] and [r2] are distinct (for the C variables invariant)
    *)
    let other_vs_other r1 r2 sz =
      let maybe_negate c =
        if Bool.equal r1.negated r2.negated then c else negate_bitv c
      in
      let c = fresh_bitv C sz in [
        ({ bv = r1.value; sz }, c) ;
        ({ bv = r2.value; sz }, maybe_negate c)
      ]

    (* Orient the equality [r = xt[s_xt]^{i,j}] where [r] and [xt] are
       uninterpreted ("Other"), [r] has size [sz] and [xt] has size [s_xt].

       We introduce a new C-variable [c] and two A-variables [a1[i]] and
       [a2[s_xt - 1 - j]] and orient:

        [alien(r) = c] and [alien(xt) = a1 @ c' @ a2]

       where [c'] is [c] if [r] and [xt] have the same polarity, and

       Requires: [size st = j - i + 1]
       Requires: [st] and [xt] are distinct (for the C variables invariant ---
         but this is actually impossible because the sizes wouldn't match)
    *)
    let other_vs_ext r sz xt s_xt i j =
      let c  = fresh_bitv C sz in
      let a1 = fresh_bitv A i in
      let a2 = fresh_bitv A (s_xt - 1 - j) in
      let extr = { bv = xt.value ; sz = s_xt } in
      let maybe_negate c =
        if Bool.equal r.negated xt.negated then c else negate_bitv c
      in
      [ ({ bv = r.value; sz }, c) ; (extr, a2 @ maybe_negate c @ a1) ]

    (* Orient the equality [id[s]^{i,j} = id'[s']^{i',j'}].

       We introduce a C variable [c] and A variables a1, a1', a2, a2' and
       orient:

        [alien(id) = a2 @ c @ a1] and [alien(id') = a2' @ c' @ a1']

       where [c'] is [c] if [id] and [id'] have the same polarity and [not c]
       otherwise.

       The "shared" part is equal to the C variable.

       Requires: [id] and [id'] are distinct variables. This requirement ensures
         that we maintain the invariant of C variables that they never occur
         twice in the same multi-equation.
    *)
    let ext1_vs_ext2 (id,s,i,j) (id',s',i',j') = (* id != id' *)
      let c   = fresh_bitv (C) (j - i + 1) in
      let a1  = fresh_bitv A i  in
      let a1' = fresh_bitv A i' in
      let a2  = fresh_bitv A (s - 1 - j)   in
      let a2' = fresh_bitv A (s' - 1 - j') in
      let x_v = { sz = s  ; bv = id.value  } in
      let y_v = { sz = s' ; bv = id'.value } in
      let maybe_negate c =
        if Bool.equal id.negated id'.negated then c else negate_bitv c
      in
      [ (x_v , a2 @ c @ a1) ; (y_v , a2' @ maybe_negate c @ a1') ]

    (* Orient the equality [xt[siz]^{i1, i1 + tai} = xt[siz]^{i2, i2 + tai}]

       The [overl] variable contains the number of overlapping bits.
       If the [sp] variable is false, either size is negated and we negate every
       other occurence of the [b] variable below.

       - If there are no overlapping bits, the two parts are independent.
          We create a fresh B-variable [b] and A-variables [a1], [a2] and [a3]
          and orient:

            [xt = a3 @ b @ a2 @ b @ a1]

          The B-variable is used for the common part that is repeated.

       - If there are overlapping bits, we create only the A variables [a1] and
          [a3] for the before/after parts, and we create two B variables.

          [b_box] is the total constraint size (from [i1] to [i2 + tai]).
          [nn_overl] is the number of *initial* non-overlapping bits (from [i1]
          to [i2]).

          The [b] vector is then split into two parts to properly align the
          repetition. The computation is:

            sz_b1 = b_box % nn_overl (size of b1)
            sz_b2 = nn_overl - sz_b1 (size of b2)
            a1[i] @ ((b1 @ b2) * (b_box/nn_overl)) @ b1 @ a2[siz - tai - i2]

          It will be more clear with an example:

             _ nn_overl = 3
            / \
            xxxxxxx???
            ???yyyyyyy
            \________/
              b_box = 10

          Which creates the following decomposition:

            $$$xxxxxxx???###
            $$$???yyyyyyy###
            \\\uvvuvvuvvu///
            where a1 = \\\, b1 = u, b2 = vv, a2 = ///

       Requires: [i1 < i2]
    *)
    let ext_vs_ext sp xt siz (i1,i2) tai =
      let overl = i1 + tai -i2 in
      if overl <= 0 then begin
        let a1 = fresh_bitv A i1     in
        let a2 = fresh_bitv A (-overl) in
        let a3 = fresh_bitv A (siz - tai - i2) in
        let b  = fresh_bitv  B tai in
        let b' = if sp then b else negate_bitv b in
        ({ bv = xt.value ; sz = siz } , a3 @ b @ a2 @ b' @ a1)
      end
      else begin
        let b_box = i2 + tai - i1 in
        let nn_overl = tai - overl in(* =i2-i1 >0 sinon egalite sytaxique*)
        let sz_b1 = b_box mod nn_overl in
        let a1 = fresh_bitv A i1                 in
        let a3 = fresh_bitv A (siz - tai - i2) in
        let b1 = fresh_bitv B sz_b1              in
        let b2 = fresh_bitv B (nn_overl - sz_b1 )in
        let acc = ref b1 in
        let cpt = ref nn_overl in
        (* NB: first occurence of [b1] must be flipped, because there is an
           occurence before that in the initial [acc] value. *)
        let flip = ref true in
        while !cpt <= b_box do
          let b1 = if !flip && not sp then negate_bitv b1 else b1 in
          let b2 = if not !flip && not sp then negate_bitv b2 else b2 in
          acc := b1 @ b2 @(!acc);
          cpt := !cpt + nn_overl;
          flip := not !flip
        done;
        ({ bv = xt.value ; sz = siz } , a3 @ (!acc) @ a1)
      end

    (* [sys_solve sys] orients a system of equations between simple terms.

       The resulting system contains equations between a simple term on the
       left, and a solver_simple_term on the right.  The solver_simple_term only
       involves *fresh* A, B, and C variables.

       Each uninterpreted symbol (variable or alien) appearing in the original
       system appears in the oriented system, possibly multiple times.

       In a single equation of the resulting system:

       - The A variables only refer to parts of the variable that were
          unconstrained in the original equation. Each A variable appears
          *exactly once* in the oriented system.
       - The B variables appear due to equalities involving multiple
          extractions of the same uninterpreted term. They appear in a single
          equation, but can appear *multiple times in a single equation*.
       - The C variables appear due to equalities involving multiple
          uninterpreted terms. They appear at most once in each equation, but
          can appear *in multiple equations*. They only appear in equations that
          have distinct left-hand-side.

       Requires (R1): there are no trivial equalities in [sys]
    *)
    let sys_solve sys =
      let c_solve (st1,st2) = match st1.bv,st2.bv with
        |Cte b1, Cte b2 ->
          assert (not (Z.equal b1 b2));
          raise Util.Unsolvable (* forcement distincts *)

        |Cte b, Other r -> [cte_vs_other b r st2.sz]
        |Other r, Cte b -> [cte_vs_other b r st1.sz]

        |Cte b, Ext(xt,s_xt,i,j) -> [cte_vs_ext b xt s_xt i j]
        |Ext(xt,s_xt,i,j), Cte b -> [cte_vs_ext b xt s_xt i j]
        |Other o1, Other o2 ->
          if X.equal o1.value o2.value
          then raise Util.Unsolvable (* forcement different *)
          else
            other_vs_other o1 o2 st1.sz

        |Other o, Ext(xt,s_xt,i,j) -> other_vs_ext o st1.sz xt s_xt i j

        |Ext(xt,s_xt,i,j), Other o -> other_vs_ext o st2.sz xt s_xt i j
        |Ext(id,s,i,j), Ext(id',s',i',j') ->
          if not (X.equal id.value id'.value)
          then ext1_vs_ext2 (id,s,i,j) (id',s',i',j')
          else if i = i'
          then raise Util.Unsolvable
          else
            let sp = Bool.equal id.negated id'.negated in
            [ext_vs_ext sp id s (if i<i' then (i,i') else (i',i)) (j - i + 1)]

      in List.flatten (List.map c_solve sys)


    (* [partition eq l] returns a list of pairs [(a, bs)] where [bs] contains
       all the [b] such that [(a, b)] occurs in the original list.

       When applied to oriented systems of equations returned by [sys_solve],
       this merges together all the equalities involving the same [simple_term]
       on the left. *)
    let partition eq l =
      let rec add acc (t,cnf) = match acc with
        |[] -> [(t,[cnf])]
        |(t',cnf')::r -> if eq t t' then (t',cnf::cnf')::r
          else (t',cnf')::(add r (t,cnf))
      in List.fold_left add [] l


    let slicing_pattern s_l =
      let rec f_aux l1 l2 = match (l1,l2) with
        |[],[] -> []
        |a::r1,b::r2 when a = b -> a::(f_aux r1 r2)
        |a::r1,b::r2 ->
          if a < b then a::(f_aux r1 ((b-a)::r2))
          else b::(f_aux ((a-b)::r1) r2)
        |_ -> assert false
      in List.fold_left f_aux (List.hd s_l)(List.tl s_l)

    (* [slice_var var pat_hd pat_tl] slices a variable to make it fit the
       pattern [pat_hd :: pat_tl].
       Returns the list of created fresh variables, the left over pattern and
       the sort of the variable (if it is not a constant). *)
    let slice_var var pat_hd pat_tl =
      let mk, tr =
        match var.bv.defn with
        | Dcte (n, _) ->
          (fun ofs sz ->
             { bv = s_cte (Z.extract n (ofs - sz) sz) sz ; sz }
          ), None
        | Droot { sorte; _ } ->
          (fun _ sz -> { bv = s_var sorte; sz }), Some sorte
        | Dlink _ -> assert false
      in
      let rec aux cnt plist =
        match plist with
        | [] -> [], []
        | h :: t when cnt < h -> [ mk cnt cnt ], (h - cnt) :: t
        | h :: t when cnt = h -> [ mk cnt cnt ], t
        | h :: t ->
          let vl, ptail = aux (cnt - h) t in
          mk cnt h :: vl, ptail
      in
      let fst_v = mk var.sz pat_hd in
      let cnt = var.sz - pat_hd in
      let vl, pat_tail = aux cnt pat_tl in
      fst_v :: vl, pat_tail, tr

    (* [assoc_var_id vid sub] is a helper function to apply a substitution in
       the presence of negation.

       [sub] is a list of pairs [(var, vars)] where [var] is a [tvar] to be
       substituted by the composition [vars].  If the variable with ID [vid] is
       found in the list, the composition [vars] is returned. If the variable
       with ID [-vid] is found in the list, the composition [(bvnot vars)] is
       returned instead.

       Requires: the variables in [sub] are unconstrained root variables.
    *)
    let rec assoc_var_id vid sub =
      match sub with
      | [] -> raise Not_found
      | ({ bv = { defn = Droot { id; _ } }; _ }, vs) :: sub ->
        if id = vid then
          vs
        else if id = -vid then
          negate_bitv vs
        else
          assoc_var_id vid sub
      | _ :: _ -> (* Can only substitute [Droot] variables *) assert false

    (* [assoc_var v sub] is the same as [assoc_var_id] but takes a variable.

       Requires: [v] is an unconstrainted root variable or a constant.
       Raises: [Not_found] if [v] is not in the substitution, or if [v] is a
         constant.
       Requires: the variables in [sub] are unconstrained root variables. *)
    let assoc_var v sub =
      match v.bv.defn with
      | Droot { id; _ } -> assoc_var_id id sub
      | Dcte _ -> raise Not_found
      | _ -> (* Can only substitute [Droot] variables *) assert false

    (* This is a helper function for [slice_vars].

       [apply_sub_rev sub changed acc pat rcomp] applies the substitution [sub]
       (which maps B-variable to lists of B-variables) to the composition
       [rcomp], which is stored in *reverse* order, and:

       - Updates [changed] if the substitution effectively changes a variable
       - Computes the resulting composition (in normal order) in [acc]
       - Computes the resulting pattern in [pat]

       If [changed', comp', pat' = apply_sub_rev sub false [] [] rcomp] then
       the following holds:

       - [pat' = List.map (fun bv -> bv.st) comp']
       - If [changed'] is [false], [comp' = List.rev rcomp]

       Note that the substitution can be recursive, so we must do a recursive
       call on the result of applying the substitution (we can't add [vl]
       to [acc], we must add [(`rev` vl)] to [r] instead). *)
    let rec apply_sub_rev sub changed acc pat = function
      | [] -> changed, acc, pat
      | v :: r ->
        match assoc_var v sub with
        | vl ->
          (* Note that this is [(`rev` vl) @ r] and not [vl @ r] because
             the composition is given in reverse order. *)
          apply_sub_rev sub true acc pat (List.rev_append vl r)
        | exception Not_found ->
          apply_sub_rev sub changed (v :: acc) (v.sz :: pat) r

    (* [slice_vars eq pat (c, req, subs)] slices the variables in [eq] according
       to the pattern [pat]. [eq] is a composition of simple terms.

       If the composition [eq] does not match the pattern in [pat]:
       - When variables in the composition are bigger than the expected pattern
          size, the variables are split into multiple parts, which fit the
          pattern.

          Splits involving A variables are not recorded, because A variables are
          guaranteed to have unique occurences.

          Splits involving B and C variables are accumulated in [subs], which
          is a pair [(b_sub, c_sub)] of substitutions for the B and C
          variables, respectively.

          Splits involving C variables can propagate to other compositions in
          the system, but not to the current composition, since C variables
          never occur twice in the same composition.

          On the other hand, splits involving B variables must be applied to the
          current composition. This may cause other B variable to be split and
          become *smaller* than the corresponding pattern, even if the pattern
          elements were all smaller than the corresponding variables initially.

       - When variables in the composition are smaller than the expected
          pattern size (see above), the pattern must be broken up. This is
          recorded in [c], and it means that the pattern must be re-applied to
          any composition it was already applied to, which can cause more
          slicing.

       Finally, the resulting (= sliced) composition is stored in [req], in
       *reverse* order.  Once the slicing is done, [req] is reversed and
       returned. We also apply the B-substitutions that were accumulated,
       because it is possible to have two occurences [b_1] and [b_2] of a
       B-variable where the second occurence [b_2] gets sliced, but the first
       occurence [b_1] has already been dealt with. We perform this "late"
       slicing for all B-variables at once at the end of the iteration.
    *)
    let rec slice_vars eq pat (c, req, subs)=
      match eq, pat with
      | [], [] ->
        (* If the slicing changed the pattern, or if applying the B-variables
           substitution changes the pattern, we must report it so that the whole
           system is re-sliced. *)
        let (bsub, csub) = subs in
        begin match bsub with
          | [] when not c -> List.rev req, csub, None
          | _ ->
            let c, eq, pat = apply_sub_rev bsub c [] [] req in
            eq, csub, if c then Some pat else None
        end
      | st :: eq, n :: pt when st.sz < n ->
        (* Since we start with a [slicing_pattern], this should only occur when
           a B-variable has been split into parts below.
           Therefore we assert that the variable is indeed a B variable and that
           list of substitutions for B variables is not empty. *)
        assert (not (Compat.List.is_empty (fst subs)));
        assert (
          match st.bv.defn with Droot { sorte = B; _ } -> true | _ -> false
        );
        slice_vars eq (n - st.sz :: pt) (true, st :: req, subs)
      | st :: eq, n :: pt when st.sz = n ->
        slice_vars eq pt (c, st :: req, subs)
      | st :: eq, n :: pt ->
        let (nvar_list, pt', flag) = slice_var st n pt in
        begin match flag with
          | Some C ->
            (* A C variable got split: we must record the information in the
               C-substitution so that it gets to the instances of the variable
               in other multi-equations. *)
            let bsub, csub = subs in
            let subs = (bsub, (st, nvar_list) :: csub) in
            slice_vars eq pt' (c, List.rev_append nvar_list req, subs)
          | Some B ->
            (* A B variable got split: we must update the other occurences of
               the variable in the current composition. If there are other
               occurences before the current one, the information is recorded in
               the B-substitution, and we will also update it at the end. *)
            let eq = List.fold_right (fun st' acc ->
                if equal_alpha_term equal_tvar st' st then
                  nvar_list @ acc
                else
                  st' :: acc) eq [] in
            let bsub, csub = subs in
            let subs = ((st, nvar_list) :: bsub, csub) in
            slice_vars eq pt' (c, List.rev_append nvar_list req, subs)
          | None | Some A ->
            slice_vars eq pt' (c, List.rev_append nvar_list req, subs)
        end
      | [], _ :: _ | _ :: _, [] -> assert false

    (* [uniforme_slice vls] takes as argument the list of right-hand side
       concatenations associated with a single left-hand-side term in an
       equation system. We will call this a multi-equality.

       vls is a list of lists: each term in the multi-equality is a
       concatenation of solver_simple_terms.

       In particular, it satisfies the hypotheses that:

       - A and C variables occur *at most once* in the multi-equality (C
          variables may occur in multi-equality involving different left-hand
          sides).

       - B variables only appear in a single concatenation, but may (in fact,
          do) appear multiple times in that single concatenation.

       [uniforme_slice] returns a pair [(eqs, c_subs)] where:

       - [eqs] is a *uniform* multi-equality, that is, each concatenation in
          [eqs] has the same shape (the bitvector at any given position has the
          same size in all concatenations).  In particular, all concatenations
          have the same length.

          The concatenations in [eqs] satisfy the same requirements as above
          regarding the A, B and C variables; but some of the variables may have
          been replaced with a concatenation of smaller variables.

       - [c_subs] is a mapping from C variables to pairs of C variables, where
          the original C variable has been replaced by the concatenation of the
          new C variables. The original C variable must not be used anymore, and
          must be replaced with the concatenation instead.

          This mapping can be recursive: a C-variable [c] can be substituted
          with the concatenation [c1 @ c2] of two fresh C-variables, and then
          [c2] can be substituted with the concatenation [c3 @ c4]. *)
    let uniforme_slice eqs =
      let pat = slicing_pattern (List.map (List.map (fun bv -> bv.sz)) eqs) in
      let rec slice_vars_fix pat acc csub = function
        | [] -> acc, csub
        | eq :: eqs ->
          (* If the pattern changes, we must re-slice the whole system. This
             happens when one occurence of a B-variable gets sliced in a way
             that is not compatible with another occurence of the same
             B-variable. *)
          let eq, csub, pat' = slice_vars eq pat (false, [], ([], csub)) in
          match pat' with
          | None -> slice_vars_fix pat (eq :: acc) csub eqs
          | Some pat ->
            slice_vars_fix pat [] csub (List.rev_append acc (eq :: eqs))
      in
      slice_vars_fix pat [] [] eqs

    let apply_subs subs sys =
      let rec f_aux = function
        | [] -> []
        | v::r ->
          match assoc_var v subs with
          | vl ->
            (* Substitutions may be recursive and need to be applied again to
               their result. *)
            f_aux (vl @ r)
          | exception Not_found -> v :: f_aux r
      in List.map (fun (t,vls) ->(t,List.map f_aux vls))sys

    (* [equations_slice parts] takes a partitioned system [parts], i.e. a list
       of pairs [(a, bs)] where [a] are uninterpreted terms and [bs] are
       multi-equations involving A, B and C variables.

       The usual conditions apply:

       - A variables occur at most once in the whole partitioned system
       - B variables occur in at most one composition of at most one
          multi-equation, but they appear multiple times within this
          single composition
       - C variables occur at most once in the multi-equation associated with a
          given uninterpreted term, but may occur in multi-equations associated
          with distinct uninterpreted terms.

       [equations_slice parts] returns a new system that is equivalent to the
       original system, but where each uninterpreted term is associated with a
       *uniform* multi-equation (see the definition of [uniforme_slice]).

       Note that [equations_slice] works recursively: trying to make an uniform
       multi-equation for a specific uninterpreted term may cause some of its
       C-variables to be split, which in turn can require re-slicing the other
       equations involving the original C-variable, even if they have already
       been sliced. Which can in turn cause re-slicing of the new C-variables,
       etc. *)
    let equations_slice parts =
      let rec slice_rec bw = function
        |[] -> bw
        |(t,vls)::r ->
          let (vls', csub) = uniforme_slice vls in
          if Compat.List.is_empty csub then slice_rec ((t,vls')::bw) r
          else
            begin
              let _bw = apply_subs csub bw in
              let _fw = apply_subs csub r in
              let eq (_, l1) (_, l2) =
                (* [apply_subs] does not change the left-hand sides *)
                Compat.List.(equal (equal (equal_alpha_term equal_tvar)))
                  l1 l2
              in
              if Compat.List.equal eq _bw bw
              then slice_rec ((t,vls')::bw) _fw
              else slice_rec [] (_bw@((t,vls'):: _fw))
            end
      in slice_rec [] parts

    (* [build_solution unif_slic] takes as argument a uniform system of
        multi-equations (see above). It builds a solution to the uniform system
        by propagating equalities then replacing each term with the
        concatenation of representatives for the corresponding multi-equation.

        This is a destructive operation on the variables occuring in the system:
        the system must not be re-used. *)
    let build_solution unif_slic =
      (* Propagate equalities to ensure a single representative per class *)
      let union x y = union x.bv y.bv in
      List.iter (fun (_, vls) ->
          let hd = List.hd vls in
          List.iter (List.iter2 union hd) (List.tl vls)) unif_slic;

      let vars = Hashtbl.create 17 in
      let get_rep var =
        match (find var.bv).defn with
        | Dlink _ -> assert false
        | Dcte (n, _) -> Cte n
        | Droot { id; _ } ->
          assert (id <> 0);
          match Hashtbl.find vars (abs id) with
          | (p, n) -> if id > 0 then p else n
          | exception Not_found ->
            let r = X.term_embed (E.fresh_name (Ty.Tbitv var.sz)) in
            let p = Other (positive r) in
            let n = Other (negative r) in
            Hashtbl.add vars (abs id) (p, n);
            if id > 0 then p else n
      in
      let to_external_ast v =
        {sz = v.sz;
         bv = get_rep v}
      in
      let rec cnf_max l = match l with
        |[] -> []
        |[elt]-> [elt]
        |a::b::r ->
          begin
            match a.bv,b.bv with
            | Cte b1, Cte b2 ->
              cnf_max ({ bv = Cte Z.(b1 lsl b.sz + b2) ; sz = a.sz + b.sz }::r)
            | _, Cte _ -> a::(cnf_max (b::r))
            | _ -> a::b::(cnf_max r)
          end
      in List.map
        (fun (t,vls) ->
           t,cnf_max (List.map to_external_ast (List.hd vls))
        )unif_slic

    (* [solve u v] takes as argument two abstract terms (i.e. concatenation of
       simple terms) [u] and [v] and returns a substitution [subs].

       The substitution [subs] maps all the uninterpreted terms ("other")
       appearing in the abstract terms [u] and [v] to a definition, expressed as
       an abstract term, involving only constants and *fresh* A, B and C
       variables.

       @raise Valid if the two terms are already equal. *)
    let solve u v =
      if equal_abstract X.equal u v then raise Valid
      else begin
        let varsU = get_vars u in
        let varsV = get_vars v in
        if Compat.List.is_empty varsU && Compat.List.is_empty varsV
        then raise Util.Unsolvable
        else
          begin
            let st_sys = slice u v in
            if Options.get_debug_bitv () then
              Debug.print_sliced_sys st_sys;
            let sys_sols = sys_solve st_sys in
            if Options.get_debug_bitv () then
              Debug.print_c_solve_res sys_sols;
            let parts = partition (equal_alpha_term X.equal) sys_sols in
            if Options.get_debug_bitv () then
              Debug.print_partition_res parts;
            let unif_slic = equations_slice parts in
            if Options.get_debug_bitv () then
              Debug.print_partition_res unif_slic;
            let sol = build_solution unif_slic in
            if Options.get_debug_bitv () then
              Debug.print_final_solution sol;
            sol
          end
      end

  end

  let equal bv1 bv2 = equal_abstract X.equal bv1 bv2

  (* Note: we must use [X.str_cmp] here because [compare] is the implementation
     called by [X.str_cmp] itself. *)
  let compare x y = compare_abstract X.str_cmp (embed x) (embed y)

  let hash = hash_abstract X.hash

  let leaves bitv =
    List.fold_left
      (fun acc x ->
         match x.bv with
         | Cte _  -> acc
         | Other t | Ext(t,_,_,_) -> (X.leaves t.value)@acc
      ) [] bitv

  let is_constant bitv =
    List.for_all (fun x ->
        match x.bv with
        | Cte _ -> true
        | Other r | Ext (r, _, _, _) -> X.is_constant r.value) bitv

  let is_mine_opt = function
    | [{ bv = Other { value = r; negated = false }; _ }] -> Some r
    | _ -> None

  let is_mine bv =
    match is_mine_opt bv with
    | Some r -> r
    | None -> X.embed bv

  let print = Debug.print_C_ast

  (* This is used to extract terms from non-bitv semantic values.

     We assume that non-bitv semantic values of a bitvector type are
     necessarily uninterpreted terms, because that should be the case at the
     time this code is written.

     If this ever ceases to be the case, we should either preserve the original
     term along with the semantic value, or fail more gracefully here. *)
  let term_extract r =
    match X.term_extract r with
    | Some t, _ -> t
    | None, _ ->
      Util.internal_error "Non-BV semantic value: %a" X.print r

  (* This is a helper function that converts a [simple_term] to an integer
     expression. *)
  let simple_term_to_nat acc st =
    match st.bv with
    | Cte n -> E.Ints.(acc * ~$$Z.(~$1 lsl st.sz) + ~$$n)
    | Other r ->
      let t = term_extract r.value in
      let t = if r.negated then E.BV.bvnot t else t in
      E.Ints.(acc * ~$$Z.(~$1 lsl st.sz) + E.BV.bv2nat t)
    | Ext (o, _, i, j) ->
      assert (st.sz = j - i + 1);
      let t = term_extract o.value in
      let t = if o.negated then E.BV.bvnot t else t in
      E.Ints.(
        acc * ~$$Z.(~$1 lsl st.sz) +
        (E.BV.bv2nat t / ~$$Z.(~$1 lsl i)) mod ~$$Z.(~$1 lsl st.sz))

  let abstract_to_nat r =
    List.fold_left simple_term_to_nat (E.Ints.of_int 0) r

  (* Ideally, we would want to just call [abstract_to_nat r |> X.make]. But if
     we do so, we may end up in a loop where we repeatedly call [X.make] on a
     [BV2Nat] term -- so instead if we are a single [Other] term, we become
     uninterpreted. *)
  let bv2nat ot bv =
    match bv with
    | [{ bv = Other { value = r; negated }; sz }] ->
      let t = term_extract r in
      let maybe_negate t =
        if negated then E.Ints.(~$$Z.(~$1 lsl sz - ~$1) - t) else t
      in
      let t', ctx =
        begin match E.term_view t with
          | { f = Op Int2BV _; _ } ->
            (* bv2nat will simplify: we must call [X.make] again *)
            E.BV.bv2nat t |> maybe_negate, []
          | { ty = Tbitv n; _ } ->
            assert (n = sz);
            if negated then
              (* if we are negated, we will simplify *)
              E.BV.bv2nat t |> maybe_negate, []
            else
              (* bv2nat will *not* simplify: become uninterpreted with interval
                 information *)
              let t = E.BV.bv2nat t |> maybe_negate in
              t, [ E.Ints.(~$0 <= t) ; E.Ints.(t < ~$$Z.(~$1 lsl n)) ]
          | { ty; _ } ->
            Util.internal_error "expected bitv, got %a" Ty.print ty
        end
      in
      X.term_embed ot, E.Core.eq ot t' :: ctx
    | _ ->
      (* Note: we can't just call [X.make] on the result of [abstract_to_nat]
         because [X.make] should only be called on subterms. If we do it, it
         causes crashes when `IntervalCalculus.add` assumes that the arguments
         of division operators have been added to the `Uf` prior to the
         division itself. *)
      let t' = abstract_to_nat bv in
      X.term_embed ot, [ E.Core.eq ot t' ]

  let make t =
    let { E.f; xs; _ } = E.term_view t in
    match f, xs with
    | Op BV2Nat, [x] ->
      (* When we have a BV2Nat expression, we try our best to convert it to
         something that is usable by the arithmetic theory.

         More precisely, after simplification of the argument, we get a
         composition of constants and aliens or alien extractions, to which we
         apply [bv2nat] recursively. If the alien or alien extraction are
         [int2bv] terms, we convert the composition [(bv2nat ((_ int2bv n) x))]
         into [(mod x (pow 2 n))]. *)
      let r, ctx = Canon.make x in
      let r, ctx' = bv2nat t r in
      r, List.rev_append ctx' ctx
    | _ ->
      let r, ctx = Canon.make t in
      is_mine r, ctx

  let color _ = assert false

  let type_info bv =
    let sz = List.fold_left (fun acc bv -> bv.sz + acc) 0 bv in
    Ty.Tbitv sz

  let solve_ter u t =
    try
      List.map
        (fun (p, v) -> p.bv, is_mine v)
        (Solver.solve u t)
    with Solver.Valid -> []

  (* ne resout pas quand c'est deja resolu *)
  let solve_bis u t =
    if Options.get_debug_bitv () then
      Printer.print_dbg
        ~module_name:"Bitv" ~function_name:"solve_bis"
        "solve %a = %a" X.print u X.print t;

    match X.extract u , X.extract t with
    | None   , None   -> if X.str_cmp u t > 0 then [u,t] else [t,u]
    | None   , Some [ { bv = Cte _; _ } ] -> [u,t]
    | Some [ { bv = Cte _; _ } ],    None -> [t,u]
    | None   , Some t -> solve_ter (embed u) t
    | Some u , None   -> solve_ter u (embed t)
    | Some u , Some t -> solve_ter u t

  let rec subst_rec (x : X.r) (subs : X.r) (biv : X.r abstract) : X.r abstract =
    match biv with
    | [] -> []
    | { bv = Cte _; _ } as y :: biv ->
      y :: subst_rec x subs biv
    | { bv = Other y; _ } :: biv ->
      let y' =
        if X.equal x y.value then
          embed subs
        else
          embed (X.subst x subs y.value)
      in
      let y' = if y.negated then negate_abstract y' else y' in
      y' @ subst_rec x subs biv
    | { bv = Ext (y, y_sz, i, j); _ } :: biv ->
      let y' =
        if X.equal x y.value then
          embed subs
        else
          embed (X.subst x subs y.value)
      in
      let y' = if y.negated then negate_abstract y' else y' in
      extract y_sz i j y' @ subst_rec x subs biv

  let subst x subs biv =
    if Options.get_debug_bitv () then
      Printer.print_dbg
        ~module_name:"Bitv" ~function_name:"subst"
        "subst %a |-> %a in %a" X.print x X.print subs print biv;
    if Compat.List.is_empty biv then is_mine biv
    else
      let r = Canon.normalize (subst_rec x subs biv) in
      is_mine r
(*
  module M =  Map.Make
    (struct
      type t = X.r
      let compare = X.compare
     end)


  module Map = Map.Make
    (struct
      type t = (X.r simple_term) list
      let compare = compare_mine
     end)

  module Set = Set.Make (
    struct
      type t = (X.r simple_term) list
      let compare = compare_mine
    end)
*)
  let fully_interpreted sb =
    match sb with
    | Sy.Op (Concat | Extract _ | Sign_extend _ | Repeat _ | BVnot) -> true
    | _ -> false

  let term_extract _ = None, false

  let abstract_selectors v acc =
    let acc, v =
      Compat.List.fold_left_map (fun acc bv ->
          match bv with
          | { bv = Cte _ ; _ } -> acc, bv
          | { bv = Other { negated ; value = r } ; sz } ->
            let r', acc = X.abstract_selectors r acc in
            acc, { bv = Other { negated ; value = r' } ; sz }
          | { bv = Ext ({ negated ; value = r }, i, j, r_sz) ; sz } ->
            let r', acc = X.abstract_selectors r acc in
            acc, { bv = Ext ({ negated ; value = r' }, i, j, r_sz) ; sz }
        ) acc v
    in
    is_mine v, acc

  let solve r1 r2 pb =
    Sig.{pb with sbt = List.rev_append (solve_bis r1 r2) pb.sbt}

  (* Pop the first bit, raises [Not_found] if there is no first bit.

     Note that the returned bv has an incorrect size. *)
  let pop_bit = function
    | [] -> raise Not_found
    | ({ bv = Cte n; sz } as st) :: rst ->
      Some (Z.testbit n (sz - 1)),
      if sz > 1 then
        { st with sz = sz - 1 } :: rst
      else
        rst
    | { bv = Other _ | Ext _ ; sz } as st :: rst ->
      None, if sz > 1 then { st with sz = sz - 1 } :: rst else rst

  (* Fills the segment of [buf] from [pos] to [sz] with a bitvector that is
     different from all those in [abstracts].

     Uninterpreted ("Other" and "Ext") components in [abstracts] are ignored.

     Currently a fairly naive backtracking search. *)
  let rec search buf pos sz abstracts =
    (* [t] : values (a) we must be distinct from and (b) start with a '1' *)
    (* [f] : values (a) we must be distinct from and (b) start with a '0' *)
    let t, nt, f, nf = List.fold_left (fun (t, nt, f, nf) ab ->
        let b, bv = pop_bit ab in
        match b with
        | Some true -> (bv :: t, 1 + nt, f, nf)
        | Some false -> (t, nt, bv :: f, 1 + nf)
        | None -> (t, nt, f, nf)) ([], 0, [], 0) abstracts
    in
    match t, f with
    | _, [] -> Bytes.fill buf pos sz '0'
    | [], _ -> Bytes.fill buf pos sz '1'
    | _, _ ->
      (* Prefer searching where there are more candidates, i.e. less
         constraints. *)
      let x, cx, y, cy =
        if nt < nf then t, '1', f, '0' else f, '0', t, '1'
      in
      match search buf (pos + 1) (sz - 1) x with
      | () -> Bytes.set buf pos cx
      | exception Not_found ->
        search buf (pos + 1) (sz - 1) y;
        Bytes.set buf pos cy

  let is_cte = function | { bv = Cte _; _ } -> true | _ -> false
  let is_cte_abstract = List.for_all is_cte

  let assign_value r distincts eq =
    (* If we are trying to assign a value to a constant, or a term that has a
       constant in its equivalence class, bail out *)
    let biv = embed r in
    if is_cte_abstract biv || List.exists
         (fun (_, x) ->
            match X.extract x with
            | Some b -> is_cte_abstract b
            | None -> false) eq
    then None else
      let sz = List.fold_left (fun tot { sz; _ } -> tot + sz) 0 biv in
      (* Only try to be distinct from constants. *)
      let distincts =
        List.fold_left (fun acc x ->
            let biv = embed x in
            if is_cte_abstract biv then biv :: acc else acc) [] distincts
      in
      let buf = Bytes.create sz in
      match search buf 0 sz distincts with
      | () ->
        let bv = Bytes.unsafe_to_string buf in
        Some (E.bitv bv (Ty.Tbitv sz), true)
      | exception Not_found ->
        let bv = String.make sz '0' in
        Some (E.bitv bv (Ty.Tbitv sz), true)

  let to_model_term r =
    match embed r with
    | [{ bv = Cte b; sz }] ->
      let s = Z.format ("%0" ^ string_of_int sz ^ "b") b in
      Some (Expr.bitv s Ty.(Tbitv sz))
    | _ ->
      (* A constant semantic value cannot be a concatenation of constant
         simple term as the canonizer merges consecutive constant simple
         terms. *)
      None
end
