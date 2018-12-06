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

open AltErgoLib
open Options
open Format
open Numbers
module H = Hashtbl

type pred = Eq | Ge | Le | Gt

let dsimplex = ref false

(******************************************************************************)

module type Coef_Type = sig
  type t = Q.t
  val zero      : t
  val one       : t
  val m_one : t
  val is_zero   : t -> bool
  val is_one    : t -> bool
  val compare   : t -> t -> int
  val equal     : t -> t -> bool
  val to_string : t -> string
  val add       : t -> t -> t
  val sub       : t -> t -> t
  val mult      : t -> t -> t
  val div       : t -> t -> t
  val minus     : t -> t
end

type t_c2 = Q.t * Q.t

type t1 =  { mutable a : (int * Q.t) array; mutable c : Q.t * Q.t}

type t2 =  { mutable a2 : Q.t array; mutable c2 : Q.t * Q.t}



type rich_result =
  { vof   : t_c2;
    vals  : (int * t_c2) list;
    ctx   : (int * t2) list;
    distr : int array;
    order : int Queue.t}

type result =
  | Unsat   of rich_result
  | Unbound of rich_result
  | Max     of rich_result
  | Eq_unsat


module Simplex (C : Coef_Type) = struct

  exception Out of int

  module C2 = struct
    type t = C.t * C.t

    let zero  = C.zero, C.zero

    let concrete c = c, C.zero
    let abstract c = c, C.m_one (* -1, car on a p + (-eps) > 0 *)

    let to_string (c,k) =
      "(" ^ (C.to_string c) ^ " + " ^ (C.to_string k) ^ "*e)"
    let add (c1,k1) (c2,k2)   = C.add c1 c2, C.add k1 k2
    let mult c1 (c2,k2)  = C.mult c1 c2, C.mult c1 k2
    let is_zero (c, k) = C.is_zero c && C.is_zero k
    let is_one (c, k) = C.is_one c && C.is_one k

    let compare  (c1,k1) (c2,k2) =
      let r = C.compare c1 c2 in if r <> 0 then r else C.compare k1 k2

    let div (c1,k1) c = C.div c1 c, C.div k1 c

    let minus (c,k) = C.minus c, C.minus k

  end

  type sbt  = {old_lhs:int; lhs:int; rhs:t2}

  let boung_ghost = -1

  module D = struct

    let matrix_stats matrix co =
      if !dsimplex then begin
        fprintf fmt "taille: %d x %d@."
          (Array.length co.a2) (List.length matrix);
        let z = ref 0 in
        let nz = ref 0 in
        List.iter
          (fun (_,{a2=a2}) ->
             Array.iter (fun v -> incr (if Q.is_zero v then z else nz)) a2
          )matrix;
        fprintf fmt "zero-cells:     %d@." !z;
        fprintf fmt "non-zero-cells: %d@." !nz
      end

    let expand s n =
      let rec exrec s n = if n <= -1 then s else exrec (" "^s) (n-1) in
      exrec s (n-(String.length s))

    let poly0 fmt l =
      List.iter (fun (si,c) -> fprintf fmt "%sL%d + " (C.to_string c) si) l;
      fprintf fmt "0"

    let poly fmt {a=a;c=c} =
      Array.iter (fun (si,c) -> fprintf fmt "%sL%d + " (C.to_string c) si) a;
      fprintf fmt "%s" (C2.to_string c)

    let poly01 fmt {a=a; c=c} =
      for i = 1 to Array.length a - 2 do
        fprintf fmt "%s" (expand (C.to_string (snd a.(i))) 2)
      done

    let pred = function
      | Eq -> "="
      | Ge -> ">="
      | Gt -> ">"
      | Le -> "<="

    let sep = "----------------------------------------------------------------"

    let given_problem co eqs s_neq nb_vars =
      if !dsimplex then begin
        fprintf fmt "%s@." sep;
        fprintf fmt "I am given a problem of size %d:@." nb_vars;
        fprintf fmt "max: %a;@." poly0 co;
        List.iter
          (fun (x,(pp, pn, ctt)) ->
             fprintf fmt "  (%a)  + (%a) + %s =  0;@."
               poly0 pp poly0 pn (Q.to_string ctt)
          ) eqs;
        fprintf fmt "  %a >  0;@." poly0 s_neq;
        fprintf fmt "%s@." sep;
      end


    let max_poly {a2=a2} =
      Array.fold_left (fun n v -> max n (String.length (C.to_string v))) 0 a2

    let max_sys ctx = List.fold_left (fun n (_,p) -> max n (max_poly p)) 0 ctx

    let expand s n =
      let rec exrec s n = if n <= -1 then s else exrec (" "^s) (n-1) in
      exrec s (n-(String.length s))

    let ppoly sp fmt {a2=a2; c2=c2} =
      Array.iter (fun c -> fprintf fmt "%s" (expand (C.to_string c) sp)) a2;
      fprintf fmt "   %s@." (C2.to_string c2)

    let auxiliary_problem sbt s_neq co h_i_s =
      if !dsimplex then begin
        fprintf fmt "%s@.Associations:@." sep;
        H.iter(fun i j -> fprintf fmt "L(%d) -> %d@." j i)h_i_s;
        fprintf fmt "subst:@.";
        List.iter
          (fun ((s,i),p) ->fprintf fmt "(L%d,%d) |-> %a@." s i poly p) sbt;

        fprintf fmt "s_neq:@.";
        let (s, i), pneq = s_neq in
        fprintf fmt "(L%d,%d) |-> %a@." s i poly pneq;
        fprintf fmt "cost:@.";
        fprintf fmt "%a@." poly co;
        fprintf fmt "%s@." sep
      end

    let compacted_problem basic non_basic matrix co =
      if !dsimplex then begin
        let sp = max (max_sys matrix) (max_poly co) in
        fprintf fmt "%s@." sep;
        fprintf fmt "compacted_problem:@.";
        fprintf fmt "> non_basic vars:@.";
        H.iter (fun i s -> fprintf fmt "L%i |-> %d@." s i) non_basic;

        fprintf fmt "@.> basic vars:@.";
        H.iter (fun i s -> fprintf fmt "L%i |-> %d@." s i) basic;

        fprintf fmt "@.> matrix:@.";
        List.iter (fun (i,p) -> fprintf fmt "%d |-> %a" i (ppoly sp) p) matrix;

        fprintf fmt "@.> cost: %a@.@." (ppoly sp) co;
        fprintf fmt "%s@." sep
      end

    let psystem fmt (ctx, co, distr) =
      fprintf fmt "@.tbl: ";
      Array.iteri (fun i s -> fprintf fmt "%d -> L%d | " i s) distr;
      fprintf fmt "@.@.";

      let sp = max (max_sys ctx) (max_poly co) in
      List.iter
        (fun (i,p) -> fprintf fmt "%d    = %a" i (ppoly sp) p) ctx;
      fprintf fmt "cost = %a@." (ppoly sp) co

    let report_unsat ctx co distr =
      if !dsimplex then begin
        fprintf fmt "%s@." sep;
        fprintf fmt "pb aux's result:(E_unsat)@.%a@." psystem (ctx,co,distr);
        fprintf fmt "%s@." sep;
      end

    let report_max ctx co distr =
      if !dsimplex then begin
        fprintf fmt "%s@." sep;
        fprintf fmt "pb aux's result:(E_max)@.%a@." psystem (ctx,co,distr);
        fprintf fmt "%s@." sep;
      end

    let given_problem2 ctx co distr =
      if !dsimplex then begin
        fprintf fmt "%s@." sep;
        fprintf fmt "[solve] given pb:@.%a@." psystem (ctx,co, distr);
        fprintf fmt "%s@." sep
      end

    let in_simplex ctx co distr =
      if !dsimplex then begin
        fprintf fmt "%s@." sep;
        fprintf fmt "@.[simplex]@. I start with:@.%a@."
          psystem (ctx,co, distr);
        fprintf fmt "%s@." sep
      end


    let result_extraction status ctx co distr =
      if !dsimplex then begin
        fprintf fmt
          "::RESULT EXTRACTION FROM:::::::::::::::::::::::::::::::::::::::@.";
        fprintf fmt "The problem is %s@." status;
        fprintf fmt "%a@."  psystem (ctx,co, distr);
        fprintf fmt
          ":::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::@.";
      end



    let retrieved_cost co =
      if !dsimplex then
        fprintf fmt "retrieved_const: %a@." (ppoly 4) co


    let pline fmt (i,p) =
      let sp = max_poly p in
      fprintf fmt "x%d   = %a" i (ppoly sp) p

    let psbt fmt sbt =
      let sp = max_poly sbt.rhs in
      fprintf fmt "%d |->  %a / (old %d)@."
        sbt.lhs (ppoly sp)sbt.rhs sbt.old_lhs

    let choosed_var ch_vr =
      if !dsimplex then fprintf fmt "choosed var's index: %d@." ch_vr

    let choosed_eq ch_eq =
      if !dsimplex then fprintf fmt "choosed eq:     %a@." pline ch_eq

    let pivot_result sbt =
      if !dsimplex then fprintf fmt "pivot's result: %a@." psbt sbt

    let change_pivot ch_vr old_vr =
      if !dsimplex then fprintf fmt "ch_vr: %d et old_vr: %d@." ch_vr old_vr

    let init_simplex_pb ctx co distr ghost line =
      if !dsimplex then begin
        fprintf fmt "%s@." sep;
        fprintf fmt "init_simplex: pb_aux@.%a@." psystem (ctx,co,distr);
        fprintf fmt "choosed var's index: %d@." ghost;
        fprintf fmt "choosed eq:     %a@." pline line;
        fprintf fmt "%s@." sep
      end

  end

  module Normalizer = struct

    exception Trivial
    exception Inconsistent
    exception Pivot of int * int * C.t

    let array_is_null ar =
      let len = Array.length ar in
      let is_null = ref true in
      let i = ref 0 in
      while !i < len && !is_null do
        is_null := C.is_zero ar.(!i);
        incr i;
      done;
      !is_null

    let coefs_have_mem_sign ar =
      let len = Array.length ar in
      let nb_pos = ref 0 in
      let nb_neg = ref 0 in
      let i = ref 0 in
      while !i < len && (!nb_pos = 0 || !nb_neg = 0) do
        let c = C.compare (snd ar.(!i)) C.zero in
        if c > 0 then incr nb_pos;
        if c < 0 then decr nb_neg;
        incr i;
      done;
      match !nb_pos, !nb_neg with
      | 0, 0  -> Some 0
      | 0, ng -> Some ng
      | ps, 0 -> Some ps
      | _     -> None


    let create len (lpos, lneg, ctt) tbl_i_s =
      let a = Array.init len (fun i -> i, Q.zero) in (* BUG CORRIGE*)
      let f1 (i,c)= a.(i) <- i,c in
      List.iter f1 lpos;
      List.iter f1 lneg;
      a.(0) <- -1, C.zero;
      a.(len-1) <- 1-len, C.zero;
      { a = a; c = C2.concrete ctt }

    let create_strict len s_neq tbl_i_s =
      { (create len (s_neq,[],Q.zero) tbl_i_s) with c = C2.abstract C.zero }

    let mult_const a c v =
      let f2 i (s,cs) = a.(i) <- s, C.zero in
      let g2 i (s,cs) = () in
      let h2 i (s,cs) = a.(i) <- s, C.mult v cs in
      let k = if C.is_zero v then f2 else if C.is_one v then g2 else h2 in
      Array.iteri k a;
      {a=a ; c = C2.mult v c}

    let pivot_in_p len {a=a; c=c} =
      try
        for i = 0 to len - 1 do
          let s, v = a.(i) in
          if not (C.is_zero v) then raise (Pivot (s,i,v))
        done;
        if C2.is_zero c then raise Trivial else raise Inconsistent
      with Pivot (s,ind,v) ->
        a.(ind) <- s, C.zero;
        (s, ind), mult_const a c (C.div C.m_one v)

    let subst_in_p ({a=a ; c=c} as pp) ((s,lhs), {a=rhs_a; c=rhs_c}) =
      let s', v = a.(lhs) in
      (*assert (String.compare s s' = 0);*)
      if not (C.is_zero v) then begin
        a.(lhs) <- s, C.zero;
        let f6a j (sw,w) =
          let sj, vj = rhs_a.(j) in
          if not (C.is_zero vj) then a.(j) <- sj, C.add vj w
        in
        let f6b j (sw,w) =
          let sj, vj = rhs_a.(j) in
          if not (C.is_zero vj) then a.(j) <- sj, C.add (C.mult v vj) w
        in
        let f6 = if C.is_one v then f6a else f6b in
        Array.iteri f6 a;
        pp.c <- C2.add c (C2.mult v rhs_c)
      end

    let z_subst_in_p p s = p.a.(s) <- s, C.zero

    let normalize_poly p sbt zsbt =
      for i = 0 to Vec.size sbt - 1 do subst_in_p p (Vec.get sbt i) done;
      for i = 0 to Vec.size zsbt - 1 do z_subst_in_p p (Vec.get zsbt i) done

    let normalize_sbt sbt zsbt =
      for i = 0 to Vec.size sbt - 1 do
        for j = 0 to Vec.size zsbt - 1 do
          z_subst_in_p (snd (Vec.get sbt i)) (Vec.get zsbt j)
        done;
      done;
      for i = Vec.size sbt - 1 downto 1 do
        for j = i - 1 downto 0 do
          subst_in_p (snd (Vec.get sbt j)) (Vec.get sbt i)
        done;
      done;
      let l1 = ref [] in
      let l2 = ref [] in
      for i = 0 to Vec.size sbt - 1  do l1 := (Vec.get sbt i)  :: !l1 done;
      for i = 0 to Vec.size zsbt - 1 do l2 := (Vec.get zsbt i) :: !l2 done;
      !l2, !l1


    let sbt = Vec.make 107 ((0,0),{a=[||]; c=Q.zero, Q.zero})
    let zsbt = Vec.make 107 (-2)

    let solve_zero_arr zsbt zsbt_inv a =
      Array.iter
        (fun (s,coef) ->
           if not (C.is_zero coef) then
             begin Vec.push zsbt s; zsbt_inv.(s) <- true end
        )a

    let solve_zero_list zsbt zsbt_inv l =
      if !dsimplex then  fprintf fmt "[eq_solve] 0 = 0 (modulo Li >= 0)@.";
      List.iter
        (fun (s,coef) ->
           if not zsbt_inv.(s) then
             begin Vec.push zsbt s; zsbt_inv.(s) <- true end
        )l




    let substs_from_equalities eqs h_i_s len =
      if !dsimplex then fprintf fmt "subst from eqs:@.";
      Vec.clear sbt;
      Vec.clear zsbt;
      let zsbt_inv = Array.make len false in
      let eqs =
        List.fold_left
          (fun acc (x,((lp,ln, ctt) as lp_ln)) -> (* lp + ln + ctt = 0 *)
             let sg = Q.sign ctt in
             let p = (create len lp_ln h_i_s) in
             if !dsimplex then fprintf fmt "  >> poly %a@." D.poly p;
             match lp, ln with
             | [], []   -> assert false
             | _::_, [] when sg = 0 -> solve_zero_list zsbt zsbt_inv lp; acc
             | [], _::_ when sg = 0 -> solve_zero_list zsbt zsbt_inv ln; acc
             | _::_, [] when sg > 0 -> raise Inconsistent
             | [], _::_ when sg < 0 -> raise Inconsistent
             | _ -> (create len lp_ln h_i_s)::acc
          )[] eqs
      in
      (*let mm = ref [] in*)
      List.iter
        (fun p ->
           (*mm := {c=p.c ; a = Array.copy p.a} :: !mm;*)
           if !dsimplex then
             fprintf fmt "[eq_solve] solve      0 = %a@." D.poly p;
           normalize_poly p sbt zsbt;
           if !dsimplex then
             fprintf fmt "i.e. [eq_solve] solve      0 = %a@." D.poly p;
           try
             match coefs_have_mem_sign p.a with
             | Some n ->
               let c = C2.compare p.c C2.zero in
               if n = 0 && c <> 0 then raise Inconsistent;
               if n > 0 && c > 0 then raise Inconsistent;
               if n < 0 && c < 0 then raise Inconsistent;
               if n <> 0 && c = 0 then solve_zero_arr zsbt zsbt_inv p.a;
               if n <> 0 && c <> 0 then
                 let ((s, pivot), p) as ln = pivot_in_p len p in
                 if !dsimplex then
                   fprintf fmt "new pivot (L%d,%d) |-> %a@.@."
                     s pivot D.poly p;
                 Vec.push sbt ln
             | _ ->
               let ((s, pivot), p) as ln = pivot_in_p len p in
               if !dsimplex then
                 fprintf fmt "new pivot (L%d,%d) |-> %a@.@."
                   s pivot D.poly p;
               Vec.push sbt ln
           with Trivial -> ()
        )eqs;
      normalize_sbt sbt zsbt

    (*
      let mm = !mm in
      let mmT =
      List.fast_sort
      (fun {a=a1} {a=a2} ->
      try
      for i = 0 to Array.length a1 -1 do
      let _, c1 = a1.(i) in
      let _, c2 = a2.(i) in
      if C.is_zero c1 then raise (Out 1);
      if C.is_zero c2 then raise (Out (-1));
      let c = C.compare c1 c2 in if c <> 0 then raise (Out c)
      done;
      0
      with Out c -> c
      ) mm
      in
      fprintf fmt "MM@.";
      List.iter
      (fun p ->
      fprintf fmt "%a@." D.poly01 p;
      )mm;
      fprintf fmt "MMT@.";
      List.iter
      (fun p ->
      fprintf fmt "%a@." D.poly01 p;
      )mmT;
    *)

    let make_problem co eqs s_neq len =
      let h_i_s = H.create len in
      for i = 1 to len - 2 do H.add h_i_s i i done;
      H.add h_i_s 0 (-1);
      H.add h_i_s (len-1) (1-len);
      if !dsimplex then
        fprintf fmt "make_problem: len = %d (incluant les neqs et ghost)@." len;
      let zsbt, sbt = substs_from_equalities eqs h_i_s len in

      if !dsimplex then begin
        fprintf fmt "ZERO substs:@.";
        List.iter (fun i -> fprintf fmt "L%i -> 0 ; " i) zsbt;
        fprintf fmt "@."
      end;

      let p_sneq = create_strict len s_neq h_i_s in
      List.iter (subst_in_p p_sneq) sbt;
      List.iter (z_subst_in_p p_sneq) zsbt;
      let s_neq = (1 - len, len - 1) , p_sneq in
      let co = create len (co, [], Q.zero) h_i_s in
      List.iter (subst_in_p co) sbt;
      List.iter (z_subst_in_p co) zsbt;
      D.auxiliary_problem sbt s_neq co h_i_s;
      co, s_neq :: sbt, zsbt

    let compact_poly_2 {a=a ; c=c} base new_len h_zsbt =
      let non_basic = H.create 101 in
      let old_i = ref 0 in
      let f3 i =
        while H.mem base !old_i || H.mem h_zsbt !old_i do incr old_i done;
        let s, c = a.(!old_i) in
        H.add non_basic i s;
        incr old_i;
        c
      in
      {a2=Array.init new_len f3 ; c2=c}, non_basic

    let compact_poly {a=a ; c=c} base new_len h_zsbt =
      let old_i = ref 0 in
      let f4 i =
        while H.mem base !old_i || H.mem h_zsbt !old_i do incr old_i done;
        let s, coef = a.(!old_i) in
        incr old_i;
        coef
      in
      { a2 = Array.init new_len f4; c2=c }


    (* XXX : Faire des simplifications pour eliminer les  lignes triviales
       de la matrice de la forme s_i |-> ctt ???
       XXX : Faire des simplifications pour eliminer les  colonnes nulles ???
    *)
    let compact_problem co matrix len new_len zsbt =
      let base = H.create 101 in
      let basic = H.create 101 in
      List.iter (fun ((s,i),p) -> H.add base i 0) matrix;
      let h_zsbt = H.create (List.length zsbt) in
      List.iter (fun i -> H.add h_zsbt i ()) zsbt;
      let matrix, _ =
        List.fold_left
          (fun (matrix,cptL) ((s,i),p) ->
             let p = compact_poly p base new_len h_zsbt in
             H.add basic cptL s;
             (cptL, p)::matrix, cptL + 1
          )([],new_len) matrix
      in
      let matrix =
        List.fold_left
          (fun acc ((i, p) as line) ->
             if !dsimplex then
               fprintf fmt "compact_problem: LINE %a@." D.pline line;
             if array_is_null p.a2 then
               let c = C2.compare p.c2 C2.zero in
               if c = 0 then acc
               else
               if c < 0 then raise Inconsistent
               else line :: acc (* CONSTANT SOLUTION: SHOULD EXTRACT IT*)
             else line :: acc
          )[] matrix
      in
      let co, non_basic = compact_poly_2 co base new_len h_zsbt in
      D.compacted_problem basic non_basic matrix co;
      let distr =
        Array.init
          len (fun i -> try H.find basic i with Not_found ->
            try H.find non_basic i
            with Not_found ->
              if !dsimplex then
                fprintf fmt "Colonne vide ! donc supprimee@.";
              -20000)
      in
      co, matrix, distr

    let norm_main co eqs s_neq nb_vars =
      let len = nb_vars + 2 in (* ghost + one slack var *)
      let co, matrix, zsbt = make_problem co eqs s_neq len in
      let new_len = len - (List.length matrix) - (List.length zsbt) in
      if !dsimplex then
        fprintf fmt "new_len = %d (excluant les pivots)@." new_len;
      compact_problem co matrix len new_len zsbt

  end

  (************************************************************************)

  module Core_Simplex = struct

    type system = (int * t2) list * t2

    type i_result =
      | I_unsat of system
      | I_unbound of system
      | I_max of system

    exception E_max of system
    exception E_unbound of system
    exception E_unsat of system

    let len          =  ref (-1)
    let co_opt: t2 option ref = ref None
    let v_ghost      = "!ghost"
    let main_simplex = ref true

    (*debut utile *)
    let reset_refs length =
      len    := length;
      co_opt := None;
      main_simplex := true

    let index_of_ghost distr =
      try
        Array.iteri (fun i s -> if s = boung_ghost then raise (Out i)) distr;
        assert false
      with Out i -> i

    let line_with_min_const ctx =
      match ctx with
      | [] -> assert false
      | line :: ctx ->
        List.fold_left
          (fun ((_,p') as line') ((_,p) as line) ->
             if C2.compare p.c2 p'.c2 < 0 then line else line') line ctx

    let subst ({a2=a2; c2=c2} as pp) lhs {a2=rhs_a2; c2=rhs_c2} =
      let v = a2.(lhs) in
      if not (C.is_zero v) then begin
        a2.(lhs) <- C.zero;
        let f7a j w =
          let rhs_j = rhs_a2.(j) in
          if not (C.is_zero rhs_j) then a2.(j) <- C.add rhs_j w
        in
        let f7b j w =
          let rhs_j = rhs_a2.(j) in
          if not (C.is_zero rhs_j) then a2.(j) <- C.add (C.mult v rhs_j) w
        in
        let f7 = if C.is_one v then f7a else f7b in
        Array.iteri f7 a2;
        pp.c2 <- C2.add c2 (C2.mult v rhs_c2)
      end

    let subst_line {old_lhs=old_lhs; lhs=lhs; rhs=rhs} (i, p) =
      if i = old_lhs then begin p.a2 <- rhs.a2; p.c2 <- rhs.c2 end
      else subst p lhs rhs

    let subst_ctx ctx sbt = List.iter (subst_line sbt) ctx

    (*fin utile *)


    (*** coeur du simplex *****************************************************)

    exception Choose_index of int

    let choose_var ctx co (q,lines) =
      try
        for _ = 0 to !len - 1 do
          let i = Queue.pop q in
          Queue.push i q;
          if C.compare co.a2.(i) C.zero > 0 then raise (Choose_index i)
        done;
        raise (E_max (ctx,co))
      with Choose_index ind -> ind

    let choose_eq ctx co ch_vr =
      let acc = ref None in
      List.iter
        (fun ((j,p) as line) ->
           let v_ch_vr = p.a2.(ch_vr) in
           if C.compare v_ch_vr C.zero < 0 then
             let rap = C2.minus (C2.div p.c2 v_ch_vr) in
             match !acc with
             | None -> acc := Some (v_ch_vr, rap, line)
             | Some (v_r,r,(jj,_)) ->
               let delta = C2.compare rap r in
               let change = delta < 0 || (delta = 0 &&  j < jj) in
               if change then acc := Some (v_ch_vr, rap, line)
        )ctx;
      match !acc with
      | None            -> raise (E_unbound (ctx,co))
      | Some (_, _, eq) -> eq

    let mult_const a2 c2 v =
      let f5 i cs = a2.(i) <- C.zero in
      let g5 i cs = () in
      let h5 i cs = a2.(i) <- C.mult v cs in
      let k = if C.is_zero v then f5 else if C.is_one v then g5 else h5 in
      Array.iteri k a2;
      {a2=a2 ; c2 = C2.mult v c2}


    let change_pivot ch_vr (old_vr, {a2=old_a; c2=c2}) distr order =
      D.change_pivot ch_vr old_vr;

      (* update_distr *)
      let tmp = distr.(ch_vr) in
      distr.(ch_vr) <- distr.(old_vr);
      distr.(old_vr) <- tmp;

      let v = old_a.(ch_vr) in
      old_a.(ch_vr) <- C.m_one;
      {old_lhs=old_vr; lhs=ch_vr; rhs= mult_const old_a c2 (C.div C.m_one v)}

    let cpt = ref 0
    let last_cost = ref (Q.zero, Q.zero)
    let loops distr order co_cst =
      if C2.compare co_cst ! last_cost = 0 then begin
        incr cpt;
        let limit = max (Queue.length (fst order)) (Array.length distr) in
        !cpt >= limit
      end
      else begin
        last_cost := co_cst;
        cpt := 0;
        false
      end

    let nbloops = ref 0
    let rec simplex ctx co distr order =

      (*
        let ppoly fmt {a2=a2; c2=c2} =
        Array.iter (fun c -> fprintf fmt "%s " (C.to_string c)) a2;
        fprintf fmt " %s@." (C2.to_string c2)
        in
        let psystem fmt (ctx, co, distr) =
        fprintf fmt "@.tbl: ";
        Array.iteri (fun i s -> fprintf fmt "%d -> %s | " i s) distr;
        fprintf fmt "@.@.";
        List.iter (fun (i,p) -> fprintf fmt "%d    = %a" i ppoly p) ctx;
        fprintf fmt "cost = %a@." ppoly co
        in
        fprintf fmt "@.####################################################@.";
        fprintf fmt "%a" psystem (ctx, co, distr);
        fprintf fmt "@.####################################################@.";
      *)

      if !main_simplex && loops distr order co.c2 then raise (E_max(ctx,co));
      incr nbloops;
      (*
      fprintf fmt "nb_loops = %d @." !nbloops;
      fprintf fmt "ici: main = %b : %s @." !main_simplex (C2.to_string co.c2);
      (*D.matrix_stats ctx co;*)
      *)

      if !main_simplex &&
         C.compare (fst co.c2) C.zero >= 0 &&
         C.compare (snd co.c2) C.zero >= 0 then
        raise (E_max(ctx,co));

      D.in_simplex ctx co distr;

      let ch_vr = choose_var ctx co order in
      D.choosed_var ch_vr;

      let ch_eq = choose_eq ctx co ch_vr in
      D.choosed_eq ch_eq;

      let sbt = change_pivot ch_vr ch_eq distr order in
      D.pivot_result sbt;

      begin match !co_opt with
          None -> ()
        | Some coo ->
          subst coo sbt.lhs sbt.rhs;
          co_opt := Some coo
      end;
      subst_ctx ctx sbt;
      subst co sbt.lhs sbt.rhs;
      simplex ctx co distr order

    (*** / coeur du simplex **************************************************)

    (***   coeur du simplex_init *********************************************)

    let delete_ghost ghost ghost_p ctx distr order =
      let ch_vr = ref 0 in
      try
        for i = 0 to !len - 1 do
          if C.compare ghost_p.a2.(i) C.zero <> 0 then (ch_vr := i; raise Exit)
        done;
        failwith "Pas possible"
      with Exit ->
        let sbt = change_pivot !ch_vr (ghost, ghost_p) distr order in
        D.choosed_var !ch_vr;
        D.pivot_result sbt;
        subst_ctx ctx sbt;
        ctx

    let report_unsat distr order ctx co =
      D.report_unsat ctx co distr;
      let ghost = try index_of_ghost distr with Not_found -> assert false in
      if ghost < !len then begin
        List.iter (fun (_,p) -> p.a2.(ghost) <- C.zero) ctx;
        ctx, true
      end
      else
        try
          let p_ghost = List.assoc ghost ctx in
          let ctx = delete_ghost ghost p_ghost ctx distr order in
          let ghost = index_of_ghost distr in
          assert (ghost < !len);
          List.iter (fun (_,p) -> p.a2.(ghost) <- C.zero) ctx;
          ctx, true
        with Not_found -> assert false

    let report_max distr order ctx co =
      D.report_max ctx co distr;
      let ghost =
        try index_of_ghost distr
        with Not_found -> assert false in
      if ghost < !len then begin
        List.iter (fun (_,p) ->
            if not ((Array.length p.a2) == !len) then
              failwith (
                sprintf "len = %d but plen = %d" !len (Array.length p.a2));
            p.a2.(ghost) <- C.zero) ctx;
        ctx, false
      end
      else
        try
          let p_ghost = List.assoc ghost ctx in
          let ctx = delete_ghost ghost p_ghost ctx distr order in
          let ghost = index_of_ghost distr in
          assert (ghost < !len);
          List.iter (fun (_,p) -> p.a2.(ghost) <- C.zero) ctx;
          ctx, C2.compare p_ghost.c2 C2.zero <> 0
        with Not_found -> assert false

    (* chercher une solution initiale *)
    let init_simplex ctx ((_,p) as line) distr order =
      let ghost = index_of_ghost distr in
      List.iter (fun (_,p) -> p.a2.(ghost) <- C.one) ctx;
      let co_a2 = Array.make (Array.length p.a2) C.zero in
      co_a2.(ghost) <- C.m_one;
      let co = {a2=co_a2; c2= C2.zero} in
      D.init_simplex_pb ctx co distr ghost line;
      (* choix du premier pivot sur la variable fantome *)
      let sbt = change_pivot ghost line distr order in
      D.pivot_result sbt;
      subst_ctx ctx sbt;
      subst co sbt.lhs sbt.rhs;
      try simplex ctx co distr order
      with
      | E_unbound (ctx,co) -> raise (E_unbound (ctx,co)) (*XXX*)
      | E_unsat   (ctx,co) -> report_unsat distr order ctx co
      | E_max     (ctx,co) -> report_max distr order ctx co


    let retrieve_cost distr =
      match !co_opt with
      | None -> assert false
      | Some co ->
        co_opt := None;
        let i = index_of_ghost distr in
        if i < !len then co.a2.(i) <- C.zero;
        co


    (*** / coeur du simplex_init *********************************************)

    let solve co ctx distr order =
      D.given_problem2 ctx co distr;
      try
        let (_,p) as line = line_with_min_const ctx in
        if C2.compare p.c2 C2.zero >= 0 then simplex ctx co distr order
        else
          begin
            co_opt := Some co;
            main_simplex := false;
            let ctx, unsat = init_simplex ctx line distr order in
            main_simplex := true;
            let co = retrieve_cost distr in
            D.retrieved_cost co;
            if unsat then I_unsat (ctx, co) else simplex ctx co distr order
          end
      with
      | E_max (ctx, co)    -> I_max (ctx, co)
      | E_unbound (ctx,co) -> I_unbound (ctx, co)
      | E_unsat(ctx,co)    -> I_unsat(ctx,co)


    let infos_of distr q {c2=c2} ctx =
      let acc0 =
        List.fold_left
          (fun acc (i,p) ->
             if C2.is_zero p.c2 then acc
             else (i, p.c2):: acc
          )[] ctx
      in
      let acc = ref [] in
      let inf i s = if s > 0 then
          try acc := (s, List.assoc i acc0) :: !acc
          with Not_found -> ()
      in
      Array.iteri inf distr;
      {vof   = c2;
       vals  = !acc;
       ctx   = ctx;
       distr = distr;
       order =q }

    let result_extraction distr q = function
      | I_max (ctx_ex,co_ex) ->
        D.result_extraction "max" ctx_ex co_ex distr;

        let res = infos_of distr q co_ex ctx_ex in
        if !dsimplex then
          fprintf fmt ">result size %d@." (List.length res.vals);
        Max res

      | I_unbound (ctx_ex,co_ex) ->
        D.result_extraction "unbound" ctx_ex co_ex distr;
        let res = infos_of distr q co_ex ctx_ex in
        if !dsimplex then
          fprintf fmt ">result size %d@." (List.length res.vals);
        Unbound res

      | I_unsat (ctx_ex,co_ex) ->
        D.result_extraction "unsat" ctx_ex co_ex distr;
        let res = infos_of distr q co_ex ctx_ex in
        if !dsimplex then fprintf fmt ">result size %d@."
            (List.length res.vals);
        Unsat res

    let core_main co matrix distr =
      let len = Array.length co.a2 in
      reset_refs len;
      let q = Queue.create () in
      for i = len - 1 downto 0 do Queue.push i q done;
      let res = solve co matrix distr (q, []) in
      result_extraction distr q res

  end

  let cpt = ref 0
  let main co eqs s_neq nb_vars =
    (*XXXTimer.Simplex_main.start();*)
    (*incr cpt;
      fprintf fmt "%d@." !cpt; *)
    let res = D.given_problem co eqs s_neq nb_vars;
      try
        (*fprintf fmt "avant norm@.";
          fprintf fmt " nb_eqs = %d@." (List.length eqs);
          fprintf fmt " nb_vars = %d@." nb_vars;*)
        let co, matrix, distr = Normalizer.norm_main co eqs s_neq nb_vars in
        (*fprintf fmt "apres norm@.";
          fprintf fmt " nb_sbts = %d@." (List.length matrix);
          fprintf fmt " nb_vars = %d@." (Array.length distr);*)
        D.matrix_stats matrix co;
        Core_Simplex.core_main co matrix distr
      with Normalizer.Inconsistent -> Eq_unsat
    in
    (*XXXTimer.Simplex_main.stop();*)
    res





  let subst_spec ({a2=a2; c2=c2} as pp) v {a2=rhs_a2; c2=rhs_c2} =
    if not (C.is_zero v) then begin
      let f7a j w =
        let rhs_j = rhs_a2.(j) in
        if not (C.is_zero rhs_j) then a2.(j) <- C.add rhs_j w
      in
      let f7b j w =
        let rhs_j = rhs_a2.(j) in
        if not (C.is_zero rhs_j) then a2.(j) <- C.add (C.mult v rhs_j) w
      in
      let f7 = if C.is_one v then f7a else f7b in
      Array.iteri f7 a2;
      pp.c2 <- C2.add c2 (C2.mult v rhs_c2)
    end

  let partial_restart res (max_ctt: (int*Q.t) list) =
    (*XXXTimer.Simplex_main.start();*)
    if !dsimplex then fprintf fmt "new:   ";
    if !dsimplex then List.iter
        (fun (i,q) ->
           fprintf fmt "%s*L%d + " (Q.to_string q) i
        )(List.rev max_ctt);
    if !dsimplex then fprintf fmt "@.";

    (*let max_ctt = ancien_ in*)
    match res with
    | Eq_unsat -> Eq_unsat

    | Unsat   rr | Unbound rr | Max rr ->
      match rr.ctx with
      | [] -> assert false
      | (_,a)::_ ->
        if !dsimplex then fprintf fmt "@.tbl: ";
        if !dsimplex then
          Array.iteri (fun i s ->
              fprintf fmt "%d -> L%d | " i s) rr.distr;
        if !dsimplex then fprintf fmt "@.@.";
        let len = Array.length a.a2 in
        let cost =
          {a2=Array.make len Q.zero; c2=Q.zero,Q.zero} in
        Array.iteri
          (fun i ld ->
             if !dsimplex then fprintf fmt "> AVANT: cost: %a@."
                 (D.ppoly (D.max_poly cost)) cost;
             if !dsimplex then
               fprintf fmt "traitement de l'index %d@." i;
             begin
               try
                 let q = List.assoc ld max_ctt in
                 if !dsimplex then
                   fprintf fmt "L%d associe a %s@." ld (Q.to_string q);
                 try
                   cost.a2.(i) <- Q.add cost.a2.(i) q
                 with Invalid_argument s ->
                   assert (String.compare s "index out of bounds" = 0);
                   if !dsimplex then
                     fprintf fmt "L%d out of bounds@." ld;
                   try
                     let rhs = List.assoc i rr.ctx in
                     subst_spec cost q rhs

                   with Not_found -> () (*vaut zero ? assert false*)
               with Not_found ->
                 if !dsimplex then
                   fprintf fmt "L%d associe a RIEN@." ld
             end;

          )rr.distr;
        if !dsimplex then
          fprintf fmt "@.> RES cost: %a@.@."
            (D.ppoly (D.max_poly cost)) cost;

        (* XXX *)
        let leng = Array.length cost.a2 in
        Core_Simplex.reset_refs leng;
        (* XXX *)
        let res =
          Core_Simplex.solve cost rr.ctx rr.distr (rr.order, []) in
        let res =
          Core_Simplex.result_extraction rr.distr rr.order res in
        (*XXX*Timer.Simplex_main.stop();*)
        res

(*
  let main co eqs s_neq nb_vars =
  let res = main co eqs s_neq nb_vars in
  let res' = partial_restart res co in
  (match res, res' with
  | Eq_unsat, Eq_unsat -> ()
  | Unsat   rr, Unsat   r ->
(*let r1, i1 = rr.vof in
  let r2, i2 = r.vof in
  assert (Q.equal r1 r2 && Q.equal i1 i2)
*)
  ()

  | Unbound rr,Unbound r  ->
  let r1, i1 = rr.vof in
                    let r2, i2 = r.vof in
  assert (Q.equal r1 r2 && Q.equal i1 i2)

  |  Max     rr, Max     r ->
  let r1, i1 = rr.vof in
  let r2, i2 = r.vof in
  assert (Q.equal r1 r2 && Q.equal i1 i2)

  | _ -> assert false);
  res
*)
end

module Simplex_Q = Simplex(Numbers.Q)

