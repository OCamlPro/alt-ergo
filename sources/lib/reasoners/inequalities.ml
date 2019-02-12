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

module Z = Numbers.Z
module Q = Numbers.Q

module type S = sig

  module P : Polynome.T with type r = Shostak.Combine.r
  module MP : Map.S with type key = P.t

  type t = {
    ple0 : P.t;
    is_le : bool;
    (* int instead of Term.t as a key to prevent us
       from using it in deductions *)
    dep : (Q.t * P.t * bool) Util.MI.t;
    expl : Explanation.t;
    age : Z.t;
  }

  module MINEQS : sig
    type mp = (t * Q.t) MP.t
    val empty : mp
    val is_empty : mp -> bool
    val younger : t -> t -> bool
    val insert : t -> mp -> mp
    val ineqs_of : mp -> t list
    val add_to_map : mp -> t list -> mp
    val iter : (P.t -> (t * Q.t) -> unit) -> mp -> unit
    val fold : (P.t -> (t * Q.t) -> 'a -> 'a) -> mp -> 'a -> 'a
  end

  val current_age : unit -> Numbers.Z.t
  val incr_age : unit -> unit

  val create_ineq :
    P.t -> P.t -> bool -> Expr.t option -> Explanation.t -> t

  val print_inequation : Format.formatter -> t -> unit

  val fourierMotzkin :
    ('are_eq -> 'acc -> P.r option -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

  val fmSimplex :
    ('are_eq -> 'acc -> P.r option -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

  val available :
    ('are_eq -> 'acc -> P.r option -> t list -> 'acc) -> 'are_eq -> 'acc ->
    MINEQS.mp -> 'acc

end

module type Container_SIG = sig
  module Make
      (P : Polynome.T with type r = Shostak.Combine.r)
    : S with module P = P

end

module Container : Container_SIG = struct
  module Make
      (P : Polynome.T with type r = Shostak.Combine.r)
    : S with module P = P = struct

    module X = Shostak.Combine
    module P = P
    module MP = Map.Make(P)
    module MX = Map.Make(struct type t = X.r let compare = X.hash_cmp end)

    let age_cpt = ref Z.zero

    let current_age () = !age_cpt

    let incr_age () =  age_cpt := Z.add !age_cpt Z.one;

    type t = {
      ple0 : P.t;
      is_le : bool;
      dep : (Q.t * P.t * bool) Util.MI.t;
      expl : Explanation.t;
      age : Z.t;
    }

    let print_inequation fmt ineq =
      fprintf fmt "%a %s 0 %a" P.print ineq.ple0
        (if ineq.is_le then "<=" else "<") Explanation.print ineq.expl

    let create_ineq p1 p2 is_le a expl =
      let ple0 = P.sub p1 p2 in
      match P.to_list ple0 with
      | ([], ctt) when is_le && Q.sign ctt > 0->
        raise (Intervals.NotConsistent expl)

      | ([], ctt) when not is_le  && Q.sign ctt >= 0 ->
        raise (Intervals.NotConsistent expl)

      | _ ->
        let p,c,d = P.normal_form ple0 in (* ple0 = (p + c) * d, and d > 0 *)
        assert (Q.compare d Q.zero > 0);
        let c = if P.type_info p == Ty.Treal then c else (Q.ceiling c) in
        let p = P.add_const c p in
        let dep = match a with
          | Some a -> Util.MI.singleton (Expr.uid a) (Q.one, p, is_le)
          | None -> Util.MI.empty
        in
        { ple0 = p; is_le = is_le;
          dep = dep;
          expl = expl; age = !age_cpt }

    let find_coefficient x ineq = P.find x ineq.ple0

    let split_pos_neg _ ({ ple0 = p ; age; _ }, _) (mx, nb_max) =
      let mx = List.fold_left (fun m (c,x) ->
          let cmp = Q.sign c in (* equiv. to compare c Q.zero *)
          if cmp = 0 then m
          else
            let (pos, neg) = try MX.find x m with Not_found -> (0,0) in
            if cmp > 0 then MX.add x (pos+1, neg) m
            else MX.add x (pos, neg+1) m ) mx (fst (P.to_list p))
      in
      mx, if Z.equal age !age_cpt then nb_max + 1 else nb_max

    module MINEQS = struct

      type mp = (t * Q.t) MP.t

      let empty = MP.empty

      let is_empty mp = MP.is_empty mp

      let younger ineq' ineq =
        (* requires more work in Explanation
           Explanation.younger ineq'.expl ineq.expl ||*)
        Z.compare ineq'.age ineq.age <= 0

      let insert ineq mp =
        (* ineq.ple0  == is ==  p0 + ctt <(=) 0 i.e. p0 <(=) -ctt *)
        let p0, ctt = P.separate_constant ineq.ple0 in
        try
          let ineq', ctt' = MP.find p0 mp in
          (* ineq'.ple0  == is ==  p0 + ctt' <(=) 0 i.e. p0 <(=) -ctt' *)
          let cmp = Q.compare ctt' ctt in
          if cmp = 0 then
            if ineq.is_le == ineq'.is_le then (* equivalent *)
              (* if ineq in older, we should update the map to have
                 the right (most recent) age *)
              if younger ineq ineq' then mp
              else MP.add p0 (ineq, ctt) mp
            else
            if ineq.is_le then mp (* ineq' more precise, because it has < *)
            else MP.add p0 (ineq, ctt) mp (*ineq has < -c and ineq' <= -c *)
          else
          if cmp > 0 then (* i.e. ctt' > ctt, i.e. p0 <(=) -ctt' < -ctt *)
            mp (* ineq' is more precise *)
          else (* cmp < 0 i.e. ctt' < ctt, i.e. - ctt' > - ctt >(=) p0 *)
            MP.add p0 (ineq, ctt) mp (* ineq is more precise *)
        with Not_found -> MP.add p0 (ineq, ctt) mp

      let ineqs_of mp = MP.fold (fun _ (ineq, _) acc -> ineq :: acc) mp []

      let add_to_map mp l = List.fold_left (fun mp v -> insert v mp) mp l

      let iter = MP.iter

      let fold = MP.fold

    end

    module Debug = struct

      let list_of_ineqs fmt =
        List.iter (fprintf fmt "%a  " print_inequation)

      let map_of_ineqs fmt =
        MINEQS.iter (fun _ (i , _) -> fprintf fmt "%a  " print_inequation i)

      let cross x vars cpos cneg others =
        if Options.debug_fm () then begin
          fprintf Options.fmt "[fm] We cross on %a (%d vars remaining)@."
            X.print x (MX.cardinal vars);
          fprintf Options.fmt "with:@. cpos = %a@. cneg = %a@. others = %a@."
            list_of_ineqs cpos list_of_ineqs cneg map_of_ineqs others
        end

      let cross_result x ninqs =
        if Options.debug_fm () then
          fprintf Options.fmt
            "result of eliminating %a: at most %d new ineqs (not printed)@."
            X.print x ninqs

    end

    let mult_list c dep =
      if Q.equal c Q.one then dep
      else
        Util.MI.fold
          (fun a (coef,p,is_le) dep ->
             Util.MI.add a (Q.mult coef c, p, is_le) dep
          )dep Util.MI.empty

    let merge_deps d1 d2 =
      Util.MI.merge
        (fun _ op1 op2 ->
           match op1, op2 with
           | None, None -> None
           | Some _, None -> op1
           | None, Some _ -> op2
           | Some(c1,p1, is_le1), Some(c2,p2, is_le2) ->
             assert (P.equal p1 p2 && is_le1 == is_le2);
             Some (Q.add c1 c2, p1, is_le1)
        )d1 d2

    let cross x cpos cneg mp =
      let nb_inqs  = ref 0 in
      let rec cross_rec acc l =
        Options.exec_thread_yield ();
        match l with
        | [] -> acc
        | { ple0=p1; is_le=k1; dep=d1; expl=ex1; age=a1 }::l ->
          let n1 = Q.abs (P.find x p1) in
          let acc =
            List.fold_left
              (fun acc
                {ple0=p2; is_le=k2; dep=d2; expl=ex2; age=a2} ->
                Options.exec_thread_yield ();
                let n2 = Q.abs (P.find x p2) in
                let n1, n2 = (* light normalization of n1 and n2 *)
                  if Q.equal n1 n2 then Q.one, Q.one
                  else n1, n2
                in
                let p = P.add (P.mult_const n2 p1) (P.mult_const n1 p2) in
                let p, c, d = P.normal_form p in (* light norm of p *)
                let p = P.add_const c p in
                assert (Q.sign d > 0);
                let d1 = mult_list (Q.div n2 d) d1 in
                let d2 = mult_list (Q.div n1 d) d2 in
                let ni =
                  { ple0 = p;  is_le = k1&&k2;
                    dep = merge_deps d1 d2;
                    age = Z.max a1 a2;
                    expl = Explanation.union ex1 ex2 }
                in
                incr nb_inqs;
                MINEQS.insert ni acc
              ) acc cpos
          in
          cross_rec acc l
      in
      cross_rec mp cneg, !nb_inqs

    let split x mp =
      let split_rec _ (ineq, _) (cp, cn, co, nb_pos, nb_neg) =
        try
          let a = find_coefficient x ineq in
          if Q.sign a > 0 then ineq::cp, cn, co, nb_pos+1, nb_neg
          else cp, ineq::cn, co, nb_pos, nb_neg+1
        with Not_found -> cp, cn, MINEQS.insert ineq co, nb_pos, nb_neg
      in
      MINEQS.fold split_rec mp ([], [], MINEQS.empty, 0, 0)

    let choose_var mp =
      let pos_neg, nb_max = MINEQS.fold split_pos_neg mp (MX.empty, 0) in
      if nb_max = 0 then raise Not_found;
      let xopt = MX.fold (fun x (pos, neg) acc ->
          match acc with
          | None -> Some (x, pos * neg)
          | Some (_, c') ->
            let c = pos * neg in
            if c < c' then Some (x, c) else acc
        ) pos_neg None in
      match xopt with
      | Some (x, _) -> x, pos_neg
      | None -> raise Not_found

    let monome_ineq ineq = P.is_monomial ineq.ple0 != None

    let fourierMotzkin add_ineqs are_eq acc mp =
      let rec fourier acc mp =
        Options.exec_thread_yield ();
        if MINEQS.is_empty mp then acc
        else
          try
            let x, vars = choose_var mp in
            let cpos, cneg, others, nb_pos, nb_neg = split x mp in
            Debug.cross x vars cpos cneg others;
            let s_x = Some x in
            let acc = add_ineqs are_eq acc s_x cpos in
            let acc = add_ineqs are_eq acc s_x cneg in
            let size_res = Q.from_int (nb_pos * nb_neg) in
            let mp', nb_inqs =
              if Q.compare size_res (fm_cross_limit ()) >= 0 &&
                 Q.sign (fm_cross_limit()) >= 0 then
                let u_cpos = List.filter monome_ineq cpos in
                let u_cneg = List.filter monome_ineq cneg in
                let mp', nb_inq1 = match u_cpos with
                  | []  -> others, 0
                  | [_] -> cross x cneg u_cpos others
                  | _   -> assert false (* normalization invariant *)
                in
                let mp', nb_inq2 = match u_cneg with
                  | []  -> mp', 0
                  | [_] -> cross x cpos u_cneg mp'
                  | _   -> assert false (* normalization invariant *)
                in
                mp', nb_inq1 + nb_inq2
              else
                cross x cpos cneg others
            in
            Debug.cross_result x nb_inqs;
            fourier acc mp'
          with Not_found -> add_ineqs are_eq acc None (MINEQS.ineqs_of mp)
      in
      fourier acc mp

    let fmSimplex _add_ineqs _are_eq _acc _mp =
      let msg =
        "Not implemented in the default version!"^
        "Use the FmSimplex plugin instead" in
      failwith msg

    let available = fourierMotzkin

  end
end

module FM = Container.Make

let current = ref (module Container : Container_SIG)

let initialized = ref false

let set_current mdl = current := mdl

let load_current_inequalities_reasoner () =
  match Options.inequalities_plugin () with
  | "" ->
    if Options.debug_fm () then
      eprintf "[Dynlink] Using the 'FM module' for arithmetic inequalities@."

  | path ->
    if Options.debug_fm () then
      eprintf "[Dynlink] Loading the 'inequalities' reasoner in %s ...@." path;
    try
      MyDynlink.loadfile path;
      if Options.debug_fm () then  eprintf "Success !@.@."
    with
    | MyDynlink.Error m1 ->
      if Options.debug_fm() then begin
        eprintf
          "[Dynlink] Loading the 'inequalities' reasoner in \"%s\" failed!@."
          path;
        Format.eprintf ">> Failure message: %s@.@."
          (MyDynlink.error_message m1);
      end;
      let prefixed_path = sprintf "%s/%s" Config.pluginsdir path in
      if Options.debug_fm () then
        eprintf
          "[Dynlink] Loading the 'inequalities' reasoner in %s with prefix %s@."
          path Config.pluginsdir;
      try
        MyDynlink.loadfile prefixed_path;
        if Options.debug_fm () then  eprintf "Success !@.@."
      with
      | MyDynlink.Error m2 ->
        if not (Options.debug_fm()) then begin
          eprintf
            "[Dynlink] Loading the 'inequalities' reasoner in \"%s\" failed!@."
            path;
          Format.eprintf ">> Failure message: %s@.@."
            (MyDynlink.error_message m1);
        end;
        eprintf
          "[Dynlink] Trying to load the plugin from \"%s\" failed too!@."
          prefixed_path;
        Format.eprintf ">> Failure message: %s@.@."
          (MyDynlink.error_message m2);
        exit 1

let get_current () =
  if not !initialized then
    begin
      load_current_inequalities_reasoner ();
      initialized := true;
    end;
  !current
