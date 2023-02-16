module type X = sig
  type var
  type val_

  val pp_var : Format.formatter -> var -> unit
  val pp_val : Format.formatter -> val_ -> unit

  val compare_var : var -> var -> int
  val equal_val : val_ -> val_ -> bool
  val compare_val : val_ -> val_ -> int
end

module type S = sig
  type var
  (** Type of the variable. *)

  type val_
  (** Type of the value. *)

  type t
  (** Type of a substitution. *)

  exception Collision of var * val_ * val_

  val id : t
  (** [id] is the identical substitution. *)

  val is_identical : t -> bool
  (** [is_identical sbs] check if the substitution [sbs] is the trivial
      substitution. *)

  val apply : t -> var -> val_
  (** [apply sbs k] apply the substitution [sbs] to the variable [k].
      @Raise Not_found if the variable [k] is not in the domain of the
      substitution [sbs]. *)

  val assign : ?force:bool -> var -> val_ -> t -> t
  (** [assign ~force k v sbs] add the substitution [k -> v] to the
      substitution [sbs].
      If [force = false] the function raises the exception {!exception:Collide}
      if the variable [k] is already substitute by a value [w] in [sbs] and
      [v] and [w] are not equal for {!val:X.equal_val}.
      Otherwise, the old binding is replaced by the new one. *)

  val compose : ?force:bool -> t -> t -> t
  (** [compose sbs1 sbs2] compose the substitutions [sbs1] and [sbs2]. If
      [force = false] and [sbs1] and [sbs2] does not agree on some variables,
      the exception {!exception:Collision} is raised. Otherwise, the
      old bindings are replaced by the new ones. *)

  val filter_domain : t -> f:(var -> bool) -> t

  val equal : t -> t -> bool
  (** [equal sbs1 sbs2] check if the substitutions [sbs1] and [sbs2] are equal
      using {!val:X.equal_val} to compare the values. *)

  val compare : t -> t -> int
  (** [equal sbs1 sbs2] compare the substitutions [sbs1] and [sbs2]
      using {!val:X.compare_val} to compare the values. *)

  val pp : Format.formatter -> t -> unit
  (** [pp fmt sbs] pretty print the substitution [sbs] on the formatter
      [fmt]. *)

  val show : t -> string
  (** [show sbs] produce the string displaying by [pp]. *)

  module Set : Set.S with type elt = t
  (** Module of sets of substitutions using the comparison function
      {!val:compare}. *)

  module Map : Map.S with type key = t
  (** Module of maps of substitutions using the comparison function
      {!val:compare}. *)
end

module Make (X : X) : S with type var = X.var and type val_ = X.val_ = struct
  module M = Map.Make (struct
      type t = X.var
      let compare = X.compare_var
    end)

  type var = X.var
  type val_ = X.val_
  type t = val_ M.t

  exception Collision of var * val_ * val_

  let id = M.empty

  let is_identical = M.is_empty

  let compare = M.compare X.compare_val

  let equal = M.equal X.equal_val

  let apply sbs var = M.find var sbs

  let assign ?(force = false) k v =
    let collision_handler = function
      | Some w when force -> Some w
      | Some w when X.equal_val v w -> Some w
      | Some w -> raise (Collision (k, v, w))
      | None -> Some v
    in
    M.update k collision_handler

  let compose ?(force = false) =
    let collision_handler =
      if force then fun _ _ v2 -> Some v2
      else fun k v1 v2 -> begin
          if X.equal_val v1 v2 then raise (Collision (k, v1, v2))
          else Some v1
        end
    in
    M.union collision_handler

  let filter_domain sbs ~f = M.filter (fun v _ -> f v) sbs

  let pp fmt sbs = M.iter (fun k v ->
      Format.fprintf fmt "%a -> %a" X.pp_var k X.pp_val v) sbs

  let show = Format.asprintf "%a" pp

  module Set = Set.Make(struct
      type nonrec t = t
      let compare = compare
    end)

  module Map = Map.Make(struct
      type nonrec t = t
      let compare = compare
    end)
end
