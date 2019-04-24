open Typed

(** 1. Values *)

(** The type of values manipulated by the simplifyer. *)
type value

(** 2. Simplifyer *)

(** A simplified formula/expr/... type. *)
type 'a simp

(** Returns the formula that has been simplified *)
val get : 'a simp -> 'a

(** Returns true if the formula has simplified *)
val modified : 'a simp -> bool

module type S =
sig
  (** The type of annotations *)
  type a

  (** Each of the following function returns a simplified version of the
      atom/formula/desc/tterm/decl in argument.
      Tests multiple properties:
      - replaces trivial equalities by true or false
      - replaces (_ is cons) (cons ...) by true when `cons` is a
        constructor
      - replaces if (cond) then t1 else t2 by t1/t2 when cond is
        simplified by true/false. *)

  val simplify_atom : a atatom -> a atatom simp

  val simplify_tform : a atform -> a atform simp

  val simplify_tt_desc : a tt_desc -> a tt_desc simp

  val simplify_tterm : a atterm -> a atterm simp

  val simplify_tdecl : a atdecl -> a atdecl simp
end

module Make
    (Annot :
     sig
       type annot

       (** They are used to unify the constant true/false representations *)
       val true_form : annot atform
       val false_form : annot atform
       val true_atom : annot atatom
       val false_atom : annot atatom

       (** Builds an annoted value given a value. *)
       val mk : 'a -> ('a, annot) annoted

       (** Prints an annotation *)
       val print_annot : annot Typed.annot_printer

     end
    ) : S with type a = Annot.annot

module SInt : S with type a = int
