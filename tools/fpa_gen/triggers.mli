module DE = Dolmen.Std.Expr

val process_axiom :
  fp_tyvar:DE.Ty.Var.t -> DE.Term.Var.t list -> DE.Term.t -> unit
