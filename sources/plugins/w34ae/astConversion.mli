

val get_infix_ident : Why3_ptree.ident -> string
val str_of_label : Why3_ptree.label -> string
val str_of_labs : Why3_ptree.label list -> string
val dummy_loc : Why3_loc.position


val translate_tuple : Parsed.lexpr list -> Loc.t -> Parsed.lexpr
val translate_innfix_ident :
  Why3_ptree.ident -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_infix_ident :
  Why3_ptree.ident -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_qualid : Why3_ptree.qualid -> Parsed.lexpr
val translate_idapp :
  Why3_ptree.qualid -> Parsed.lexpr list -> Loc.t -> Parsed.lexpr
