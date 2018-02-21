

val get_infix_ident : Why3_ptree.ident -> string
val str_of_label : Why3_ptree.label -> string
val str_of_labs : Why3_ptree.label list -> string
val dummy_loc : Why3_loc.position
val translate_quant :
  Why3_ptree.quant ->
  Loc.t ->
  (string * string * Parsed.ppure_type) list ->
  (Parsed.lexpr list * bool) list ->
  Parsed.lexpr list -> Parsed.lexpr -> Parsed.lexpr
val translate_binop :
  Why3_ptree.binop -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_tuple : Parsed.lexpr list -> Loc.t -> Parsed.lexpr
val translate_pty : Why3_ptree.pty -> Parsed.ppure_type
val translate_binder :
  Why3_ptree.binder -> string * string * Parsed.ppure_type
val translate_innfix_ident :
  Why3_ptree.ident -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_infix_ident :
  Why3_ptree.ident -> Loc.t -> Parsed.lexpr -> Parsed.lexpr -> Parsed.lexpr
val translate_qualid : Why3_ptree.qualid -> Parsed.lexpr
val translate_apply : Parsed.lexpr -> Parsed.lexpr -> Loc.t -> Parsed.lexpr
val translate_idapp :
  Why3_ptree.qualid -> Parsed.lexpr list -> Loc.t -> Parsed.lexpr
val translate_term : Why3_ptree.term -> Parsed.lexpr

