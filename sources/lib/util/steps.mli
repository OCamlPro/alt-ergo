type incr_kind = Matching | Omega | Fourier | Uf | Builtin | Ac

val incr  : incr_kind -> unit
val start : unit -> unit
val stop  : unit -> int

