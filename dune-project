(lang dune 2.0)

; Since we want to generate opam files we need to provide informations ;
(generate_opam_files true)

(name alt-ergo)
(version dev)
(authors "Alt-Ergo developers")
(maintainers "Alt-Ergo developers")
(source (github OCamlPro/alt-ergo))
; Not specifying bug_reports since it defaults to the github issue page
(homepage "https://alt-ergo.ocamlpro.com/")
(documentation "https://ocamlpro.github.io/alt-ergo")

(using menhir 2.0)

; First package, the alt-ergo binary

(package
 (name alt-ergo)
 (synopsis "The Alt-Ergo SMT prover")
 (description "\
Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on https://alt-ergo.ocamlpro.com/")
 (depends
  (ocaml (>= 4.04.0))
  (dune (>= 2.0))
  (alt-ergo-lib (= :version))
  (alt-ergo-parsers (= :version))
   menhir
   cmdliner
 )
)

; Second package, the alt-ergo gui binary

(package
 (name altgr-ergo)
 (synopsis "The GUI for the Alt-Ergo SMT prover")
 (description "\
Altgr-Ergo is the graphical interface for the Alt-Ergo SMT prover.

Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on https://alt-ergo.ocamlpro.com/"
 )
 (license "OCamlPro Non-Commercial Purpose License, version 1")

 (depends
  (ocaml (>= 4.04.0))
  (dune (>= 2.0))
  (alt-ergo-lib (= :version))
  (alt-ergo-parsers (= :version))
  lablgtk
  conf-gtksourceview
  cmdliner
 )
)

; Third package, the alt-ergo parsers library

(package
 (name alt-ergo-parsers)
 (synopsis "The Alt-Ergo SMT prover parser library")
 (description "\
This is the parser library used in the Alt-Ergo SMT solver.

Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on http://alt-ergo.ocamlpro.com/"
 )
 (license "OCamlPro Non-Commercial Purpose License, version 1")

 (depends
  (ocaml (>= 4.04.0))
  (dune (>= 2.0))
  (alt-ergo-lib (= :version))
  (psmt2-frontend (>= 0.3))
  (camlzip (>= 1.07))
  menhir
  stdlib-shims
 )
)

; Fourth package, the alt-ergo library

(package
 (name alt-ergo-lib)
 (synopsis "The Alt-Ergo SMT prover library")
 (description "\
This is the core library used in the Alt-Ergo SMT solver.

Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on http://alt-ergo.ocamlpro.com/"
 )
 (license "OCamlPro Non-Commercial Purpose License, version 1")

 (depends
  (ocaml (>= 4.04.0))
  (dune (>= 2.0))
  dune-configurator
  num
  (ocplib-simplex (>= 0.4))
  zarith
  seq
  stdlib-shims
 )
)
