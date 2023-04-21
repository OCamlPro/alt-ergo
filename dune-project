(lang dune 3.0)

; Since we want to generate opam files we need to provide informations ;
(generate_opam_files true)

(name alt-ergo)
(version 2.4.3)
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
  (ocaml (>= 4.05.0))
  (alt-ergo-lib (= :version))
  (alt-ergo-parsers (= :version))
   menhir
  (cmdliner (>= 1.1.0))
  (odoc :with-doc)
 )
)

(package
  (name alt-ergo-js)
  (synopsis "The Alt-Ergo SMT prover")
  (description "\
Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on https://alt-ergo.ocamlpro.com/")
 (depends
  (ocaml (>= 4.05.0))
  (alt-ergo-lib (= :version))
  (alt-ergo-parsers (= :version))
  (js_of_ocaml (and (>= 4.0.1) (<= 5.0.1)))
  js_of_ocaml-lwt
  js_of_ocaml-ppx
  data-encoding
  zarith_stubs_js
  lwt_ppx
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
  (ocaml (>= 4.05.0))
  (alt-ergo-lib (= :version))
  (alt-ergo-parsers (= :version))
  lablgtk3
  (cairo2 (>= 0.6.4))
  conf-gtksourceview3
  lablgtk3-sourceview3
  (cmdliner (>= 1.1.0))
  (odoc :with-doc)
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
  (ocaml (>= 4.05.0))
  (alt-ergo-lib (= :version))
  (psmt2-frontend (>= 0.4))
  (camlzip (>= 1.07))
  menhir
  stdlib-shims
  (odoc :with-doc)
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
  (ocaml (>= 4.05.0))
  dune-configurator
  dune-build-info
  num
  (ocplib-simplex (and (>= 0.4) (< 0.5)))
  (zarith (>= 1.4))
  seq
  stdlib-shims
  (odoc :with-doc)
 )
)
