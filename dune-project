(lang dune 3.0)

; Since we want to generate opam files we need to provide informations ;
(generate_opam_files true)

(name alt-ergo-free)
(version 2.4.3)
(authors "Alt-Ergo developers")
(maintainers "Alt-Ergo developers")
(source (github OCamlPro/alt-ergo))
; Not specifying bug_reports since it defaults to the github issue page
(homepage "https://alt-ergo.ocamlpro.com/")
(documentation "https://ocamlpro.github.io/alt-ergo")

(using menhir 2.0)

(package
 (name alt-ergo-free)
 (synopsis "The Alt-Ergo SMT prover")
 (description "\
Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on https://alt-ergo.ocamlpro.com/")
 (depends
  (ocaml (>= 4.05.0))
  menhir
  (cmdliner (and (>= 1.1.0) (< 2.0.0)))
  (psmt2-frontend (>= 0.4))
  (camlzip (>= 1.07))
  stdlib-shims
  dune-configurator
  dune-build-info
  num
  (ocplib-simplex (and (>= 0.4.1) (< 0.5)))
  (zarith (>= 1.4))
  seq
  stdlib-shims
  (odoc :with-doc)
 )
 (conflicts
   alt-ergo
   alt-ergo-lib
   alt-ergo-parsers
   altgr-ergo)
)
