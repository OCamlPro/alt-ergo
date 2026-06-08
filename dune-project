(lang dune 3.14)
(version dev)

; Since we want to generate opam files we need to provide informations ;
(generate_opam_files true)

; For plugins and preludes
(using dune_site 0.1)

(name alt-ergo)
(authors "Alt-Ergo developers <alt-ergo@ocamlpro.com>")
(maintainers "Alt-Ergo developers <alt-ergo@ocamlpro.com>")
(source (github OCamlPro/alt-ergo))
; Not specifying bug_reports since it defaults to the github issue page
(homepage "https://alt-ergo.ocamlpro.com/")
(documentation "https://ocamlpro.github.io/alt-ergo")

(using menhir 2.0)

(package
 (name alt-ergo)
 (synopsis "The Alt-Ergo SMT prover")
 (description "\
Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on https://alt-ergo.ocamlpro.com/")
 (depends
  (ocaml (>= 4.08.1))
  dune
  (alt-ergo-lib (= :version))
  dune-site
  (cmdliner (>= 2.0))
  (odoc :with-doc)
  (camlzip (>= 1.07))
  lwt_ppx
  js_of_ocaml-lwt
  js_of_ocaml-ppx
  data-encoding
  zarith_stubs_js
 )

 (sites (share preludes) (lib plugins))
)

(package
 (name alt-ergo-js)
 (synopsis "The Alt-Ergo JavaScript artifacts")
 (depends
  (alt-ergo (= :version))
  (alt-ergo-lib (= :version))
  (js_of_ocaml (and (>= 6.0.0) (<= 6.2.0)))
  js_of_ocaml-lwt
  js_of_ocaml-ppx
  data-encoding
  (zarith_stubs_js (>= 0.16.1))
  lwt_ppx))

(package
 (name alt-ergo-lib)
 (synopsis "The Alt-Ergo SMT prover library")
 (description "\
This is the core library used in the Alt-Ergo SMT solver.

Alt-Ergo is an automatic theorem prover of mathematical formulas. It was developed at LRI, and is now maintained at OCamlPro.

See more details on http://alt-ergo.ocamlpro.com/"
 )
 (license "LicenseRef-OcamlPro-Non-Commercial")

 (depends
  (ocaml (>= 4.08.1))
  dune
  dune-build-info
  (dolmen (or (>= 0.10) (= dev)))
  (dolmen_type (or (>= 0.10) (= dev)))
  (dolmen_loop (or (>= 0.10) (= dev)))
  (ocplib-simplex (>= 0.5.1))
  (zarith (>= 1.11))
  seq
  (fmt (>= 0.9.0))
  stdlib-shims
  (ppx_blob (>= 0.7.2))
  (camlzip (>= 1.07))
  (odoc :with-doc)
  ppx_deriving
  (qcheck (and :with-test (= 0.25)))
 )
 (conflicts
  (ppxlib (< 0.30.0))
  (result (< 1.5))
 )
)
