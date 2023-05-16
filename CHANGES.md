## v2.4.3 (2023-04-14)

# Build
* Restrict the requirement version of Ocplib-simplex (PR #573)
* Dune 3.0 or above required, see https://github.com/ocaml/dune/issues/5563 (PR #575)
* Zarith 1.4 or above required
* Cairo2 0.6.4 or above required
* psmt2-frontend 0.4 or above required
* Using js_of_ocaml with a version between 4.0.1 and 5.0.1 required (PR #575)

# Bug fixes
* Fix soundness issues in the arithmetic reasoner #476, #477, #479 (PR #573)

# Regression fixes
* Remove flattening, see issues #505, #567 (PR #573)
* Using a weak table for the Shostak.combine cache to prevent some regressions (PR #573)
