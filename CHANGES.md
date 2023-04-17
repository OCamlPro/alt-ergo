## v2.4.3 (2023-04-14)

# Build
* Restrict the requirement version of Ocplib-simplex (PR #573)
* Dune 2.8 or above is required (PR #575)
* Using js_of_ocaml with a version between 4.0.1 and 5.0.1 is required for
  the new package alt-ergo-js (PR #575)

# Bug fixes
* Fix soundness issues in the arithmetic reasoner #476, #477, #479 (PR #573)

# Regression fixes
* Remove flattening, see issues #505, #567 (PR #573)
* Using a weak table for the Shostak.combine cache to prevent some regressions (PR #573)
