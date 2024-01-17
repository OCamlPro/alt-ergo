## unreleased

### Command-line interface

 - Enable FPA theory by default (#1177)
 - Remove deprecated output channels (#782)
 - Deprecate the --use-underscore since it produces models that are not SMT-LIB
   compliant (#805)
 - Add --dump-models-on to dump models on a specific output channel (#838)
 - Use consistent return codes (#842)
 - Add --continue-on-error flag to set the SMT-LIB error behavior (#853)
 - Make dolmen the default value for the --frontend option (#857)
 - Restore functionality to broken `--profiling` option (#947)
 - Add bare-bones support for interactive input in SMT-LIB format (#949)
 - Less confusing behavior on timeout (#982, #984)
 - Add `--strict` option for SMT-LIB compliant mode (#916, #1133)

### SMT-LIB support

 - Add support for the many new SMT-LIB commands (#837, #848, #852, #863, #911,
   #942, #945, #961, #975, #1069)
 - Expose the FPA rounding builtin in the SMT-LIB format (#876, #1135)
 - Allow changing the SAT solver using (set-option) (#880)
 - Add support for the `:named` attribute (#957)
 - Add support for quoted identifiers (#909, #972)
 - Add support for naming lemmas in SMT-LIB syntax (#1141, #1143)

### Model generation

 - Use post-solve SAT environment in model generation, fixing issues where
   incorrect models were generated (#789)
 - Restore support for records in models (#793)
 - Use abstract values instead of dummy values in models where the
   actual value does not matter (#804, #835)
 - Use fresh names for all abstract values to prevent accidental captures (#811)
 - Add support for model generation with the default CDCL solver (#829)
 - Support model generation for the BV theory (#841, #968)
 - Add support for optimization (MaxSMT / OptiSMT) with
   lexicographic Int and Real objectives (#861, #921)
 - Add a SMT-LIB printer for expressions (#952, #981, #1082, #931, #932)
 - Ensure models have a value for all constants in the problem (#1019)
 - Fix a rare soundness issue with integer constraints when model generation is
   enabled (#1025)
 - Support model generation for the ADT theory (#1093, #1153)

### Theory reasoning

 - Add word-level propagators for the BV theory (#944, #1004, #1007, #1010,
   #1011, #1012, #1040, #1044, #1054, #1055, #1056, #1057, #1065, #1073, #1144,
   #1152)
 - Add interval domains and arithmetic propagators for the BV theory (#1058,
   #1083, #1084, #1085)
 - Fix incompleteness issues in the BV solver (#978, #979)
 - Abstract more arguments of AC symbols to avoid infinite loops when
   they contain other AC symbols (#990)
 - Do not make irrelevant decisions in CDCL solver, improving
   performance slightly (#1041)
 - Rewrite the ADT theory to use domains and integrate the enum theory into the
   ADT theory (#1078, #1086, #1087, #1091, #1094, #1138)
 - Rewrite the Intervals module entirely (#1108)

### Internal/library changes

 - Rewrite the Vec module (#607)
 - Move printer definitions closer to type definitions (#808)
 - Mark proxy names as reserved (#836)
 - Use a Zarith-based representation for numbers and bit-vectors (#850, #943)
 - Add native support for (bvnot) in the BV solver (#856)
 - Add constant propagators for partially interpreted functions (#869)
 - Remove `Util.failwith` in favor of `Fmt.failwith` (#872)
 - Add more `Expr` smart constructors (#877, #878)
 - Do not use existential variables for integer division (#881)
 - Preserve `Subst` literals to prevent accidental incompleteness (#886)
 - Properly start timers (#924)
 - Compute a concrete representation of a model instead of performing (#925)
 - Allow direct access to the SAT API in the Alt-Ergo library computations
   during printing (#927)
 - Better handling for step limit (#936)
 - Add a generic option manager to deal with the dolmen state (#951)
 - Expose an imperative SAT API in the Alt-Ergo library (#962)
 - Keep track of the SMT-LIB mode (#971)
 - Add ability to decide on semantic literals (#1027, #1118)
 - Preserve trigger order when parsing quantifiers with multiple trigger
   (#1046).
 - Store domains inside the union-find module (#1119)

### Build and integration

 - Drop support for OCaml <4.08.1 (#803)
 - Use dune-site for the inequalities plugins. External pluginsm ust now be
   registered through the dune-site plugin mechanism in the
   `(alt-ergo plugins)` site to be picked up by Alt-Ergo (#1049).
 - Add a release workflow (#827)
 - Mark the dune.inc file as linguist-generated to avoid huge diffs (#830)
 - Use GitHub Actions badges in the README (#882)
 - Use `dune build @check` to build the project (#887)
 - Enable warnings as errors on the CI (#888)
 - Uniformization of internal identifiers generation (#905, #918)
 - Use an efficient `String.starts_with` implementation (#912)
 - Fix the Makefile (#914)

### Testing

 - Use --enable-assertions in tests (#809)
 - Add a test for push/pop (#843)
 - Use the CDCL solver when testing model generation (#938)
 - Do not test .smt2 files with the legacy frontend (#939)
 - Restore automatic creation of .expected files (#941)

### Documentation

 - Add a new example for model generation (#826)
 - Add a Pygments lexer for the Alt-Ergo native language (#862)
 - Update the current authors (#865)
 - Documentation of the `Enum` theory (#871)
 - Document `Th_util.lit_origin` (#915)
 - Document the CDCL-Tableaux solver (#995)

## v2.5.4

### Bug fixes

* Fix a long-standing soundness issue in the FPA module (#1122, originally
  reported in #1111)
* Dolmen frontend incorrectly allowed semantic triggers outside of theory
  extensions (#1122)

## v2.5.3

### Build
* Require dolmen 0.9 #1050
* Test compatibility for OCaml 5.2 #1059

### New features
* support for the SMT-LIB statement `get-value`

## v2.5.2

### Bug fixes
* Hot fix for a soundness bug related with the `distinct` statement (#890)
* Treat missing values in models as abstract (#860)

## v2.5.1

### Bug fixes
* fix a critical soundness bug with bvnot primitive (#819)

## v2.5.0

### New features
* add context reinitialisation (PR #490)
* add Dolmen frontend (PR #491,#541,#545)
* modernize the support for model generation (PR #530, #614, #659, #703, #614, #609, #755)
* support mutually recursive definitions in the native language (PR #549, #550)
* support of some options of the SMT-LIB statement (set-option) (PR #608)
* support for the (get-model) statement (required the Dolmen frontend) (PR #614)
* support the QF_BV and BV smtlib2 logic (PR #730, #733, #745).
* improve the ite preprocessing (simplification of some ites) (PR #731)

### Build
* update to the new version of ocplib-simplex (0.5)
* remove the support of the deprecated library num. Alt-Ergo only uses Zarith (PR #600)
* remove the deprecated graphical interface (PR #601)

### Bug fixes
* issue 475 -- Catch the exception I_dont_known in instantiation pass of SatML (PR #478)
* fix a memory leak in the vector module (PR #606)

## v2.4.3 (2023-04-14)

### Build
* Restrict the requirement version of Ocplib-simplex (PR #573)
* Dune 3.0 or above required, see https://github.com/ocaml/dune/issues/5563 (PR #575)
* Zarith 1.4 or above required
* Cairo2 0.6.4 or above required
* psmt2-frontend 0.4 or above required
* Using js_of_ocaml with a version between 4.0.1 and 5.0.1 required (PR #575)

### Bug fixes
* Fix soundness issues in the arithmetic reasoner #476, #477, #479 (PR #573)

### Regression fixes
* Remove flattening, see issues #505, #567 (PR #573)
* Using a weak table for the Shostak.combine cache to prevent some regressions (PR #573)

## version 2.4.2, August, 02, 2022

* Minor release

  - Migrating to lablgtk3

  - Update of CI

  - Compatibility with dune.3+

  - Miscellaneous bug fixes (type unification, term purification, ...)

## version 2.4.1, July, 27, 2021

* Minor release

  - Improvement of term purification

  - Implementation of a semantic term construction cache

  - Replacement of Travis-CI by GitHub actions

  - Improvement of documentation

  - Unsoundness fixes


## version 2.4.0, January 22, 2021

* General improvements:

  - Add Sphinx general documentation

* Frontend

  - Switch command line parsing to use cmdliner. Use `--<option name>` instead of `-<option name>`

  - Change supported extension of file with Alt-Ergo's native syntax with `.ae`. `.mlw` and `.why` extension are still supported but depreciated.

  - Add support for smtlib2 incremental commands (push, pop, check-sat-assuming)

  - Add `--input` (resp `--output`) option to manually set the input (resp output) file format

  - Add `--err-formatter` and `--std-formatter` options to set output formatters

  - Add `--pretty-output` option to add better debug formatting and to add colors

  - Check consistency of smt2 status between results and info (if present in input file)

  - Add exponentiation operation, `**` in native Alt-Ergo syntax. The operator is fully interpreted when applied to constants

  - Fix `--steps-count` and improve the way steps are counted (AdaCore contribution)

* Reasoners:

  - Add support for incremental command

  - Add new version of preludes for FPA and B set theory

* Instantiation

  - Add `--instantiation-heuristic` option that can enable lighter or heavier instantiation

  - Reduce the instantiation context (considered foralls / exists) in CDCL-Tableaux to better mimic the Tableaux-like SAT solver

* Build:

  - Update build system with proper dune-project and tree structure

  - A manpage is now installed with the opam installation

  - Add configure option `-static` to configure for statically linked compilation

* Others

  - Add option `--gc-policy` to set the allocation policy of the garbage collector

  - Multiple bugfixes


## version 2.3.2, March 23, 2020


* Minor release:

  -  Fix preludes installation
  -  Fix altgr-ergo building rule
  -  Fix issue with dynlink of parsers


## version 2.3.1, February 18, 2020


* Minor release:

  - Fix issue #248. Avoid double rounding int intervals


## version 2.3.0, February 11, 2019


* General improvements:

  - Switched build system to use dune

  - use flambda optimization options if available

* Frontend:

  - native alt-ergo format now supports algebraic datatypes

  - SMTLIB-2 ADT logic is now supported as well

  - extended/better support for if-then-else and let-bindings
    mixing terms and formulas

  - accept unknown file formats as long as a parser
    is specified on the command line, or the parser associated with
    the default language (that can be modified with option
    -default-lang) is able to parse it

  - '-save'/'-replay-used-context' options now work with multiple
    files to accomodate multiple goals in a single file

  - '-proof' option becomes '-unsat-core'. Now, it shows the names of
    the assertions / axioms / definitions used in the proof instead of
    the formulas themselves

  - '-unsat-mode' changes output to SAT/UNSAT/Unknown rather than
    Valid/Invalid/I don't know. This option is set automatically is
    the PSMT2-frontend library is used

* Reasoners:

  - added support for Algebraic Datatypes

  - improve handling of let and if-then-else bindings

  - there are now 4 core solvers (default is cdcl-tableaux):
    * cdcl : CDCL solver
    * cdcl-tableaux : CDCL extended with Tableau boolean model simplification
    * tableaux : Fonctional SAT solver with Tableau boolean model simplification
    * tableaux-cdcl : Same as Tableaux, but using a CDCL solver for boolean constraints

* Instantiation:

  - Triggers computation is done lazily in the backend

  - Triggers are periodically recomputed with different heuristics

* Data structures:

  - Term, Literal and Formula modules are now merged in a new Expr
    module. This enables arbitrary mixing of terms and formulas as done
    in SMT-LIB2 language

  - A lot of improvements in Expr module: more simplifications for
    quantified formulas, better elimination of let-in construct,
    additional constructs in the backend (iff, If-Then-Else, ...),
    code reviewing and performances improvements ...

## version 2.2.0, April 21, 2018


* Frontend:

  - new experimental support for the SMT2 standard, and for PSMT2: a
    conservative extension of SMT2 with prenex polymorphism

  - Alt-Ergo's library is now compiled (with make) and installed (with
    make install). A small example on how to use it is provided in
    examples/lib_usage.ml

  - extension of Alt-Ergo's native language to support "xor" construct,
    "Let x = form in form", and "If form then term/form else
    term/form". Previously, only "Let x = term in term/form", and "If
    term : Bool then term/form else term/form" were supported

* Instantiation:

  - add a new option "-max-multi-triggers-size <n>" to ignore
    multi-triggers containing "a lot" of terms. Default value for n = 4

  - small improvement in triggers inference

* Reasoners:

  - extending the backend to handle "If-Then-Else" on terms

  - improvements and refactoring in the CDCL SAT solver

  - soundness bugfix in UF module


## version 2.1.0, March 14, 2018


* SAT-solving:

  - important improvements in the CDCL SAT engine, which is now the
    default SAT-solver. Proofs are models generation are currently not
    available with CDCL. The old SAT-solver can be activated with option
    "-sat-solver Tableaux"

* Instantiation:

  - Add a very weak form of matching modulo arithmetic. This can be
    disabled with option "-no-arith-matching"

  - [Formula.mk_forall/exists] remove (big) triggers that are subsumed by smaller ones

  - Simplify quantified formulas when relevant instances/skolems can be deduced
    from the formulas (eg. exists x : int. x = 1 and P(x) ~~> P(1),
    and forall x : int. x <> 1 or P(x) ~~> P(1))

* Frontend:

  - improve handling of multiple goals per file. Add the ability to
    set a timelimit per goal in this case with option
    "-timelimit-per-goal"

  - add the ability to dynamically load new parsers with option
    "-parser".



## version 2.0.0, November 14, 2017


* integration of floating-point arithmetic reasoning: this is done via
  the support of the rounding operator as done in the Gappa tool. FPA
  reasoning can be enabled by calling Alt-Ergo as follows:

  alt-ergo -use-fpa -prelude fpa-theory-2017-01-04-16h00.why file.why

  where fpa-theory-2017-01-04-16h00.why is a prelude distributed with
  Alt-Ergo. More details about the integration are given in this
  paper: https://hal.inria.fr/hal-01522770, and dditional benchmarks
  can be found here:
  https://gitlab.com/OCamlPro-Iguernlala/Three-Tier-FPA-Benchs

* a new lightweight reasoning step before SAT solving that enables a
  kind of backward reasoning/goal unfolding (can be disabled with
  option -no-backward)

* integration of a simple cache mechanism for unit facts in the SAT
  (learnt clauses, assumed facts, instances, theory deductions, ...)
  to improve BCP (can be disabled with option -no-sat-learning)

* the code of the profiler is now integrated in Alt-Ergo and is
  statically linked

* deep code refactoring. In particular, one can easily build an
  Alt-Ergo library or define/register a new parser

* add the ability to parse preludes with -prelude <prelude_1.why> ...
  -prelude <prelude_n.why>

* add the ability to disable weak pointers in hash-consing module
  using option -disable-weaks (useful for more determinism)

* GUI: goals are now shown in positive form

* bugfix related to -timelimit option (use of ITIMER_VIRTUAL instead
  of ITIMER_REAL except for the GUI)

* bugfix in UF related to normalization of terms in presence of AC
  symbols

* new options -no-decisions and -no-fm to disable decisions in the SAT
  and the Fourier-Motzkin algorithm, respectively

* new improvements and heuristics in the SAT, terms, formulas,
  congruence closure, profiler, ...

* update licensing: most files are now licensed under the terms of the
  Apache license v2. Some recent OCamlPro additions are licensed under
  the terms of the OCamlPro Non-Commercial Purpose License v1

## version 1.30, November 21, 2016

* experimental support for models generation (for more details, see
   http://www.ocamlpro.com/2016/11/21/release-of-alt-ergo-1-30-with-experimental-support-for-models-generation/).

* simplify formulas of the form "forall x : t. x <> t or F" when t
  does not contain x. The only relevant instance in this case is
  "(x <> t or F) {x |-> t}". In a similar way, this allows to simplify
  formulas of the form "exists x : t. x = t and F" to "F {x |-> t}".

* integration of general simplex in IntervalCalculus based on
  ocplib-simplex.

* important parts of Intervals and IntervalCalculus have been
  rewritten and improved.

* improve tightening of intervals for non-linear variables, and of the
  CP-like loop.

* extend Fourier-Motzkin to deduce more bounds based on relational
  dependencies of the form "c * x <= (Sum_i d_i * y_i) + e"

* various improvements in the default SAT solver, Term, Formula,
  IntervalCalculus, Matching, Numbers, case-split, ...

* various (soundness and/or completeness) bug fixes in Uf, Intervals,
  IntervalCalculus, Theory, Formula, type-checking, Triggers,
  fm-simplex and satML, ...

* new option "-inst-after-bj" that forces an instantiation round after
  each backtracking/backjumping in the default SAT solver.

* new option "-no-backjumping" that disables backjumping in the
  default SAT solver (for debugging).

* new option "-fm-cross-limit" that controls the number of
  intermediate inequalities produces by Fourier-Motzking. Default
  value is 10,000.

* new option "-no-ac" to be able to deactivate the AC theory

* new option "-no-NLA" that disables non-linear arithmetic reasoning
   (*, /, %). Non-linear multiplication remains AC.


## version 1.20, February 09, 2016

* default value of option -age-bound increased from 10 to 50

* bugfix when using option --all-models

* improvements in Matching: a set of instances may cause more than one
  conflict. It's better to detect the more precise one

* remove case-split limit for the theory of arrays

* bugfix in the profiler plugin

* improvements in the default SAT solver


## version 1.10, October 19, 2015

* Improvements and bug fixes in the satML plugin

* Improvement of the solver of linear arithmetic in presence of
  non-linear arithmetic parts in the equations to be solved

* Many improvements in case-split analysis. In particular, this is now
  performed by explicit calls from the SAT solver. Its behavior can be
  controlled with the new option "-case-split-policy". Possible values
  for this option are: "after-theory-assume" (default),
  "before-matching", and "after-matching".

* Alt-Ergo can now be called on zipped files (eg. <file>.mlw.zip or
  <file>.why.zip). Decompression is done on the fly with camlzip.

* Soundness bug fixes in arithmetic, interval calculus, union-find,
  ...

* Code reviewing/refactoring/rewriting/optimization in many parts of
  the solver


## version 1.00, January 29, 2015

* General Improvements:

   ** theories data structures: semantic values (internal theories
      representation of terms) are now hash-consed. This enables the
      use of hash-based comparison (instead of structural comparison)
      when possible

   ** theories combination: the dispatcher component, that sends
      literals assumed by the SAT solver to different theories
      depending on whether these literals are equalities,
      disequalities or inequalities, has been re-implemented. The new
      code is much simpler and enables new optimizations and
      factorizations

   ** case-split analysis: we made several improvements in the
      heuristics of the case-split analysis mechanism over finite
      domains

   ** explanations propagation: we improved explanations propagation
      in congruence closure and linear arithmetic algorithms. This
      makes the proofs faster thanks to a better back-jumping in the
      SAT solver part

   ** linear integer arithmetic: we re-implemented several parts of
      linear arithmetic and introduced important improvements in the
      Fourier-Motzkin algorithm to make it run on smaller sub-problems
      avoiding some redundant executions. These optimizations allowed
      a significant speed up on our internal benchmarks

   ** data structures: we optimized hash-consing and some functions in
      the "formula" and "literal" modules

   ** SAT solving: we made a lot of improvements to the default
       SAT-solver and to the SatML plugin. In particular, the decision
       procedure part now receives facts (literals) in bulk from the
       solvers, rather than individually, trimming the costs of
       intermediate calls to theories reasoners, such as
       Fourier-Motzkin

   ** Matching: we extended the E-matching algorithm to also perform
      matching modulo the theory of records. In addition, we
      simplified matching heuristics and optimized the E-matching
      process to avoid computing the same instances several times

   ** Memory management: thanks to the ocp-memprof tool
      (http://memprof.typerex.org/), we identified some parts of
      Alt-Ergo that needed some improvements in order to avoid useless
      memory allocations, and thus unburden the OCaml garbage
      collector

   ** the function that retrieves the used axioms and predicates (when
      option 'save-used-context' is set) has been improved


* Bug Fixes:

   ** 6 in the "inequalities" module of linear arithmetic

   ** 4 in the "formula" module

   ** 3 in the "ty" module used for types representation and
      manipulation

   ** 2 in the "theories front-end" module that interacts with the
      SAT solvers

   ** 1 in the "congruence closure" algorithm

   ** 1 in "existential quantifiers elimination" module

   ** 1 in the "type-checker"

   ** 1 in the "AC theory" of associative and commutative function
      symbols

   ** 1 in the "union-find" module


* New OCamlPro Plugins:

  ** profiling plugin: when activated, this plugin records and prints
    some information about the current execution of Alt-Ergo every 'n'
    seconds: In particular, one can observe a module being activated,
    a function being called, the amount of time spent in every
    module/function, the current decision/instantiation level, the
    number of decisions/instantiations that have been made so far, the
    number of case-splits, of boolean/theory conflicts, of assumptions
    in the decision procedure, of generated instances per axiom, ...

  ** fm-simplex plugin: when activated, this plugin is used instead of
    the Fourier-Motzkin method to infer bounds for linear integer
    arithmetic affine forms (which are used in the case-split analysis
    process). This module uses the Simplex algorithm to simulate
    particular runs of Fourier-Motzkin. In practice, the new algorithm
    scales better on linear integer arithmetic problems containing
    lots of inequalities


* New Options:

  -version-info: prints some information about this version of
   Alt-Ergo (release and compilation dates, release commit ID)

  -no-theory: deactivate theory reasoning. In this case, only the
   SAT-solver and the matching parts are used

  -inequalities-plugin: specify a plugin to use, instead of the
  "default" Fourier-Motzkin algorithm, to handle inequalities of
  linear arithmetic

  -tighten-vars: when this option is set, the Fm-Simplex plugin will
   try to infer bounds for integer variables as well. Note that this
   option may be very expensive

  -profiling-plugin: specify a profiling plugin to use to monitor an
   execution of Alt-Ergo

  -profiling <delay>: makes the profiling module prints its information
   every <delay> seconds

  -no-tcp: deactivate constraints propagation modulo theories


* Removed Capabilities:

  ** the pruning module used in the frontend is not available anymore

  ** the SMT and SMT2 front-ends have been removed. We plan to implement a
     new front-end for SMT2 in upcoming releases


## version 0.99.1, December 30, 2014

  o the "SAT solving" part can now be delegated to an external plugin;

  o new experimental SAT solver based on mini-SAT, provided as a
  plugin. This solver is, in general, more efficient on ground
  problems;

  o heuristics simplification in the default SAT solver and in the
  matching (instantiation) module;

  o re-implementation of internal literals representation;

  o improvement of theories combination architecture;

  o rewriting some parts of the formulas module;

  o bugfixes in records and numbers modules;

  o new option "-no-Ematching" to perform matching without equality
  reasoning (i.e. without considering "equivalence classes"). This
  option is very useful for benchmarks coming from Atelier-B;

  o two new experimental options: "-save-used-context" and
  "-replay-used-context". When the goal is proved valid, the first option
  allows to save the names of useful axioms into a ".used" file. The
  second one is used to replay the proof using only the axioms listed
  in the corresponding ".used" file. Note that the replay may fail
  because of the absence of necessary ground terms generated by
  useless axioms (that are not included in .used file) during the
  initial run.

## version 0.95.2, September 20th, 2013


  o Alt-Ergo is now maintained and distributed by OCamlPro, while
    academic research is conducted in partnership with the VALS team
    (LRI),
  o source code is reorganized into sub-directories,
  o quantifiers instantiation heuristics are simplified,
  o bug-fixes in matching, nums, records, sums,
  o improvement of the GUI when opening big files.

## version 0.95.1, March 05th, 2013

  o bug fixes (existantial elimination, Euclidean division)
  o minor enhancement (transformation of boolean equalities into equivalences)
  o minor enhancement (sort axioms/definitions instances according to their size)

## version 0.95, January 11th, 2013

  + Main changes in the solver:
  -----------------------------

    o new combination method for Shostak solvers

    o improvement of non-linear multiplication distribution over addition

    o input language extension: polymorphic declaration are now allowed (logic x: 'a)

    o input language extension: the types of terms can now be forced in a formula using the construct <term> : <type> (see man for an example)

    o input language modification: a label should be a string. The construct <label> : <term> is replaced by "<label>" : <term>

    o new keywords in the syntax: inversion, check, cut and include

    o experimental options for theories models generation:
        -model option: model on labeled terms
        -complete-model option: complete model

    o -timelimit n option: set the time limit to n seconds (not supported on Windows)

    o bug fixes

  + Main changes in the graphical interface:
  ------------------------------------------

    o the number of instances for each axiom are now shown on the right of the GUI

    o the number of instances of each axiom can be limited by the user

    o the modifications made in the GUI can now be saved in a session file <f>.agr

    o session files can be replayed with -replay option

    o models can be displayed in the GUI

    o unsat-cores (-proof option) can be used to simplify the context


## version 0.94, December 2nd, 2011

  o the theory of records replaces the theory of pairs
  o bug fixes
    (intervals, term data-structure, stack-overflows, matching,
     existentials, distincts, CC, GUI)
  o improvements
     (SMT-Lib2 front-end, intervals, case-splits,
      triggers, lets)
  o multiset ordering for AC(X)
  o manual lemma instantiation in the GUI


## version 0.93.1, May 9th, 2011

  o bug fixes (distinct, let-in, explanations)

## version 0.93, April 12th, 2011

  o -steps <i> stops Alt-Ergo after a given number of steps
  o -max-split option to limit the number of case-splits
  o new polymorphic theory of arrays: ('a, 'b) farray
  o explanations (-proof option)
  o Built-in support for enumeration types
  o graphical frontend (altgr-ergo), needs to be compiled with make
    gui && make install-gui
  o new predicate distinct (a,b,c, ...) to express that constants
    a,b,c,... are pairwise distinct
  o new constructs: let x = <term> in <term>
                    let x = <term> in <formula>
  o partial support for / (division) operator
  o bug fixes

## version 0.92.2, October 22nd, 2


  o New built-in syntax for the theory of arrays
  o Fixes a bug in the arithmetic module
  o Allows folding and unfolding of predicate definitions
  o Fixes other bugs

## version 0.91, May 19th, 2010

  o experimental support for the theory of functional polymorphic
    arrays with the -arrays option
  o the -pairs option should now be used for the built-in support of
    polymorphic pairs
  o support the equality part of the omega test with the -omega option
  o partial support for non-linear arithmetics
  o support case split on integer variables
  o new support for Euclidean division and modulo operators
  o new environment variable ERGOLIB to specify the library directory

## version 0.9, July 17th, 2009

  o support AC symbols
  o support for C-like hexadecimal floating-point constants
  o handle the division operator

## version 0.8, July 21st, 2008

  o pretty output with the -color option
  o the SAT solver part is now equipped with a backjumping mechanism
  o now handles the flet and let SMT-lib constructs
  o goal directed strategy
  o pruning strategy (-select option)
  o incremental strategy for instantiation of lemmas
  o fail if a parameter is bound twice in a definition
  o treatment of existential formulas have been slightly improved
  o decision procedure for polymorphic pairs
  o decision procedure for bit-vectors
  o combination scheme for several decision procedures

## version 0.7.3, March 5th, 2008

  o renamings in the interfaces
  o provides an API for alt-ergo (make api or make api.byte)
  o handles the modulo operator (%) as an uninterpreted symbol
  o allow labels on any term, not only on predicates

## version 0.7, October 11th, 2007
  o trigger construction has been improved
  o preliminary implementation of combination scheme (Arithmetic+pairs)
  o the SAT loop has been improved


## version 0.6, February 1st, 2007

  o new CC(X) architecture (it can know directly handle relation symbols)
  o fully handles the polymorphism of the logic

## version 0.5, October 12th, 2006
  o first (beta) release
