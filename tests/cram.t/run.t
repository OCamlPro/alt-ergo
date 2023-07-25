  $ export BUILD_PATH_PREFIX_MAP="SRC=$(dirname $(dirname $(dirname $(dirname $(which alt-ergo))))):$BUILD_PATH_PREFIX_MAP"
  $ echo '(check-sat)' | alt-ergo --inequalities-plugin does-not-exist -i smtlib2 -o smtlib2 2>&1 >/dev/null | sed -E 's/\(\\".*\\"\)//'
  alt-ergo: ; Fatal Error: [Dynlink] Loading the 'inequalities' reasoner (FM module) plugin in "does-not-exist" failed!
            >> Failure message: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure")

Now we will have some tests for the models. Note that it is okay if the format
changes slightly, you should be concerned with ensuring the semantic is
appropriate here.

  $ alt-ergo --frontend dolmen --produce-models model555.smt2 --no-forced-flush-in-output 2>/dev/null
  
  unknown
  (
    (define-fun a1 () (Array Int Int)
     (store ((as const (Array Int Int)) 0) 0 0))
    (define-fun x () Int 0)
    (define-fun y () Int 0)
  )

Now we will test some semantic triggers.

  $ alt-ergo --frontend legacy -o smtlib2 semantic_triggers.ae 2>/dev/null
  
  unknown
  
  unsat
  
  unsat
  $ alt-ergo --frontend dolmen -o smtlib2 semantic_triggers.ae 2>/dev/null
  
  unknown
  
  unsat
  
  unsat

And some SMT2 action.

  $ alt-ergo --frontend dolmen -o smtlib2 --prelude prelude.ae postlude.smt2 2>/dev/null
  
  unknown
  
  unsat
  
  unknown
  
  unsat

Here are some tests to check that we have sane behavior given the insane
combinations of produce-models et al.

First, if model generation is not enabled, we should error out when a
`(get-model)` statement is issued:

  $ echo '(get-model)' | alt-ergo --frontend dolmen -i smtlib2 -o smtlib2
  (error "Model generation disabled (try --produce-models)")

This should be the case Tableaux solver as well:

  $ echo '(get-model)' | alt-ergo --frontend dolmen --sat-solver Tableaux -i smtlib2 -o smtlib2
  (error "Model generation disabled (try --produce-models)")

The messages above mention `--produce-models`, but we can also use
`set-option`. This requires the Tableaux solver, however:

  $ echo '(get-model)' | alt-ergo --frontend dolmen --produce-models -i smtlib2 -o smtlib2
  (error "No model produced.")

  $ echo '(set-option :produce-models true)(get-model)' | alt-ergo --frontend dolmen --sat-solver Tableaux -i smtlib2 -o smtlib2
  (error "No model produced.")

  $ echo '(set-option :produce-models true)(get-model)' | alt-ergo --frontend dolmen -i smtlib2 -o smtlib2
  (error "Model generation requires the Tableaux solver (try --produce-models)")
  (error "Model generation disabled (try --produce-models)")

And now some cases where it should work (using either `--produce-models` or
`Tableaux` with `set-option`):

  $ echo '(check-sat)(get-model)' | alt-ergo --frontend dolmen --produce-models -i smtlib2 -o smtlib2 2>/dev/null
  
  unknown
  (
  )

  $ echo '(set-option :produce-models true)(check-sat)(get-model)' | alt-ergo --frontend dolmen --sat-solver Tableaux -i smtlib2 -o smtlib2 2>/dev/null
  
  unknown
  (
  )
