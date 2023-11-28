  $ echo '(check-sat)' | alt-ergo --inequalities-plugin does-not-exist -i smtlib2 -o smtlib2 2>&1 >/dev/null | sed -E 's/\(\\".*\\"\)//'
  alt-ergo: Fatal Error: [Dynlink] Loading the 'inequalities' reasoner (FM module) plugin in "does-not-exist" failed!
            >> Failure message: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure")

Now we will have some tests for the models. Note that it is okay if the format
changes slightly, you should be concerned with ensuring the semantic is
appropriate here.

  $ alt-ergo --produce-models model555.smt2 --no-forced-flush-in-output 2>/dev/null
  
  unknown
  (
    (define-fun a1 () (Array Int Int) (store (as @a0 (Array Int Int)) 0 0))
    (define-fun x () Int 0)
    (define-fun y () Int 0)
  )

Now we will test some semantic triggers.

  $ alt-ergo -o smtlib2 semantic_triggers.ae 2>/dev/null
  
  unknown
  
  unsat
  
  unsat

And some SMT2 action.

  $ alt-ergo -o smtlib2 --prelude prelude.ae postlude.smt2 2>/dev/null
  
  unknown
  
  unsat
  
  unknown
  
  unsat

Here are some tests to check that we have sane behavior given the insane
combinations of produce-models et al.

First, if model generation is not enabled, we should error out when a
`(get-model)` statement is issued:

  $ echo '(set-logic ALL)(check-sat)(get-model)' | alt-ergo -i smtlib2 -o smtlib2 --continue-on-error 2> /dev/null
  
  unknown
  (error "Model generation disabled (try --produce-models)")

This should be the case Tableaux solver as well:

  $ echo '(set-logic ALL)(check-sat)(get-model)' | alt-ergo --sat-solver Tableaux -i smtlib2 -o smtlib2 --continue-on-error 2> /dev/null
  
  unknown
  (error "Model generation disabled (try --produce-models)")

The messages above mention `--produce-models`, but we can also use
`set-option`.

  $ echo '(set-option :produce-models false)(set-logic ALL)(check-sat)(get-model)' | alt-ergo --produce-models -i smtlib2 -o smtlib2 --continue-on-error 2> /dev/null
  
  unknown
  (error "Model generation disabled (try --produce-models)")

  $ echo '(set-option :produce-models false)(set-logic ALL)(check-sat)(get-model)' | alt-ergo --sat-solver Tableaux -i smtlib2 -o smtlib2 --continue-on-error 2> /dev/null
  
  unknown
  (error "Model generation disabled (try --produce-models)")

And now some cases where it should work (using either `--produce-models` or `set-option`):

  $ echo '(set-logic ALL)(check-sat)(get-model)' | alt-ergo --produce-models -i smtlib2 -o smtlib2 2>/dev/null
  
  unknown
  (
  )

  $ echo '(set-option :produce-models true)(set-logic ALL)(check-sat)(get-model)' | alt-ergo -i smtlib2 -o smtlib2 2>/dev/null
  
  unknown
  (
  )
  $ echo '(set-option :produce-models true)(set-logic ALL)(check-sat)(get-model)' | alt-ergo --sat-solver Tableaux -i smtlib2 -o smtlib2 2>/dev/null
  
  unknown
  (
  )

We now test the --continue-on-error strategy where alt-ergo fails (legitimately) on some commands but keeps running.
  $ echo '(get-info :foo) (set-option :bar) (set-logic ALL) (check-sat)' | alt-ergo -i smtlib2 -o smtlib2 --continue-on-error 2>/dev/null
  unsupported
  
  (error "Invalid set-option")
  
  unknown

Some errors are unescapable though. It its the case of syntax error in commands.
  $ echo '(get-info :foo) (set-option :bar) (exil) (check-sat)' | alt-ergo -i smtlib2 -o smtlib2 --continue-on-error 2>/dev/null
  unsupported
  
  (error "Invalid set-option")
  (error "Error on parsing errors (code 3)")

Let us check that we can parse psmt2 files with a .smt2 extension. No output,
no errors expected.
  $ alt-ergo poly.smt2 --type-only
