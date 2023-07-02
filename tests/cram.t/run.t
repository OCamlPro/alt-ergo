  $ export BUILD_PATH_PREFIX_MAP="SRC=$(dirname $(dirname $(dirname $(dirname $(which alt-ergo))))):$BUILD_PATH_PREFIX_MAP"
  $ echo '(check-sat)' | alt-ergo --inequalities-plugin does-not-exist -i smtlib2 -o smtlib2
  alt-ergo: ; Fatal Error: [Dynlink] Loading the 'inequalities' reasoner (FM module) plugin in "does-not-exist" failed!
            >> Failure message: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure(\"$TESTCASE_ROOT/does-not-exist: cannot open shared object file: No such file or directory\")")
  [125]

Now we will have some tests for the models. Note that it is okay if the format
changes slightly, you should be concerned with ensuring the semantic is
appropriate here.

  $ alt-ergo --frontend dolmen --produce-models model555.smt2 --no-forced-flush-in-output 2>/dev/null
  
  unknown
  (
    (define-fun x () Int 0)
    (define-fun y () Int 0)
    (define-fun a1 () (Array Int Int) (store (as @a1 (Array Int Int)) 0 0))
  )
