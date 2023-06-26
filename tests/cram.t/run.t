  $ export BUILD_PATH_PREFIX_MAP="SRC=$(dirname $(dirname $(dirname $(dirname $(which alt-ergo))))):$BUILD_PATH_PREFIX_MAP"
  $ echo '(check-sat)' | alt-ergo --inequalities-plugin does-not-exist -i smtlib2 -o smtlib2
  alt-ergo: ; Fatal Error: [Dynlink] Loading the 'inequalities' reasoner (FM module) plugin in "does-not-exist" failed!
            >> Failure message: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure(\"$TESTCASE_ROOT/does-not-exist: cannot open shared object file: No such file or directory\")")
  [125]
