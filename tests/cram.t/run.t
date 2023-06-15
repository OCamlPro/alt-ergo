  $ export BUILD_PATH_PREFIX_MAP="SRC=$(dirname $(dirname $(dirname $(dirname $(which alt-ergo))))):$BUILD_PATH_PREFIX_MAP"
  $ echo '(check-sat)' | alt-ergo --inequalities-plugin does-not-exist -i smtlib2 -o smtlib2
  [Error]
          Loading the 'inequalities' reasoner (FM module) in plugin "does-not-exist" failed!
         >> Failure message: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure(\"$TESTCASE_ROOT/does-not-exist: cannot open shared object file: No such file or directory\")")
  alt-ergo: ; Fatal Error: [Dynlink] Trying to load the plugin from "SRC/default/src/bin/text/../lib/alt-ergo/plugins/does-not-exist" failed too!
            >> Failure message: error loading shared library: Dynlink.Error (Dynlink.Cannot_open_dll "Failure(\"SRC/default/src/bin/text/../lib/alt-ergo/plugins/does-not-exist: cannot open shared object file: No such file or directory\")")
  [125]
