The `--unsat-core` option can be used to produce unsat cores with the legacy
Tableaux solver.

  $ cat > input.ae << EOF
  > 
  > logic x, y : int
  > 
  > axiom h_x_0 : x = 0
  > 
  > axiom h_y_0 : y = 0
  > 
  > goal g : not (x = 1)
  > EOF

  $ alt-ergo --sat-solver Tableaux --unsat-core input.ae -o smtlib2 2>/dev/null
  
  unsat
  unsat-core:
    h_x_0
  

Unsat cores can be checked with the `-d unsat-core` option.

  $ alt-ergo --sat-solver Tableaux --unsat-core -d unsat-core input.ae -o smtlib2 2>&1 | grep -Ev '^; File '
  
  ; 
  unsat
 
Unsat cores can be used in the SMT-LIB format as well.

  $ cat > input.smt2 << EOF
  > (set-logic ALL)
  > (set-option :produce-unsat-cores true)
  > (declare-const x Int)
  > (declare-const y Int)
  > (assert (! (= x 0) :named h_x_0))
  > (assert (! (= y 0) :named h_y_0))
  > (assert (= x 1))
  > (check-sat)
  > (get-unsat-core)
  > EOF

  $ alt-ergo --sat-solver Tableaux input.smt2 2>/dev/null
  
  unsat
  (h_x_0)

Unsat cores also work with the default CDCL-Tableaux solver.

  $ alt-ergo --unsat-core input.ae -o smtlib2 2>/dev/null
  
  unsat
  unsat-core:
    h_x_0
  

  $ alt-ergo --unsat-core -d unsat-core input.ae -o smtlib2 2>/dev/null
  
  unsat

  $ alt-ergo input.smt2 2>/dev/null
  
  unsat
  (h_x_0)

Unsat core generation (but not printing) can also be enabled from the command
line with `--produce-unsat-cores`.

  $ cat > input.smt2 << EOF
  > (set-logic ALL)
  > (declare-const x Int)
  > (declare-const y Int)
  > (assert (! (= x 0) :named h_x_0))
  > (assert (! (= y 0) :named h_y_0))
  > (assert (= x 1))
  > (check-sat)
  > (get-unsat-core)
  > EOF

  $ alt-ergo input.smt2 2>/dev/null
  
  unsat
  (error "input.smt2:8.0: Unsat core generation disabled (try --produce-unsat-cores)")
  [1]

  $ alt-ergo --produce-unsat-cores input.smt2 2>/dev/null
  
  unsat
  (h_x_0)
