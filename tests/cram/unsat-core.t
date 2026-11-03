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
