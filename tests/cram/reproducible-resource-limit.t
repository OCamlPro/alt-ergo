The `:reproducible-resource-limit` option can be set using the `(set-option)`
command. It applies independently to all the subsequent calls to `(get-sat)`.

  $ cat > input.smt2 << EOF
  > (set-logic ALL)
  > 
  > (declare-const x Int)
  > (declare-const y Int)
  > 
  > (assert (> x y))
  > (assert (< x 0))
  > (assert (> y 0))
  > 
  > ; If the limit is too low, we should return unknown
  > (set-option :reproducible-resource-limit 1)
  > (check-sat)
  > (get-info :reason-unknown)
  > 
  > ; Trying again does not help
  > (check-sat)
  > (get-info :reason-unknown)
  > 
  > ; Disabling the limit should return unsat
  > (set-option :reproducible-resource-limit 0)
  > (check-sat)
  > EOF

  $ alt-ergo input.smt2 2>/dev/null
  
  unknown
  (:reason-unknown (:step-limit 2))
  
  unknown
  (:reason-unknown (:step-limit 2))
  
  unsat

The reproducible resource limit can also be set using the
`--reproducible-resource-limit` command-line option. It can then be overriden
using `(set-option)` in the script.

  $ cat > nolimit.smt2 << EOF
  > (set-logic ALL)
  > 
  > (declare-const x Int)
  > (declare-const y Int)
  > 
  > (assert (> x y))
  > (assert (< x 0))
  > (assert (> y 0))
  > 
  > (check-sat)
  > (get-info :reason-unknown)
  > 
  > (check-sat)
  > (get-info :reason-unknown)
  > 
  > (set-option :reproducible-resource-limit 0)
  > (check-sat)
  > EOF

  $ alt-ergo --reproducible-resource-limit 1 nolimit.smt2 \
  >   2>/dev/null
  
  unknown
  (:reason-unknown (:step-limit 2))
  
  unknown
  (:reason-unknown (:step-limit 2))
  
  unsat

The global step limit cannot be overridden and always applies.

  $ alt-ergo --steps-bound 1 nolimit.smt2 \
  >   2>/dev/null
  
  unknown
  (:reason-unknown (:step-limit 2))
  
  unknown
  (:reason-unknown (:step-limit 2))
  
  unknown

The resource limit also works within an incremental context.

  $ cat > incremental.smt2 << EOF
  > (set-logic ALL)
  > 
  > (declare-const x Int)
  > (declare-const y Int)
  > 
  > (push 1)
  > 
  > (assert (> x y))
  > (assert (< x 0))
  > (assert (> y 0))
  > 
  > (set-option :reproducible-resource-limit 1)
  > (check-sat)
  > (get-info :reason-unknown)
  > 
  > (set-option :reproducible-resource-limit 0)
  > (check-sat)
  > EOF

  $ alt-ergo incremental.smt2 2>/dev/null
  
  unknown
  (:reason-unknown (:step-limit 2))
  
  unsat
