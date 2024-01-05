;;; logic
(set-logic ALL)
(set-feature :oracles true)

;;; grammar
(synth-fun grammar () Int
  ; declare non-terminals
  ((start Int)) 
  ; grammar rules
  ((start Int ((Constant Int))))
)

;;; Constraints
(declare-oracle-fun oracle-identity (Int) Int oracle_binary)
(constraint (= grammar (oracle-identity 5)))

;;; SyGuS synthesis command
(check-synth)

