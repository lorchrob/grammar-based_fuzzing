;;; logic
(set-logic ALL)

(set-feature :oracles true)

;;; grammar
(synth-fun grammar () (_ BitVec 16)
  ; declare non-terminals
  ((start (_ BitVec 16))) 
  ; grammar rules
  ((start (_ BitVec 16) ((Constant (_ BitVec 16)))))
)

;;; Constraints
(declare-oracle-fun oracle-identity ((_ BitVec 16)) (_ BitVec 16) oracle_binary)
(constraint (= grammar (oracle-identity #b0000000000000000)))

;;; SyGuS synthesis command
(check-synth)

