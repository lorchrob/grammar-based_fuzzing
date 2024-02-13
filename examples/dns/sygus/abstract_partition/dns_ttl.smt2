;;; logic
(set-logic LIA)
;(set-feature :oracles true)

;;; data-types
(declare-datatype Top (
  (Message (TTL Int)
  )
))

;;; grammar
(synth-fun dns_packet () Top
  ; declare non-terminals
  (
    (message Top) 
    (int Int)
  ) 
  ; grammar rules
  (
    (message Top    ((Message int)))
    (int Int    ((Constant Int)))
  )
)

;;; Constraints
; 1. TTL is >= 0 (signed)
(define-fun c1 ((message Top)) Bool
  (match message (
    ((Message ttl) (> ttl 0))
  ))
)
(constraint (c1 dns_packet))

;;; SyGuS synthesis command
