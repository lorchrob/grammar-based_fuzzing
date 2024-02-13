;;!! Use fixed-length lists

;;; logic
(set-logic BV)

;;; grammar
(synth-fun dns_message () (_ BitVec 871)
  ; declare non-terminals
  (
    (message (_ BitVec 871)) 
    (header (_ BitVec 111)) 
    (question (_ BitVec 136)) ; domain name plus 16*2
    (record (_ BitVec 208)) ; octets plus domain name plus others
    (name (_ BitVec 104)) ; labels plus 8 bit termination
    (labels (_ BitVec 96)) ; fixed size 3 labels
    (label (_ BitVec 32)) ; octets plus 8-bit length
    (octets (_ BitVec 24)) ; fixed size 3 octets
    (octet (_ BitVec 8))
    (bv_16 (_ BitVec 16)) 
    (ttl (_ BitVec 32))
    (code (_ BitVec 4))
    (flag (_ BitVec 1))
    (z (_ BitVec 3))
  ) 
  ; grammar rules
  (
    (message (_ BitVec 871)  ((concat header question record record record)))
    (header  (_ BitVec 111)  ((concat bv_16 bv_16 code flag flag flag flag z code bv_16 bv_16 bv_16 bv_16)))
    (question (_ BitVec 136) ((concat name bv_16 bv_16)))
    (record (_ BitVec 208)   ((concat name bv_16 bv_16 ttl bv_16 octets)))
    (name (_ BitVec 104)     ((concat labels octet)))
    (labels (_ BitVec 96)    ((concat label label label)))
    (label (_ BitVec 32)     ((concat octet octets)))
    (octets (_ BitVec 24)    ((concat octet octet octet)))
    (octet (_ BitVec 8)      ((Constant (_ BitVec 8))))
    (bv_16 (_ BitVec 16)     ((Constant (_ BitVec 16))))
    (ttl (_ BitVec 32)       ((Constant (_ BitVec 32))))
    (code (_ BitVec 4)       ((Constant (_ BitVec 4))))
    (flag (_ BitVec 1)       ((Constant (_ BitVec 1))))
    (z (_ BitVec 3)          ((Constant (_ BitVec 3))))
  )
)

;;; Constraints

;;; SyGuS synthesis command
(check-synth)