;;; logic
(set-logic BV)
;(set-feature :oracles true)

;;; data-types
(declare-datatype OctetList (
  (Nil)
  (Cons (Head (_ BitVec 8)) (Tail OctetList))
))

(declare-datatype DomainName (
  (Name)
))

(declare-datatype DNSQuestion (
  (Question (QNAME DomainName) (QTYPE (_ BitVec 16)) (QCLASS (_ BitVec 16)))
))

(declare-datatype RDATA (
  (Rdata)
))

(declare-datatype ResourceRecord (
  (Record (NAME DomainName) (CLASS (_ BitVec 16)) (TTL (_ BitVec 32)) (RDATA RDATA))
))

(declare-datatype DNSHeader (
  (Header (ID (_ BitVec 16)) (QR (_ BitVec 16)) (Opcode (_ BitVec 4)) 
    (AA (_ BitVec 1)) (TC (_ BitVec 1)) (RD (_ BitVec 1)) (RA (_ BitVec 1)) 
    (Z (_ BitVec 3)) (RCODE (_ BitVec 4)) 
    (QDCOUNT (_ BitVec 16)) (ANCOUNT (_ BitVec 16)) (NSCOUNT (_ BitVec 16)) (ARCOUNT (_ BitVec 16))
  )
))

(declare-datatype DNSMessage (
  (Message (Header DNSHeader) 
    (Question DNSQuestion) 
    (Answer ResourceRecord) 
    (Authority ResourceRecord) 
    (Additional ResourceRecord)
  )
))

;;; grammar
(synth-fun dns_message () DNSMessage
  ; declare non-terminals
  (
    (message DNSMessage) 
    (header DNSHeader) 
    (question DNSQuestion) 
    (record ResourceRecord) 
    (name DomainName) 
    (rdata RDATA)
    (octets OctetList) 
    (octet (_ BitVec 8))
    (bv_16 (_ BitVec 16)) 
    (ttl (_ BitVec 32))
    (code (_ BitVec 4))
    (flag (_ BitVec 1))
    (z (_ BitVec 3))
  ) 
  ; grammar rules
  (
    (message DNSMessage    ((Message header question record record record)))
    (header  DNSHeader     ((Header bv_16 bv_16 code flag flag flag flag #b000 code bv_16 bv_16 bv_16 bv_16)))
    (question DNSQuestion  ((Question name bv_16 bv_16)))
    (record ResourceRecord ((Record name bv_16 ttl rdata)))
    (name DomainName       (Name))
    (rdata RDATA           (Rdata))
    (octets OctetList      (Nil (Cons octet octets)))
    (octet (_ BitVec 8)    ((Constant (_ BitVec 8))))
    (bv_16 (_ BitVec 16)   ((Constant (_ BitVec 16))))
    (ttl (_ BitVec 32)     ((Constant (_ BitVec 32))))
    (code (_ BitVec 4)     ((Constant (_ BitVec 4))))
    (flag (_ BitVec 1)     ((Constant (_ BitVec 1))))
    (z (_ BitVec 3)        ((Constant (_ BitVec 3))))
  )
)

;;; Constraints
; 1. TTL is >= 0 (signed)
(define-fun c1 ((record ResourceRecord)) Bool
  (match record (
    ((Record name class ttl rdata) (= (bvand #b10000000000000000000000000000000 ttl) #x00000000))
  ))
)
(define-fun c2 ((message DNSMessage)) Bool
  (match message (
    ((Message header query answer authority additional) (and (c1 answer) (c1 authority) (c1 additional)))
  ))
)
(constraint (c2 dns_message))

; 2. Z field is zero'd out
; Encoded directly in the grammar

;;; SyGuS synthesis command
(check-synth)