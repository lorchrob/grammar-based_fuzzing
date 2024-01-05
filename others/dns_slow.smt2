;;!! Takes 8 minutes to generate an example with no constraints.
;;!! And this is with single resource records, not lists of resource records.

;;; logic
(set-logic BV)
;(set-feature :oracles true)

;;; data-types
(declare-datatype OctetList (
  (Nil)
  (Cons (Head (_ BitVec 8)) (Tail OctetList))
))

(declare-datatype Label (
  (Label (Length (_ BitVec 8)) (Octets OctetList))
))

(declare-datatype LabelList (
  (Nil2)
  (Cons2 (Head Label) (Tail LabelList))
))

(declare-datatype DomainName (
  (Name (Labels LabelList) (Termination (_ BitVec 8)))
))

(declare-datatype DNSQuestion (
  (Question (QNAME DomainName) (QTYPE (_ BitVec 16)) (QCLASS (_ BitVec 16)))
))

(declare-datatype ResourceRecord (
  (Record (NAME DomainName) (TYPE (_ BitVec 16)) (CLASS (_ BitVec 16)) (TTL (_ BitVec 32)) (RDLENGTH (_ BitVec 16)) (RDATA OctetList))
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
    (labels LabelList) 
    (label Label)
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
    (message DNSMessage        ((Message header question record record record)))
    (header  DNSHeader         ((Header bv_16 bv_16 code flag flag flag flag z code bv_16 bv_16 bv_16 bv_16)))
    (question DNSQuestion      ((Question name bv_16 bv_16)))
    (record ResourceRecord     ((Record name bv_16 bv_16 ttl bv_16 octets)))
    (name DomainName           ((Name labels octet)))
    (labels LabelList          (Nil2 (Cons2 label labels)))
    (label Label               ((Label octet octets)))
    (octets OctetList          (Nil (Cons octet octets)))
    (octet (_ BitVec 8)        ((Constant (_ BitVec 8))))
    (bv_16 (_ BitVec 16)        ((Constant (_ BitVec 16))))
    (ttl (_ BitVec 32)         ((Constant (_ BitVec 32))))
    (code (_ BitVec 4)       ((Constant (_ BitVec 4))))
    (flag (_ BitVec 1)           ((Constant (_ BitVec 1))))
    (z (_ BitVec 3)            ((Constant (_ BitVec 3))))
  )
)

;;; Constraints

;;; SyGuS synthesis command
(check-synth)