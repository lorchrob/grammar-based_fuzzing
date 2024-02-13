;;!! Use fixed-length lists

;;; logic
(set-logic BV)

;;; datatypes, only for documentation (not used in grammar)
(declare-datatype OctetList (
  (List (fst (_ BitVec 8)) (snd (_ BitVec 8)) (trd (_ BitVec 8)))
))

(declare-datatype Label (
  (Label (Length (_ BitVec 8)) (Octets OctetList))
))

(declare-datatype LabelList (
  (List2 (fst2 Label) (snd2 Label) (trd2 Label))
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

;;; grammar
(synth-fun dns_message () (_ BitVec 871)
  ; declare non-terminals
  (
    (message (_ BitVec 871)) 
  ) 
  ; grammar rules
  (
    (message (_ BitVec 871)  ((Constant (_ BitVec 871))))
  )
)

;;; Constraints
(constraint (bvugt ((_ extract 809 800) dns_message) #b0000000000))

;;; SyGuS synthesis command
(check-synth)