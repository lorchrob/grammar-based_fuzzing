;;; logic
(set-logic LIA)
;(set-feature :oracles true)

;;; data-types
(declare-datatype OctetList (
  (Nil)
  (Cons (Head Int) (Tail OctetList))
))

(declare-datatype DomainName (
  (Name)
))

(declare-datatype DNSQuestion (
  (Question (QNAME DomainName) (QTYPE Int) (QCLASS Int))
))

(declare-datatype RDATA (
  (Rdata)
))

(declare-datatype ResourceRecord (
  (Record (NAME DomainName) (CLASS Int) (TTL Int) (RDATA RDATA))
))

(declare-datatype DNSHeader (
  (Header (ID Int) (QR Int) (Opcode Int) 
    (AA Bool) (TC Bool) (RD Bool) (RA Bool) 
    (Z Int) (RCODE Int) 
    (QDCOUNT Int) (ANCOUNT Int) (NSCOUNT Int) (ARCOUNT Int)
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
(synth-fun dns_packet () DNSMessage
  ; declare non-terminals
  (
    (message DNSMessage) 
    (header DNSHeader) 
    (question DNSQuestion) 
    (record ResourceRecord) 
    (name DomainName) 
    (rdata RDATA)
    (octets OctetList) 
    (int Int)
    (bool Bool) 
  ) 
  ; grammar rules
  (
    (message DNSMessage    ((Message header question record record record)))
    (header  DNSHeader     ((Header int int int bool bool bool bool 0 int int int int int)))
    (question DNSQuestion  ((Question name int int)))
    (record ResourceRecord ((Record name int int rdata)))
    (name DomainName       (Name))
    (rdata RDATA           (Rdata))
    (octets OctetList      (Nil (Cons int octets)))
    (int Int    ((Constant Int)))
    (bool Bool   ((Constant Bool)))
  )
)

;;; Constraints
; 1. TTL is >= 0 (signed)
(define-fun c1 ((record ResourceRecord)) Bool
  (match record (
    ((Record name class ttl rdata) (>= ttl 0))
  ))
)
(define-fun c2 ((message DNSMessage)) Bool
  (match message (
    ((Message header query answer authority additional) (and (c1 answer) (c1 authority) (c1 additional)))
  ))
)
;(constraint (c2 dns_packet))

; 2. Test constraint, NSCount > 4
(define-fun c_test2 ((header DNSHeader)) Bool
  (match header (
    ((Header id qr opcode f1 f2 f3 f4 z rcode qdcount ancount nscount arcount) (> nscount 15))
  ))
)
(define-fun c_test ((message DNSMessage)) Bool
  (match message (
    ((Message header query answer authority additional) (c_test2 header))
  ))
)
(constraint (c_test dns_packet))

; 2. Z field is zero'd out
; Encoded directly in the grammar

;;; SyGuS synthesis command
(check-synth)