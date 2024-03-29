;;; logic
(set-logic LIA)
;(set-feature :oracles true)

;;; data-types
(declare-datatype OctetList (
  (Nil)
  (Cons (Head Int) (Tail OctetList))
))

(declare-datatype Label (
  (Label (Length Int) (Octets OctetList))
))

(declare-datatype LabelList (
  (Nil2)
  (Cons2 (Head Label) (Tail LabelList))
))

(declare-datatype DomainName (
  (Name (Labels LabelList) (Termination Int))
))

(declare-datatype DNSQuestion (
  (Question (QNAME DomainName) (QTYPE Int) (QCLASS Int))
))

(declare-datatype ResourceRecord (
  (Record (NAME DomainName) (TYPE Int) (CLASS Int) (TTL Int) (RDLENGTH Int) (RDATA OctetList))
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
    (num Int)
    (bool Bool)
  ) 
  ; grammar rules
  (
    (message DNSMessage        ((Message header question record record record)))
    (header  DNSHeader         ((Header num num num bool bool bool bool num num num num num num)))
    (question DNSQuestion      ((Question name num num)))
    (record ResourceRecord     ((Record name num num num num octets)))
    (name DomainName           ((Name labels num)))
    (labels LabelList          (Nil2 (Cons2 label labels)))
    (label Label               ((Label num octets)))
    (octets OctetList          (Nil (Cons num octets)))
    (num Int                   ((Constant Int)))
    (bool Bool                 ((Constant Bool)))
  )
)

;;; Constraints

;;; SyGuS synthesis command
(check-synth)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)
(check-synth-next)