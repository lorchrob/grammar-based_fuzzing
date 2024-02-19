;;; logic
(set-logic LIA)
;(set-feature :oracles true)

;;; datatypes
(declare-datatype LabelListStub (
  (LabelListStub)
))

(declare-datatype DomainName (
  (Name (Labels LabelListStub) (Termination Int))
))

(declare-datatype DNSQuestion (
  (Question (QNAME DomainName) (QTYPE Int) (QCLASS Int))
))

(declare-datatype RDataStub (
  (RDataStub)
))

(declare-datatype ResourceRecord (
  (Record (NAME DomainName) (TYPE Int) (CLASS Int) (TTL Int) 
          (RDLENGTH Int) (RDATA RDataStub))
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
  ;;!! Should be lists
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
    (num Int)
    (bool Bool)
  ) 
  ; grammar rules
  (
    (message DNSMessage        ((Message header question record record record)))
    (header  DNSHeader         ((Header num num num bool bool bool bool 0 num num num num num)))
    (question DNSQuestion      ((Question name num num)))
    (record ResourceRecord     ((Record name num num num num RDataStub)))
    (name DomainName           ((Name LabelListStub 0)))
    (num Int                   ((Constant Int)))
    (bool Bool                 ((Constant Bool)))
  )
)


;(define-fun ttl_constraint ((rec ResourceRecord)) Bool 
;  (match rec (
;    ((Record name type class ttl rdlength rdata) (>= ttl 0))
;  ))
;)
;(define-fun c1 ((message DNSMessage)) Bool
;  (match message (
;    ((Message header question answer auth add) (and (ttl_constraint answer) (ttl_constraint auth) (ttl_constraint add)))
;  ))
;)
;(constraint (c1 dns_message))

(check-synth)
(check-synth-next)