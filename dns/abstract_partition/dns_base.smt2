;;!! Takes 8 minutes to generate an example with no constraints.
;;!! And this is with single resource records, not lists of resource records.

;;!!! Only use BVs where necessary (need some BV-specific constraint). Create
;;!!! abstract terms that can map to packets.

;;; logic
(set-logic LIA)
;(set-feature :oracles true)

;;; data-types

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

(declare-datatype TtlStub (
  (TtlStub)
))

(declare-datatype ResourceRecord (
  (Record (NAME DomainName) (TYPE Int) (CLASS Int) (TTL TtlStub) (RDLENGTH Int) (RDATA RDataStub))
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
    (record ResourceRecord     ((Record name num num TtlStub num RDataStub)))
    (name DomainName           ((Name LabelListStub 0)))
    (num Int                   ((Constant Int)))
    (bool Bool                 ((Constant Bool)))
  )
)

;;; Constraints
; 1. Each label is less than 64 octets
; (rhs)<length> < 63 

; 2. Total length of domain name is less than 256 bytes
; len((rhs)<label-list>) < 256

; 3. Length fields correspond to the actual length of the corresponding lists
; e.g., (lhs)<label>.<length> = len((lhs)<label>.<octets>)

; 4. Message compression: an entire domain name or list of labels can be replaced with a 2 octet
;    pointer prefixed by two 1s, followed by an offset from beginning of DNS packet
; (TODO)

; 5. TTL is >= 0 (signed)
; (rhs)<ttl> >= 0

; 6. Z field is zero'd out
; Encoded directly in the grammar

; Produce diverse inputs
;(constraint (not (= dns_message (let ((_let_1 (Name LabelListStub 0))) (let ((_let_2 (Record _let_1 0 0 TtlStub 0 RDataStub))) (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question _let_1 0 0) _let_2 _let_2 _let_2))))))
