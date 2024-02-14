;;!! Takes 8 minutes to generate an example with no constraints.
;;!! And this is with single resource records, not lists of resource records.

;;!!! Only use BVs where necessary (need some BV-specific constraint). Create
;;!!! abstract terms that can map to packets.

;;; logic
(set-logic ALL)
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

;;; Constraints
(declare-const dns_message DNSMessage)

;;; SyGuS synthesis command
(check-sat)
(get-model)


(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 1) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 1 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 1) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 1) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 1) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 1 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 1) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 1 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 1 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 1) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 1 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 1) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 1) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 1 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 1) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 1 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 1) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 1) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 1) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 1) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 1 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 1) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 1 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 1) 0 0) (Record (Name Nil2 0) 0 0 0 0 Nil) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil))))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 1) (Question (Name Nil2 0) 0 0) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)

(assert (not (= dns_message (Message (Header 0 0 0 false false false false 0 0 0 0 0 0) (Question (Name Nil2 0) 0 1) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 (Cons 0 Nil)) (Record (Name Nil2 0) 0 0 0 0 Nil)))))
(check-sat)
(get-model)
