;;; logic
(set-logic UFBVLIA)
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
  (Pointer (Ptr (_ BitVec 16)))
  (Cons2 (Head Label) (Tail LabelList))
))

(declare-datatype DomainName (
  (Name (Labels LabelList) (Termination (_ BitVec 8)))
))

;;; grammar
(synth-fun domain_name () DomainName
  ; declare non-terminals
  (
    (name DomainName) 
    (labels LabelList) 
    (label Label)
    (octets OctetList) 
    (octet (_ BitVec 8))
    (bv_16 (_ BitVec 16))
  ) 
  ; grammar rules
  (
    (name DomainName           ((Name labels #b00000000)))
    (labels LabelList          (Nil2 (Pointer bv_16) (Cons2 label labels)))
    (label Label               ((Label octet octets)))
    (octets OctetList          (Nil (Cons octet octets)))
    (octet (_ BitVec 8)        ((Constant (_ BitVec 8))))
    (bv_16 (_ BitVec 16)       ((Constant (_ BitVec 16))))
  )
)

;;; Helper functions
(define-fun-rec octet_list_length ((list OctetList)) (_ BitVec 8)
  (match list (
    ((Nil) #x00)
    ((Cons head tail) (bvadd (octet_list_length tail) #x01))
  ))
)
(define-fun-rec label_length ((label Label)) (_ BitVec 8)
  (match label (
    ((Label length octets) (bvadd #x01 length))
  ))
)
(define-fun-rec valid_label_length ((label Label)) Bool
  (match label (
    ((Label length octets) (= (octet_list_length octets) length))
  ))
)
(define-fun-rec labels_list_length ((list LabelList)) Int
  (match list (
    ((Nil2) 0)
    ((Pointer ptr) 2)
    ((Cons2 head tail) (+ (labels_list_length tail) 1))
  ))
)
(define-fun-rec labels_list_length2 ((list LabelList)) (_ BitVec 8)
  (match list (
    ((Nil2) #x00)
    ((Pointer ptr) #x02)
    ((Cons2 head tail) (bvadd (label_length head) (labels_list_length2 tail)))
  ))
)
(define-fun-rec valid_label_lengths ((list LabelList)) Bool
  (match list (
    ((Nil2) true)
    ((Pointer ptr) true)
    ((Cons2 head tail) (and (valid_label_length head) (valid_label_lengths tail)))
  ))
)
(define-fun-rec domain_name_length ((name DomainName)) (_ BitVec 8)
  (match name (
    ((Name labels termination) (bvadd (labels_list_length2 labels) #x01))
  ))
)

;;; Constraints
; 1. Domain names are a sequence of labels. Each label is an octet length field
;    followed by that number of octets. Domain name is terminated with a length byte of 0
; Encoded directly in the grammar

; 2. Each label is 63 octets or less
(define-fun c1 ((name DomainName)) Bool
  (match name (
    ((Name labels termination) (< (labels_list_length labels) 64))
  ))
)
(constraint (c1 domain_name))

; 3. Total length of domain name is 255 bytes or less
(constraint (bvult (domain_name_length domain_name) #xFF))

; 4. Length fields correspond to the actual length of the corresponding lists
(define-fun c2 ((name DomainName)) Bool
  (match name (
    ((Name labels termination) (valid_label_lengths labels))
  ))
)
(constraint (c2 domain_name))

; 5. Message compression: an entire domain name or list of labels can be replaced with a 2 octet
;    pointer prefixed by two 1s, followed by an offset from beginning of DNS packet
; STUB

;;; SyGuS synthesis command
(check-synth)