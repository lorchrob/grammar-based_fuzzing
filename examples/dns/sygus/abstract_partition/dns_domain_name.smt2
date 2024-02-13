;;; logic
(set-logic UFLIA)
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
  (Pointer (Ptr Int))
  (Cons2 (Head Label) (Tail LabelList))
))

(declare-datatype Top (
  (Name (Labels LabelList))
))

;;; grammar
(synth-fun domain_name () Top
  ; declare non-terminals
  (
    (name Top) 
    (labels LabelList) 
    (label Label)
    (octets OctetList) 
    (num Int)
  ) 
  ; grammar rules
  (
    (name Top                  ((Name labels)))
    (labels LabelList          (Nil2 (Pointer num) (Cons2 label labels)))
    (label Label               ((Label num octets)))
    (octets OctetList          (Nil (Cons num octets)))
    (num Int        ((Constant Int)))
  )
)

;;; Helper functions
(define-fun-rec octet_list_length ((list OctetList)) Int
  (match list (
    ((Nil) 0)
    ((Cons head tail) (+ (octet_list_length tail) 1))
  ))
)
(define-fun-rec label_length ((label Label)) Int
  (match label (
    ((Label length octets) (+ 1 length))
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
(define-fun-rec valid_label_lengths ((list LabelList)) Bool
  (match list (
    ((Nil2) true)
    ((Pointer ptr) true)
    ((Cons2 head tail) (and (valid_label_length head) (valid_label_lengths tail)))
  ))
)
(define-fun-rec domain_name_length ((name Top)) Int
  (match name (
    ((Name labels) (+ (labels_list_length labels) 1))
  ))
)

;;; Constraints
; 1. Domain names are a sequence of labels. Each label is an octet length field
;    followed by that number of octets. Domain name is terminated with a length byte of 0
; Encoded directly in the grammar

; 2. Each label is 63 octets or less
(define-fun c1 ((name Top)) Bool
  (match name (
    ((Name labels) (< (labels_list_length labels) 64))
  ))
)
(constraint (c1 domain_name))

; 3. Total length of domain name is less than 256 bytes
(constraint (< (domain_name_length domain_name) 256))

; 4. Length fields correspond to the actual length of the corresponding lists
(define-fun c2 ((name Top)) Bool
  (match name (
    ((Name labels) (valid_label_lengths labels))
  ))
)
(constraint (c2 domain_name))

; 5. Message compression: an entire domain name or list of labels can be replaced with a 2 octet
;    pointer prefixed by two 1s, followed by an offset from beginning of DNS packet
; (TODO)

;;; SyGuS synthesis command
