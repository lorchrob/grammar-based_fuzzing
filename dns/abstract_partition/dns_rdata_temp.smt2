;;;; logic
(set-logic UFLIA)
;(set-feature :oracles true)

;;;; data-types
(declare-datatype OctetList (
  (Nil)
  (Cons (Head Int) (Tail OctetList))
))

(declare-datatype Label (
  (Label (Length Int) (Octets OctetList))
))

(declare-datatype LabelList (
  (Nil3)
  (Pointer (Ptr Int))
  (Cons2 (Head Label) (Tail LabelList))
))

(declare-datatype DomainName (
  (Name (Labels LabelList) (Termination Int))
))

(declare-datatype CharacterString (
  (String (Length Int) (Data OctetList))
))

(declare-datatype CharacterStringList (
  (Nil2)
  (Cons (Head CharacterString) (Tail CharacterStringList))
))

(declare-datatype Address (
  (Addr (First Int) (Second Int) (Third Int) (Fourth Int))
))

(declare-datatype RData (
  (CName (Name4 DomainName))
  (HInfo (CPU CharacterString) (OS CharacterString))
  (MInfo (Name1 DomainName) (Name2 DomainName))
  (MX (Pref Int) (Name3 DomainName))
  (Null (Nothing OctetList))
  (SOA (MNAME DomainName) (RNAME DomainName) (Serial Int) (Refresh Int) (Retry Int) (Expire Int) (Minimum Int))
  (TXTDATA (TXT CharacterStringList))
  (ADDRESS (ADDR Address))
  (WKS (ADDRESS2 Address) (Protocol Int) (BITMAP OctetList))
))

(declare-datatype DNSRDATA (
  (Data (TYPE Int) (RDLENGTH Int) (RDATA RData))
))

;;;; grammar
(synth-fun dns_rdata () DNSRDATA
  ; declare non-terminals
  (
    (data DNSRDATA) 
    (rdata RData)
    (str CharacterString)
    (char_str_lst CharacterStringList)
    (address Address)
    (dname DomainName)
    (labels LabelList) 
    (label Label)
    (octets OctetList) 
    (int Int)
  ) 
  ; grammar rules
  (
    (data DNSRDATA                    ((Data int int rdata)))
    (rdata RData                      ((CName dname)
                                       (HInfo str str)
                                       (MInfo dname dname)
                                       (MX int dname)
                                       (Null octets)
                                       (SOA dname dname int int int int int)
                                       (TXTDATA char_str_lst)
                                       (ADDRESS address)
                                       (WKS address int octets)))
    (str CharacterString              ((String int octets)))
    (char_str_lst CharacterStringList (Nil2 (Cons str char_str_lst)))
    (address Address                  ((Addr int int int int)))
    (dname DomainName                 ((Name labels int)))
    (labels LabelList                 (Nil3 (Pointer int) (Cons2 label labels)))
    (label Label                      ((Label int octets)))
    (octets OctetList                 (Nil (Cons int octets)))
    (int Int                          ((Constant Int)))
  )
)

;;; Helper functions
(define-fun-rec label_length ((label Label)) Int
  (match label (
    ((Label length octets) (+ 1 length))
  ))
)

(define-fun-rec labels_list_length ((list LabelList)) Int
  (match list (
    ((Nil3) 0)
    ((Pointer ptr) 2)
    ((Cons2 head tail) (+ (labels_list_length tail) 1))
  ))
)

(define-fun-rec domain_name_length ((name DomainName)) Int
  (match name (
    ((Name labels term) (+ (labels_list_length labels) 1))
  ))
)

(define-fun-rec octet_list_length ((octets OctetList)) Int
  (match octets (
    ((Nil) 0)
    ((Cons head tail) (+ 1 (octet_list_length tail)))
  ))
)

(define-fun-rec character_string_length ((chars CharacterString)) Int
  (match chars (
    ((String len data) (+ (octet_list_length data) 1))
  ))
)

(define-fun-rec character_string_list_length ((strs CharacterStringList)) Int
  (match strs (
    ((Nil2) 0)
    ((Cons head tail) (+ (character_string_length head) (character_string_list_length tail)))
  ))
)
(define-fun address_length () Int 4)

(define-fun-rec rdata_length ((rdata RData)) Int
  (match rdata (
    ((CName domain_name) (domain_name_length domain_name))
    ((HInfo cpu os) (+ (character_string_length cpu) (character_string_length os)))
    ((MInfo name1 name2) (+ (domain_name_length name1) (domain_name_length name2)))
    ((MX pref name) (+ 4 (domain_name_length name)))
    ((Null data) (octet_list_length data))
    ((SOA mname rname serial refresh retry expire minimum) (+ 20 (+ (domain_name_length mname) (domain_name_length rname))))
    ((TXTDATA txt) (character_string_list_length txt))
    ((ADDRESS address) address_length)
    ((WKS address protocol bitmap) (+ address_length (+ 4 (octet_list_length bitmap))))
  ))
)

(define-fun-rec valid_label_length ((label Label)) Bool
  (match label (
    ((Label length octets) (= (octet_list_length octets) length))
  ))
)

(define-fun-rec valid_label_lengths ((list LabelList)) Bool
  (match list (
    ((Nil3) true)
    ((Pointer ptr) true)
    ((Cons2 head tail) (and (valid_label_length head) (valid_label_lengths tail)))
  ))
)

(define-fun valid_domain_name_lengths ((dname DomainName)) Bool
  (match dname (
    ((Name labels termination) (valid_label_lengths labels))
  ))
)

(define-fun valid_charstring_length ((list CharacterString)) Bool
  (match list (
    ((String length data) (= (octet_list_length data) length))
  ))
)

(define-fun-rec valid_charstring_lengths ((list CharacterStringList)) Bool
  (match list (
    ((Nil2) true)
    ((Cons head tail) (and (valid_charstring_length head) (valid_charstring_lengths tail)))
  ))
)

(define-fun valid_rdata_type ((dns_rdata DNSRDATA)) Bool
  (match dns_rdata (
    ((Data type rdlength rdata) 
      (match rdata (
        ((CName domain_name) (= type 5)) ;;!! Probably associated with multiple types
        ((HInfo cpu os) (= type 13))
        ((MInfo name1 name2) (= type 14))
        ((MX pref name) (= type 15))
        ((Null data) (= type 10))
        ((SOA mname rname serial refresh retry expire minimum) (= type 6))
        ((TXTDATA txt) (= type 16))
        ((ADDRESS address) (= type 1))
        ((WKS address protocol bitmap) (= type 11))
      ))
    )
  ))
)

(define-fun valid_rdata_lengths ((dns_rdata DNSRDATA)) Bool
  (match dns_rdata (
    ((Data type rdlength rdata) 
      (and 
        (= rdlength (rdata_length rdata))
        (match rdata (
          ((CName domain_name) (valid_domain_name_lengths domain_name)) ;;!! Probably associated with multiple types
          ((HInfo cpu os) (and (valid_charstring_length cpu) (valid_charstring_length os)))
          ((MInfo name1 name2) (and (valid_domain_name_lengths name1) (valid_domain_name_lengths name2)))
          ((MX pref name) (valid_domain_name_lengths name))
          ((Null data) true)
          ((SOA mname rname serial refresh retry expire minimum) (and (valid_domain_name_lengths mname) (valid_domain_name_lengths rname)))
          ((TXTDATA txt) (valid_charstring_lengths txt))
          ((ADDRESS address) true)
          ((WKS address protocol bitmap) true)
        ))
      )
    )
  ))
)

;;;; Constraints
; 1. Length fields match actual lengths
(constraint (valid_rdata_lengths dns_rdata))

; 2. The type field matches the actual type of the rdata
(constraint (valid_rdata_type dns_rdata))

;;;; SyGuS synthesis command
(check-synth)
(check-synth)
(check-synth)
(check-synth)
(check-synth)
(check-synth)
(check-synth)
(check-synth)
(check-synth)
(check-synth)
