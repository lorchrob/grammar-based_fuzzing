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

;;; grammar
(synth-fun dns_rdata () DNSRDATA
  ; declare non-terminals
  (
    (data DNSRDATA) 
    (rdata RData)
    (str CharacterString)
    (char_str_lst CharacterStringList)
    (address Address)
    (dname DomainName)
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
    (dname DomainName                 (Name))
    (octets OctetList                 (Nil (Cons int octets)))
    (int Int               ((Constant Int)))
  )
)

;;; Helper functions
(define-fun-rec octet_list_length ((list OctetList)) Int
  (match list (
    ((Nil) 0)
    ((Cons head tail) (+ (octet_list_length tail) 1))
  ))
)

;;; Constraints
; 1. RDLENGTH specifies length in octets of RDATA field
(define-fun c1 ((data DNSRDATA)) Bool
  (match data (
    ((Data type rdlength rdata) (= (octet_list_length rdata) rdlength))
  ))
)
(constraint (c1 dns_rdata))

; 2. Give more info about type and RDATA format
; STUB

;;; SyGuS synthesis command
(check-synth)