;;; logic
(set-logic UFBV)
;(set-feature :oracles true)

;;; data-types
(declare-datatype OctetList (
  (Nil)
  (Cons (Head (_ BitVec 8)) (Tail OctetList))
))

(declare-datatype DomainName (
  (Name)
))

(declare-datatype CharacterString (
  (String (Length (_ BitVec 8)) (Data OctetList))
))

(declare-datatype CharacterStringList (
  (Nil2)
  (Cons (Head CharacterString) (Tail CharacterStringList))
))

(declare-datatype Address (
  (Addr (First (_ BitVec 8)) (Second (_ BitVec 8)) (Third (_ BitVec 8)) (Fourth (_ BitVec 8)))
))

(declare-datatype RData (
  (CName (Name4 DomainName))
  (HInfo (CPU CharacterString) (OS CharacterString))
  (MInfo (Name1 DomainName) (Name2 DomainName))
  (MX (Pref (_ BitVec 16)) (Name3 DomainName))
  (Null (Nothing OctetList))
  (SOA (MNAME DomainName) (RNAME DomainName) (Serial (_ BitVec 32)) (Refresh (_ BitVec 32)) (Retry (_ BitVec 32)) (Expire (_ BitVec 32)) (Minimum (_ BitVec 32)))
  (TXTDATA (TXT CharacterStringList))
  (ADDRESS (ADDR Address))
  (WKS (ADDRESS2 Address) (Protocol (_ BitVec 8)) (BITMAP OctetList))
))

(declare-datatype DNSRDATA (
  (Data (TYPE (_ BitVec 16)) (RDLENGTH (_ BitVec 16)) (RDATA RData))
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
    (octet (_ BitVec 8))
    (bv_16 (_ BitVec 16)) 
    (bv_32 (_ BitVec 32)) 
  ) 
  ; grammar rules
  (
    (data DNSRDATA                    ((Data bv_16 bv_16 rdata)))
    (rdata RData                      ((CName dname)
                                       (HInfo str str)
                                       (MInfo dname dname)
                                       (MX bv_16 dname)
                                       (Null octets)
                                       (SOA dname dname bv_32 bv_32 bv_32 bv_32 bv_32)
                                       (TXTDATA char_str_lst)
                                       (ADDRESS address)
                                       (WKS address octet octets)))
    (str CharacterString              ((String octet octets)))
    (char_str_lst CharacterStringList (Nil2 (Cons str char_str_lst)))
    (address Address                  ((Addr octet octet octet octet)))
    (dname DomainName                 (Name))
    (octets OctetList                 (Nil (Cons octet octets)))
    (octet (_ BitVec 8)               ((Constant (_ BitVec 8))))
    (bv_16 (_ BitVec 16)              ((Constant (_ BitVec 16))))
    (bv_32 (_ BitVec 32)              ((Constant (_ BitVec 32))))
  )
)

;;; Helper functions
(define-fun-rec octet_list_length ((list OctetList)) (_ BitVec 16)
  (match list (
    ((Nil) #x0000)
    ((Cons head tail) (bvadd (octet_list_length tail) #x0001))
  ))
)

;;; Constraints
; 1. RDLENGTH specifies length in octets of RDATA field
;(define-fun c1 ((data DNSRDATA)) Bool
;  (match data (
;    ((Data type rdlength rdata) (= (octet_list_length rdata) rdlength))
;  ))
;)
;(constraint (c1 dns_rdata))

; 2. Give more info about type and RDATA format
; STUB

;;; SyGuS synthesis command
(check-synth)