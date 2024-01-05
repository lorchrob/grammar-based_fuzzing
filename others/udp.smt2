;;; Notes
; 1. Checksum is computed with big "one's complement sum" over different values, including from
;    the IPvX header. This is a sum where extra carry bits are added to the value of the sum.
;    Then, at the end, you take the one's complement.
; 2. Payload is variable length
; 3. 

;;; logic
(set-logic ALL)
(set-feature :oracles true)

;;; data-types
(declare-datatype IPv6Header (
  (Iphead (Ipsrc (_ BitVec 96)) (Ipdest (_ BitVec 96)))
))
(declare-datatype UDPHeader (
  (Udphead (Src (_ BitVec 16)) (Dest (_ BitVec 16)) (Len (_ BitVec 16)) (Checksum (_ BitVec 16)))
))
(declare-datatype Payload (
  (Data (Payload (_ BitVec 1000)) (Width Int)) ; As an alternative, could also use a list of bits
))
(declare-datatype Datagram (
  (Dgram (Iphead IPv6Header) (Udphead2 UDPHeader) (Data2 Payload))
)) 

;;; grammar
(synth-fun datagram () Datagram
  ; declare non-terminals
  (
    (dgram Datagram) (iphead IPv6Header) (udphead UDPHeader) (data Payload)
    (ipsrc (_ BitVec 96)) (ipdest (_ BitVec 96)) (src (_ BitVec 16)) (dest (_ BitVec 16)) 
    (len (_ BitVec 16)) (checksum (_ BitVec 16)) (payload (_ BitVec 1000)) (width Int)
  ) 
  ; grammar rules
  (
    (dgram Datagram          ((Dgram iphead udphead data)))
    (iphead IPv6Header       ((Iphead ipsrc ipdest)))
    (udphead UDPHeader       ((Udphead src dest len checksum)))
    (data Payload            ((Data payload width)))
    (ipsrc (_ BitVec 96)     ((Constant (_ BitVec 96))))
    (ipdest (_ BitVec 96)    ((Constant (_ BitVec 96))))
    (src (_ BitVec 16)       ((Constant (_ BitVec 16))))
    (dest (_ BitVec 16)      ((Constant (_ BitVec 16))))
    (len (_ BitVec 16)       ((Constant (_ BitVec 16))))
    (checksum (_ BitVec 16)  ((Constant (_ BitVec 16))))
    (payload (_ BitVec 1000) ((Constant (_ BitVec 1000))))
    (width Int               ((Constant Int)))
  )
)

;;; Constraints
; Source port between 0 and 1023
(define-fun src-val2 ((head UDPHeader)) Bool
  (match head (
    ((Udphead src dest len checksum) (bvult src #b0000010000000000))
  ))
)
(define-fun src-val ((packet Datagram)) Bool
  (match packet (
    ((Dgram head1 head2 data) (src-val2 head2))
  ))
)
;(constraint (src-val datagram))

; Dest port between 0 and 1023
(define-fun dest-val2 ((head UDPHeader)) Bool
  (match head (
    ((Udphead src dest len checksum) (bvult dest #b0000010000000000))
  ))
)
(define-fun dest-val ((packet Datagram)) Bool
  (match packet (
    ((Dgram head1 head2 data) (dest-val2 head2))
  ))
)
;(constraint (dest-val datagram))

; Length at least 8 bytes
(define-fun len-val2 ((head UDPHeader)) Bool
  (match head (
    ((Udphead src dest len checksum) (bvugt len #b0010000000000000))
  ))
)
(define-fun len-val ((packet Datagram)) Bool
  (match packet (
    ((Dgram head1 head2 data) (len-val2 head2))
  ))
)
(constraint (len-val datagram))

; Length at at most 1000
(define-fun len-val4 ((head UDPHeader)) Bool
  (match head (
    ((Udphead src dest len checksum) (bvult len #b0000001111101000))
  ))
)
(define-fun len-val3 ((packet Datagram)) Bool
  (match packet (
    ((Dgram head1 head2 data) (len-val4 head2))
  ))
)
;(constraint (len-val3 datagram))

; Length is correct
; Special case-- this will apply when converting the SyGuS output to a concrete packet

; Checksum is valid
;;!! Oracle is passed input as expected when input type is "Int", but
;;!! no input is found if we switch to "(_ BitVec 16)"
(declare-oracle-fun oracle-checksum ((_ BitVec 16)) (_ BitVec 16) oracle_binary)
(define-fun valid-checksum2 ((head UDPHeader)) Bool
  (match head (
    ((Udphead src dest len checksum) (= checksum (oracle-checksum #b0000000000000000)))
  ))
)
(define-fun valid-checksum ((packet Datagram)) Bool
  (match packet (
    ((Dgram head1 head2 data) (valid-checksum2 head2))
  ))
)
(constraint (valid-checksum datagram))

;;; SyGuS synthesis command
(check-synth)

