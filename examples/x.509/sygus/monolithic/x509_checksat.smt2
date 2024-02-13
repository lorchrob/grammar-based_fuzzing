(set-logic ALL)

;;; Datatypes

(declare-datatype Version (
  (V1)
  (V2)
  (V3)
))

(declare-datatype Time (
  (UTCTime (month Int) (day Int) (year Int) (hour Int) (minute Int) (second Int))
  (GeneralTime (month2 Int) (day2 Int) (year2 Int) (hour2 Int) (minute2 Int) (second2 Int))
))

(declare-datatype Validity (
  (Validity (notBefore Time) (notAfter Time))
))

(declare-datatype X509Cert (
  (Cert (Version Version) (SerialNumber Int) (Validity Validity))
))

;;; Constraints

(declare-const x509_cert X509Cert)

; Time fields are valid (e.g. month is from 1 to 12)
(define-fun valid_time ((time Time)) Bool
  (match time (
    ((UTCTime m d y h m s)     (and (>= m 1) (<= m 12) (>= d 1) (<= d 31) (>= h 0) (<= h 23) (>= s 0) (<= s 59)))
    ((GeneralTime m d y h m s) (and (>= m 1) (<= m 12) (>= d 1) (<= d 31) (>= h 0) (<= h 23) (>= s 0) (<= s 59)))
  ))
)

(define-fun valid_validity ((validity Validity)) Bool
  (match validity (
    ((Validity not_before not_after) (and (valid_time not_before) (valid_time not_after)))
  ))
)

(define-fun c2 ((x509_cert X509Cert)) Bool
  (match x509_cert (
    ((Cert version serial_number validity) (valid_validity validity))
  ))
)
(assert (c2 x509_cert))

; Serial number is >= 0
(define-fun c1 ((x509_cert X509Cert)) Bool
  (match x509_cert (
    ((Cert version serial_number validity) (>= serial_number 0))
  ))
)
(assert (c1 x509_cert))

; Validity period includes the current time
(define-fun before_curr ((time Time)) Bool
  (match time (
    ((UTCTime m d y h m s)     (<= y 2024))
    ((GeneralTime m d y h m s) (<= y 2024))
  ))
)

(define-fun after_curr ((time Time)) Bool
  (match time (
    ((UTCTime m d y h m s)     (>= y 2024))
    ((GeneralTime m d y h m s) (>= y 2024))
  ))
)

(define-fun validity_curr_time ((validity Validity)) Bool
  (match validity (
    ((Validity not_before not_after) (and (before_curr not_before) (after_curr not_after)))
  ))
)

(define-fun c3 ((x509_cert X509Cert)) Bool
  (match x509_cert (
    ((Cert version serial_number validity) (validity_curr_time validity))
  ))
)
(assert (c3 x509_cert))

;;; SyGuS call
(check-sat)
(get-model)