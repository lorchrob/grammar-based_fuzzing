;;; logic
(set-logic ALL)

;;; data-types
; an assignment is a pair of variable and rhs
(declare-datatype Assignment (
  ( assign (var String) (val String) )
))
; a statement is a non-empty list of assignments
(declare-datatype Statement (
  ( one (first Assignment) )
  ( cons (head Assignment) (tail Statement) )
))
(declare-datatype ValList (
  ( one2 (first String) )
  ( cons2 (head String) (tail ValList) )
))

;;; grammar
(synth-fun prog () Statement
  ; declare non-terminals
  (
    (stmt Statement) (assgn Assignment) (rhs String) (variable String) (value String)
  ) 
  ; grammar rules
  (
    (stmt     Statement  ((one assgn)
                          (cons assgn stmt)))
    (assgn    Assignment ((assign variable rhs)))
    (rhs      String     (variable value))
    (variable String     ("a"))
    (value    String     ("1"))
  )
)

;;; constraints
; All variables must be named "c"
(define-fun-rec all-variables-c ((stmt Statement)) Bool
  (match stmt (
    ((one assgn) (= (var assgn) "c"))
    ((cons head tail) (and (= (var head) "c") (all-variables-c tail)))
  ))
)
;(constraint (all-variables-c prog))

; Def before use
(define-fun-rec before ((stmt Statement) (variable String)) Bool
  (match stmt (
    ((one assgn) (not (= (val assgn) variable)))

    ((cons head tail) (or (and (= (var head) variable) (not (= (val head) variable)))
                          (and (not (= (val head) variable)) (before tail variable))))
  ))
)
(define-fun-rec all-before ((stmt Statement) (stmt_full Statement)) Bool
  (match stmt (
    ((one assgn) (before stmt_full (var assgn)))
    ((cons head tail) (and (before stmt_full (var head)) (all-before tail stmt_full)))
  ))
)


(define-fun-rec all-vals ((stmt Statement)) ValList
  (match stmt (
    ((one assgn) (one2 (var assgn)))
    ((cons head tail) (cons2 (var head) (all-vals tail)))
  ))
)
(define-fun-rec all-before2 ((stmt Statement) (vals ValList)) Bool
  (match vals (
    ((one2 val) (before stmt val))
    ((cons2 head tail) (and (before stmt head) (all-before2 stmt tail)))
  ))
)
;(constraint (before prog "a"))
;(constraint (all-before prog prog))
;(constraint (all-before2 prog (all-vals prog)))

;;; Exclude some examples
(constraint (not (= prog (one (assign "a" "1")) )))
(constraint (not (= prog (cons (assign "a" "1") (one (assign "a" "a"))) )))


;;; SyGuS synthesis command
(check-synth)

