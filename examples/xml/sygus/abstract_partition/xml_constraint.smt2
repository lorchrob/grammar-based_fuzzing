;;; logic
(set-logic ALL)

;;; data-types
(declare-datatype Stub (
  ( Stub1 )
  ( Stub2 )
  ( Stub3 )
))

(declare-datatype XmlOpenTag (
  ( Id3 (id1 String) )
  ( IdAttrib2 (id2 String) (attrib Stub) )
))

(declare-datatype XmlCloseTag (
  ( Id2 (id String) )
))

(declare-datatype XmlTree (
  ( OpenClose (full Stub))
  ( Vals (open XmlOpenTag) (inner Stub) (close XmlCloseTag) )
))

;;; grammar
(synth-fun xml () XmlTree
  ; declare non-terminals
  (
    (top XmlTree) (xmlclosetag XmlCloseTag) 
    (xmlopentag XmlOpenTag)
    (str String)
  ) 
  ; grammar rules
  (
    (top XmlTree                     ((Vals xmlopentag Stub1 xmlclosetag)
                                      (OpenClose Stub2)))
    (xmlclosetag XmlCloseTag         ((Id2 str))) 

    (xmlopentag XmlOpenTag           ((Id3 str)
                                      (IdAttrib2 str Stub3)))
    (str String                      ((Constant String)))
  )
)

;;; constraints
; Paired XML open/close tags should match
; <xml-tree>.<xml-open-tag>.<id> = <xml-tree>.<xml-close-tag>.<id>
(define-fun branch-constraint ((open XmlOpenTag) (close XmlCloseTag)) Bool
  (match open (

    ((Id3 tag1) (match close (
      ((Id2 tag2) (= tag1 tag2))
    )))

    ((IdAttrib2 tag1 attrib) (match close (
      ((Id2 tag2) (= tag1 tag2))
    )))
    
  ))
)

(define-fun-rec xml-tree-constraint ((top XmlTree)) Bool
  (match top (
    ((OpenClose stub) true)
    ((Vals open stub close) (branch-constraint open close))
  ))
)

(constraint (xml-tree-constraint xml))

;;; Exclude some examples
(constraint (not (= xml (OpenClose Stub2) )))
(constraint (not (= xml (Vals (Id3 "") Stub1 (Id2 "")) )))
(constraint (not (= xml (Vals (IdAttrib2 "" Stub3) Stub1 (Id2 "")) )))

;;; SyGuS synthesis command
(check-synth)
