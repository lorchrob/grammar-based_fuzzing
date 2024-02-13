;;; logic
(set-logic ALL)

;;; data-types
; an assignment is a pair of variable and rhs
(declare-datatype XmlAttribute (
  ( IdText (id String) (desc String) )
  ( AttribAttrib (attrib1 XmlAttribute) (attrib2 XmlAttribute) )
))

(declare-datatype XmlOpenCloseTag (
  ( Id1 (id1 String) )
  ( IdAttrib (id2 String) (attrib XmlAttribute) )
))

(declare-datatypes ((InnerXmlTree 0) (XmlTree 0)) (
  (
    ( Desc (desc String) )
    ( Tree (tree XmlTree) )
    ( Trees (tree1 InnerXmlTree) (tree2 InnerXmlTree))
  ) 
  (
    ( XmlTreeStub )
  )
))

;;; grammar
(synth-fun xml () XmlTree
  ; declare non-terminals
  (
    (xmltree XmlTree) (xmlattribute XmlAttribute) (xmlopenclosetag XmlOpenCloseTag) 
    (innerxmltree InnerXmlTree) (str String)
  ) 
  ; grammar rules
  (
    (xmltree XmlTree                 ( XmlTreeStub ))

    (xmlattribute XmlAttribute       ((IdText str str)
                                      (AttribAttrib xmlattribute xmlattribute)))

    (xmlopenclosetag XmlOpenCloseTag ((Id1 str)
                                      (IdAttrib str xmlattribute)))

    (innerxmltree InnerXmlTree       ((Desc str)
                                      (Tree xmltree)
                                      (Trees innerxmltree innerxmltree)))

    (str String                      ("a" "bb"))
  )
)

;;; constraints
; Paired XML open/close tags should match
; (lhs) <xml-tree>.<xml-open-tag>.<id> = (lhs) <xml-tree>.<xml-close-tag>.<id>

;;; Exclude some examples
;(constraint (not (= xml (Tag (Id1 "a")) )))
;(constraint (not (= xml (Tag (Id1 "bb")) )))
;(constraint (not (= xml (Branch Stub1 (Desc "a") Stub2)) ))

;;; SyGuS synthesis command
(check-synth)
