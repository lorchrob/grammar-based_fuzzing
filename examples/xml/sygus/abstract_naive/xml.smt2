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

(declare-datatype XmlCloseTag (
  ( Id2 (id String) )
))

(declare-datatype XmlOpenTag (
  ( Id3 (id1 String) )
  ( IdAttrib2 (id2 String) (attrib XmlAttribute) )
))

(declare-datatypes ((InnerXmlTree 0) (XmlTree 0)) (
  (
    ( Desc (desc String) )
    ( Tree (tree XmlTree) )
    ( Trees (tree1 InnerXmlTree) (tree2 InnerXmlTree))
  ) 
  (
    ( Tag (tag XmlOpenCloseTag) )
    ( Branch (open XmlOpenTag) (middle InnerXmlTree) (close XmlCloseTag) )
  )
))

;;; grammar
(synth-fun xml () XmlTree
  ; declare non-terminals
  (
    (xmltree XmlTree) (xmlattribute XmlAttribute) (xmlopenclosetag XmlOpenCloseTag) (xmlclosetag XmlCloseTag) 
    (xmlopentag XmlOpenTag) (innerxmltree InnerXmlTree) (str String)
  ) 
  ; grammar rules
  (
    (xmltree XmlTree                 (
                                      (Branch xmlopentag innerxmltree xmlclosetag)))

    (xmlattribute XmlAttribute       ((IdText str str)
                                      (AttribAttrib xmlattribute xmlattribute)))

    (xmlopenclosetag XmlOpenCloseTag ((Id1 str)
                                      (IdAttrib str xmlattribute)))

    (xmlclosetag XmlCloseTag         ((Id2 str))) 

    (xmlopentag XmlOpenTag           ((Id3 str)
                                      (IdAttrib2 str xmlattribute)))

    (innerxmltree InnerXmlTree       ((Desc str)
                                      (Tree xmltree)
                                      (Trees innerxmltree innerxmltree)))

    (str String                      ((Constant String)))
  )
)

;;; constraints
; Paired XML open/close tags should match
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

(define-fun-rec xml-tree-constraint ((xml XmlTree)) Bool
  (match xml (
    ((Tag open_close_tag) true)
    ((Branch open middle close) (branch-constraint open close))
  ))
)

(define-fun-rec matching-tags ((xml XmlTree)) Bool
  (xml-tree-constraint xml)
)
(constraint (matching-tags xml))

;;; Exclude some examples

;;; SyGuS synthesis command
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
(check-synth)

