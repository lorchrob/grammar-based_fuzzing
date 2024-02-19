type expr =
| Node of string * expr list
| Leaf of string

type ast = expr

(* Need types for constraints, datatypes, and (possibly) grammar *)