open Ast

let parse (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  Parser.prog Lexer.read lexbuf

(* TODO: Pretty printing *)