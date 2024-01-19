{
open Parser
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

let keyword_table = mk_hashtbl [

  "false", FALSE ;
  "true", TRUE ;
  "define-fun", DEFINEFUN ;
  "dns_message", DNS_MESSAGE ;
  "DNSMessage", DNSMESSAGE ;
  "Message", MESSAGE ;
  "Header", HEADER ;
  "Question", QUESTION ;
  "Name", NAME ;
  "Pointer", POINTER ;
  "Record", RECORD ;
  "Addr", ADDRESS ;

  "CName", CNAME ;
  "HInfo", HINFO ;
  "MInfo", MINFO ;
  "MX", MX ;
  "Null", NULL ;
  "SOA", SOA ;
  "TXTDATA", TXTDATA ;
  "Address", ADDRESS ; 
  "WKS", WKS ;

]


rule read = 
  parse
  | white { read lexbuf }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | int { NUMERAL }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }