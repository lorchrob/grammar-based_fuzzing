{
  open Parser

  let mk_hashtbl init =
    let tbl = List.length init |> Hashtbl.create in
    init |> List.iter (fun (k, v) -> Hashtbl.add tbl k v) ;
    tbl

  let keyword_table = mk_hashtbl [

    "false", FALSE ;
    "true", TRUE ;
    "define", DEFINE ;
    "fun", FUN ;
    "dns", DNS ;
    "message", MESSAGE ;
    "DNSMessage", DNSMESSAGE ;
    "Message", MESSAGE2 ;
    "Header", HEADER ;
    "Question", QUESTION ;
    "Name", NAME ;
    "Pointer", POINTER ;
    "Record", RECORD ;
    "Data", DATA ;
    "Cons", CONS ;
    "Cons2", CONS2 ;
    "Nil", NIL ;

    (* "CName", CNAME ;
    "HInfo", HINFO ;
    "MInfo", MINFO ;
    "MX", MX ; *)
    "Null", NULL ;
    (* "SOA", SOA ; *)
    "Addr", ADDR ;
    (* "TXTDATA", TXTDATA ; *)
    "WKS", WKS ;

  ]
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read = 
  parse
  | white { read lexbuf }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "-" { HYPHEN }
  | "_" { UNDERSCORE }
  | int as p { INT (int_of_string p) }
  | id as p {
    try Hashtbl.find keyword_table p with Not_found -> (print_endline p; assert false)
  }
  | eof { EOF }
  | _ as c { failwith (Printf.sprintf "unexpected character: %C" c) }