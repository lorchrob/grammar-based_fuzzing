{
  open Parser

  let mk_hashtbl init =
    let tbl = List.length init |> Hashtbl.create in
    init |> List.iter (fun (k, v) -> Hashtbl.add tbl k v) ;
    tbl

  (* let keyword_table = mk_hashtbl [
    "example", EXAMPLE ;
  ] *)
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
  | id as p {
    ID p
  }
  | eof { EOF }
  | _ as c { failwith (Printf.sprintf "unexpected character: %C" c) }