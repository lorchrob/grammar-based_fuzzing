open Ast

(* TODO: Refactor Uint64.of_int p |> Uint64.to_string_bin into a separate function.
   Add all the integers to a list, then convert + concat all during the fold. 
   *)

(** [parse s] parses [s] into an AST. *)
let parse (s : string) : dns_message =
  let lexbuf = Lexing.from_string s in
  Parser.prog Lexer.read lexbuf

let uint_to_str (width : int) (i : int) : string = 
  match width with
  | 64 -> Uint64.of_int i |> Uint64.to_string_bin
  | 32 -> Uint32.of_int i |> Uint32.to_string_bin
  | 16 -> Uint16.of_int i |> Uint16.to_string_bin
  | _ -> failwith "Bit width not supported yet"

let convert_header (id, qr, op_code, aa, tc, rd, ra, z, rcode, qd_count, an_count, ns_count, ar_count : dns_header) 
  : string = 
  let id =  uint_to_str 64 id in 
  let qr = uint_to_str 64 qr in 
  let op_code = uint_to_str 64 op_code in
  let aa = (if aa then "1" else "0") in 
  let tc = (if tc then "1" else "0") in 
  let rd = (if rd then "1" else "0") in 
  let ra = (if ra then "1" else "0") in 
  let z = uint_to_str 64 z in 
  let rcode = uint_to_str 64 rcode in 
  let qd_count = uint_to_str 64 qd_count in 
  let an_count = uint_to_str 64 an_count in 
  let ns_count = uint_to_str 64 ns_count in 
  let ar_count = uint_to_str 64 ar_count in 
  let lst = [ id; qr; op_code; aa; tc; rd; ra; z; rcode; qd_count; an_count; ns_count; ar_count ] in 
  List.fold_left (^) "" lst 

let convert_label (len, octets : label) : string = 
  let len = uint_to_str 64 len in 
  let octets = List.map (uint_to_str 64) octets in 
  let lst = len :: octets in 
  List.fold_left (^) "" lst 

let convert_address (fst, snd, thd, fth : address) : string = 
  let fst = uint_to_str 64 fst in 
  let snd = uint_to_str 64 snd in 
  let thd = uint_to_str 64 thd in 
  let fth = uint_to_str 64 fth in 
  let lst = [ fst; snd; thd; fth ] in 
  List.fold_left (^) "" lst

let rec convert_labels (labels : label_list) : string = 
  match labels with 
  | Nil -> ""
  | Pointer p -> uint_to_str 64 p  
  | Cons (label, labels) -> convert_label label ^ convert_labels labels

let convert_r_data_payload (r_data_payload : r_data_payload) : string = 
  match r_data_payload with 
  | WKS (address, protocol, bitmap) -> 
    let address = convert_address address in 
    let protocol = uint_to_str 64 protocol in 
    let bitmap = List.map (uint_to_str 64) bitmap in  
    let lst = address :: protocol :: bitmap in 
    List.fold_left (^) "" lst
  | Null octets -> 
    let lst = List.map (uint_to_str 64) octets in 
    List.fold_left (^) "" lst
  | CName _ | HInfo _ | MInfo _ | MX _ | SOA _ | TXTDATA _ | Address _ -> failwith "RDATA payload type not supported yet"

let convert_domain_name ((labels, term) : domain_name) : string = 
  let labels = convert_labels labels in 
  let term = uint_to_str 64 term in 
  let lst = [ term; labels ] in
  List.fold_left (^) "" lst

(* TODO: Generate 'type' field *)
let convert_r_data (rd_length, r_data_payload: r_data) = 
  let rd_length = uint_to_str 64 rd_length in 
  let r_data_payload = convert_r_data_payload r_data_payload in 
  let lst = [ rd_length; r_data_payload ] in 
  List.fold_left (^) "" lst 

let convert_question (domain_name, q_type, q_class : dns_question) : string = 
  let domain_name = convert_domain_name domain_name in 
  let q_type = uint_to_str 64 q_type in 
  let q_class = uint_to_str 64 q_class in 
  let lst = [ domain_name; q_type; q_class ] in 
  List.fold_left (^) "" lst

let convert_record (domain_name, type_, class_, ttl, rd_length, r_data : resource_record) : string = 
  let domain_name = convert_domain_name domain_name in 
  let type_ = uint_to_str 64 type_ in 
  let class_ = uint_to_str 64 class_ in 
  let ttl = uint_to_str 64 ttl in 
  let rd_length = uint_to_str 64 rd_length in 
  let r_data = convert_r_data r_data in
  let lst = [ domain_name; type_; class_; ttl; rd_length; r_data ] in 
  List.fold_left (^) "" lst

let convert_dns_packet (header, question, rec1, rec2, rec3 : dns_message) : string =
  convert_header header ^ convert_question question ^ 
  convert_record rec1 ^ convert_record rec2 ^ convert_record rec3

(* Main function *)
let () = 
  let input = "(define-fun dns_message () DNSMessage (Message (Header 0 0 0 false true true true 0 0 0 0 0 0) (Question (Name (Name (Pointer 13)) 0) 0 0) (Record (Name (Name (Pointer 14)) 0) 0 0 (Message 22) 0 (Data 8 (WKS (Addr 0 0 0 0) 0 Nil))) (Record (Name (Name (Pointer 14)) 0) 0 0 (Message 23) 0 (Data 1 (Null (Cons 3 Nil)))) (Record (Name (Name (Pointer 15)) 0) 0 0 (Message 24) 0 (Data 1 (Null (Cons 4 Nil))))))" in 
  let ast = parse input in 
  let packet = convert_dns_packet ast in 
  print_endline packet;