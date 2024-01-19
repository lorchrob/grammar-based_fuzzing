(* Types associated with DNS packets *)
type label = int * int list

type domain_name = label list * int

type dns_question = domain_name * int * int

type dns_header = int * int * int * bool * bool * bool * bool * int * int * int * int * int * int

type address = int * int * int * int

type char_string = int * int list

type rdata = 
  | CName of domain_name
  | HInfo of char_string * char_string
  | MInfo of domain_name * domain_name
  | MX of int * domain_name
  | Null of int list
  | SOA of domain_name * domain_name * int * int * int * int * int
  | TXTDATA of char_string list
  | Address of address
  | WKS of address * int * int list

type resource_record = domain_name * int * int * int * int * rdata

type dns_message = dns_header * dns_question * resource_record * resource_record * resource_record