%{
open Ast
%}

%token RPAREN
%token LPAREN
%token FALSE
%token TRUE
%token DEFINE
%token HYPHEN
%token FUN
%token DNS
%token UNDERSCORE
%token MESSAGE
%token DNSMESSAGE
%token MESSAGE2
%token HEADER
%token QUESTION
%token NAME
%token POINTER
%token RECORD
%token ADDR
%token DATA
%token CONS
%token CONS2
%token NIL
// %token CNAME
// %token HINFO
// %token MINFO
// %token MX
%token NULL
// %token SOA
// %token TXTDATA
%token WKS
%token EOF
%token<int> INT

%start <Ast.dns_message> prog

%%

prog: d = dns_message; EOF { d } ;
	
dns_message:
	LPAREN; DEFINE; HYPHEN; FUN; DNS; UNDERSCORE; MESSAGE; 
	LPAREN; RPAREN; DNSMESSAGE; LPAREN; MESSAGE2; 
	h = dns_header; q = dns_question; 
	r1 = resource_record; r2 = resource_record; r3 = resource_record;
	RPAREN; RPAREN; { (h, q, r1, r2, r3) } ;

dns_header:
	LPAREN; HEADER; 
	i1 = INT; i2 = INT; i3 = INT;
	b1 = bool; b2 = bool; b3 = bool; b4 = bool;
	i4 = INT; i5 = INT; i6 = INT; i7 = INT; i8 = INT; i9 = INT;
	RPAREN;
	{ (i1, i2, i3, b1, b2, b3, b4, i4, i5, i6, i7, i8, i9) }

resource_record:
	LPAREN; RECORD; d = domain_name; i1 = INT; i2 = INT; 
	LPAREN; MESSAGE2; i3 = INT; RPAREN; 
	i4 = INT; r = rdata;
	RPAREN;
	{ (d, i1, i2, i3, i4, r) }

dns_question:
	LPAREN; QUESTION; d = domain_name;
	i1 = INT; i2 = INT;
	RPAREN;
	{ (d, i1, i2) }

domain_name:
	LPAREN; NAME; LPAREN; NAME; l = label_list; RPAREN; i = INT; 
	RPAREN;
	{ (l, i) }

label_list: 
	| NIL;
	{ Nil }
	| LPAREN; POINTER; i = INT; RPAREN;
	{ Pointer i }
	| LPAREN; CONS2; l1 = label; l2 = label_list; RPAREN;
	{ Cons (l1, l2) }

label:
	LPAREN; i = INT; o = octet_list; RPAREN;
	{ (i, o) }

rdata:
	LPAREN; DATA; i = INT; p = rdata_payload;
	RPAREN;
	{ (i, p) }

rdata_payload:
	(* TODO: finish cases *)
	| LPAREN; WKS; a = address; i = INT; o = octet_list; RPAREN
	{ WKS (a, i, o) }
	| LPAREN; NULL; o = octet_list; RPAREN;
	{ Null o }

address:
	LPAREN; ADDR; i1 = INT; i2 = INT; i3 = INT; i4 = INT;
	RPAREN;
	{ (i1, i2, i3, i4) } 

octet_list:
	| NIL;
		{ [] }
	| LPAREN; CONS; i = INT; o = octet_list; RPAREN;
		{ i :: o }

bool:
	| TRUE { true }
	| FALSE { false }
	
