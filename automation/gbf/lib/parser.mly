%{
open Ast
%}

%token RPAREN
%token LPAREN
%token<string> ID

%token EOF

%start <Ast.ast> prog

%%

prog: d = expr; EOF { d } ;
	
expr:
	LPAREN; name = ID; es = list(expr); RPAREN; { Node (name, es) } ;

