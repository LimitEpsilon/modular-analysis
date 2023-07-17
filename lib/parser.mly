%{
open Syntax
%}
%token LAMBDA DOT
%token <string> ID
%token IN
%token EQUAL
%token LET
%token LP RP
%token EOF
%right LP ID LAMBDA LET

%start program
%type <tm> program

%%

program: exp EOF { $1 }

exp :
    | exp atom { App ($1, $2) }
    | atom { $1 }
    ;

atom :
    | ID { EVar ($1) }
    | LP exp RP { $2 }
    | LAMBDA ID DOT exp %prec LP{ Lam ($2, $4) }
    | LET ID EQUAL exp IN exp %prec LP{ App (Lam ($2, $6), $4) }
    ;
%%
