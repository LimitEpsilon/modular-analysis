%{
open Syntax
%}
%token LAMBDA DOT
%token <string> ID
%token IN
%token EQUAL
%token LET FIX
%token LP RP
%token EOF
%right LP ID LAMBDA LET FIX

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
    | FIX ID ID EQUAL exp IN exp %prec LP{ LetRec ($2, $3, $5, $7) }
    ;
%%
