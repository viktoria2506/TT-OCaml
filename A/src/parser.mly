%{
open Grammar;;
%}
%token <string> VAR
%token OPEN CLOSE
%token LAMBDA DOT
%token EOF
%nonassoc LAMBDA DOT
%start main
%type <Grammar.expression> main
%%
main:
        expr EOF          { $1 }
expr:
        application LAMBDA VAR DOT expr { Application($1, Lambda($3, $5)) }
        | LAMBDA VAR DOT expr { Lambda($2, $4) }
        | application { $1 }

application:
		application atom { Application($1, $2) }
		| atom { $1 }

atom:
		OPEN expr CLOSE { $2 }
		| VAR { Variable($1) }
        
