type token =
  | VAR of (string)
  | OPEN
  | CLOSE
  | LAMBDA
  | DOT
  | EOF

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Grammar.expression
