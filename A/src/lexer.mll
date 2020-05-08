{
open Parser;;
}

let whitespace = [' ' '\t' '\r' '\n' '\ ']
let variable   = ['a' - 'z']['a' - 'z' '0' - '9' '\'']*

rule main = parse
        | whitespace    { main lexbuf }
        | variable as v { VAR(v) }
        | "."           { DOT }
        | "\\"          { LAMBDA }
        | "("           { OPEN }
        | ")"           { CLOSE }
        | eof           { EOF }  
