open Grammar;;
open Buffer;;
open Printf;;

let (>>) x f = f x;;

(* let (ic, oc) = (open_in "input.txt", open_out "output.txt");; *)

let rec read_line_by_line b = 
  try
    begin
    let line = input_line stdin in
    add_string b line;
    add_string b "\n";
    read_line_by_line b;
    end
  with
    | End_of_file -> ()
;;

let read_stdin () = begin
  let b = create 169 in
  read_line_by_line b;
  contents b
end;;

fprintf stdout "%s\n" (read_stdin () >>  Lexing.from_string >> Parser.main Lexer.main >> string_of_expression);;

(* close_out oc;; *)
(* close_in ic;; *)

