type expression = 
	Variable of string 
	| Application of expression * expression 
	| Lambda of string * expression

let rec string_of_expression = function
	| Variable (x) -> x
	| Application (x, y) -> String.concat "" ["("; (string_of_expression x);  " "; (string_of_expression y); ")"]
	| Lambda (x, y) -> String.concat "" ["(\\"; (string_of_expression (Variable x)); "."; (string_of_expression y); ")"]
