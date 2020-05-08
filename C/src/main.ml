open Grammar;;
open Buffer;;
open Printf;;

module Ht = Hashtbl;;


type aterm 
  =  Atomic of int 
  | Impl of aterm * aterm
;;

type equalution = {
  left : aterm; 
  right : aterm
};;


let rec term_has_atomic term atom = match term with
  | Atomic(b) -> atom = term
  | Impl(a, b) -> begin
    let b1 = term_has_atomic a atom in 
    let b2 = term_has_atomic b atom in   
    b1 || b2
  end
;;

let bad_equal e = match e with
  | {left = Atomic(a); right = Impl(b, c)} -> begin
    let r = e.right in
    let l = e.left in
    term_has_atomic r l
  end
  | _ -> false
;;

let reverting e = match e with
  | {left = Impl(a, b); right = Atomic(c)} -> begin
    let r = e.right in 
    let l = e.left in
    {left = r; right = l}
  end
  | _ -> e
;;

let is_not_id e = match e with
    | {left = Atomic(a); right = Atomic(b)} -> a <> b
    | _ -> true
;;

let reduct e = match e with
  | {left = Impl(a, b); right = Impl(c, d)} -> begin
    let l = {left = a; right = c} in
    let r = {left = b; right = d} in  
    [l; r]
  end
  | _ -> [e]
;;

let rec substitution rule term = match term with
  | Atomic(a) -> if (rule.left = term) then rule.right else term
  | Impl(a, b) -> begin
    let s1 = substitution rule a in 
    let s2 =  substitution rule b in 
    Impl(s1, s2)
  end
;;

let rec term_to_string = function
  | Atomic(x) -> String.concat "" ["t"; string_of_int x]
  | Impl(x, y) -> String.concat "" ["("; term_to_string x; " -> "; term_to_string y; ")"]

let rec create_system expr index free_vars dep_vars = match expr with
  | Variable(s) -> begin
                        let new_index = index + 1 in
                        let id =  match (Ht.mem dep_vars s) with
                                    | true -> Ht.find dep_vars s
                                    | false -> match (Ht.mem free_vars s) with
                                      | true -> Ht.find free_vars s
                                      | false -> begin
                                                  Ht.add free_vars s new_index;
                                                  new_index
                                                end
                        in
                        let new_expr = Atomic(id) in
                        ([],  new_expr, new_index)
                      end
  | Application(p, q) -> begin
    let (xp, yp, xind) = create_system p index free_vars dep_vars in
    let (xq, yq, yind) = create_system q xind free_vars dep_vars in
    let new_index = yind + 1 in
    ({left = yp; right = Impl(yq, Atomic(new_index))}::(List.rev_append xp xq), Atomic(new_index), new_index  )
  end
  | Lambda(s, p) -> begin
    let new_index = index + 1 in
    Ht.add dep_vars s new_index;
    let (e, yp, xind) = create_system p new_index free_vars dep_vars in
    let new_expr = Impl(Atomic(new_index), yp) in
    Ht.remove dep_vars s;
    (e, new_expr, xind)
  end
;;

let is_substitution substed_aterms e = match e with
  | {left = Atomic(a); right = b} -> 
    if Ht.mem substed_aterms e.left
    then false
    else true
  | _ -> false
;;

let subst rule e = match rule = e with
  | true -> e
  | _ -> begin
    let l = substitution rule e.left in 
    let r = substitution rule e.right in 
    {left = l; right = r}
  end
;;

let rec solve_system system substed_aterms = if (List.exists bad_equal system) then None else begin
  let prev = system in
  let xsystem = List.filter is_not_id (List.rev_map reverting (List.flatten (List.rev_map reduct system))) in
  match List.exists (is_substitution substed_aterms) xsystem with
    | false -> (
        match List.compare_lengths prev xsystem with
        | 0 when (List.for_all2 (=) prev xsystem) -> Some(xsystem) 
        | _ -> solve_system xsystem substed_aterms
    )
    | true -> begin
      let rule = List.find (is_substitution substed_aterms) xsystem in
      Ht.add substed_aterms (rule.left) true;
      let ysystem = List.rev_map (subst rule) xsystem in
      solve_system ysystem substed_aterms
    end
end;;

let is_left_is_term term e = e.left = term;; 

let rec apply_subst term solution = match term with
  | Atomic(x) -> (
    match List.exists (is_left_is_term term) solution with
      | false -> term
      | true -> let rule = List.find (is_left_is_term term) solution in
        rule.right
  )
  | Impl(a, b) -> begin
    let x = apply_subst a solution in 
    let y = apply_subst b solution in
    Impl(x, y) 
  end
;;


let tab = "*   ";;

let add_pair x y z = (x, y)::z;;
let get_type_by_ind solution index = term_to_string (apply_subst (Atomic(index)) solution);;

let context solution free_vars = begin
  let pairs = Ht.fold add_pair free_vars [] in
  String.concat ", " (List.map (fun (k, v) -> String.concat " " [k; ":"; get_type_by_ind solution v]) pairs)
end;;

let separator c = if ((String.length c) = 0) then "" else ", ";;
let gap c = if ((String.length c) = 0) then "" else " ";;

let get_right_of_impl x = match x with
  | Impl(a, b) -> b
  | _ -> raise (Failure("Error"));
;;

let rec proof_impl expr solution free_vars dep_vars c cur_tab index = match expr with
  | Variable(s) -> begin
                      let new_index = index + 1 in
                      let id = match Ht.mem dep_vars s with
                        | true -> Ht.find dep_vars s
                        | false -> Ht.find free_vars s
                      in
                      let applied = apply_subst (Atomic(id)) solution in
                      (s, applied, [String.concat "" [cur_tab; c; " |- "; s; " : "; (term_to_string applied); " [rule #1]"]], new_index)
                    end
  | Lambda(s, p) -> begin
                            let new_index = index + 1 in
                            Ht.add dep_vars s new_index;
                            let applied = apply_subst (Atomic(new_index)) solution in
                            let applied_string = term_to_string applied in
                            let (xp, yp, tail_proof, xind) = proof_impl p solution free_vars dep_vars (String.concat "" [c; separator c; s; " : "; applied_string]) (cur_tab ^ tab) new_index in
                            Ht.remove dep_vars s;
                            let cur_step = String.concat "" [cur_tab; c; gap c; "|- "; String.concat "" ["(\\"; s; ". "; xp; ")" ]; " : ("; applied_string; " -> "; (term_to_string yp); ") [rule #3]"] in
                            (String.concat "" ["(\\"; s; ". "; xp; ")" ], Impl(applied, yp), cur_step::tail_proof, xind)
                          end
  | Application(p, q) ->  begin
                    let (xp, yp, p_proof, xind) = proof_impl p solution free_vars dep_vars c (cur_tab ^ tab) index in
                    let (xq, _, q_proof, yind) = proof_impl q solution free_vars dep_vars c (cur_tab ^ tab) xind in
                    let new_index = yind + 1 in
                    let cur_t = get_right_of_impl yp in
                    let cur_step = String.concat "" [cur_tab; c; gap c; "|- "; String.concat "" ["("; xp; " "; xq; ")"]; " : "; (term_to_string cur_t); " [rule #2]"] in
                    (String.concat "" ["("; xp; " "; xq; ")"], cur_t, cur_step::(List.rev_append (List.rev p_proof) q_proof), new_index)
                  end

and get_proof expr solution free_vars = begin
  let (_, _, cur_proof, _) = proof_impl expr solution free_vars (Ht.create 300 : (string, int) Ht.t) (context solution free_vars) "" 0 in
  cur_proof
end;;

let (>>) x f = f x;;
let expr = (input_line stdin) >> Lexing.from_string >> Parser.main Lexer.main;;

let free_vars = (Ht.create 300 : (string, int) Ht.t);;
let dep_vars = (Ht.create 300 : (string, int) Ht.t);;
let substed_aterms = (Ht.create 300 : (aterm, bool) Ht.t);;
let (e, _, _) = create_system expr 0 free_vars dep_vars;;

let result = solve_system e substed_aterms in 
match result with
  | Some(solution) -> List.iter (fprintf stdout "%s\n") (get_proof expr solution free_vars);
  | None -> fprintf stdout "Expression has no type\n";

close_in stdin;;
close_out stdout;;
