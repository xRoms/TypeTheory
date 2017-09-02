open Hw2_unify;;

(* Write in console to run:                                          *)
(* > ocamlc -o <EXECUTOR-NAME> hw2_unify.mli hw2_unify.ml t_unify.ml *)
(* > ./<EXECUTOR-NAME>                                               *)

type substitution = (string * algebraic_term) list
type equation = algebraic_term * algebraic_term
type system_of_equations = equation list 

let eqt00 = Fun("->", [Fun("->", [Var "var4"; Var "var4"]); Fun("->", [Var "var4"; Var "var4"])]), Fun("->", [Fun("->", [Fun("->", [Var "var5"; Var "var5"]); Fun("->", [Var "var5"; Var "var5"])]); Var "var6"])



let eqt11 = Fun("x", [Var "p1"]), Fun("x", [Var "p2"]) 
let eqt12 = Fun("y", [Var "p2"]), Fun("y", [Var "p4"])
let eqt13 = Fun("z", [Var "p5"]), Fun("z", [Var "p6"])

let eqt21 = Fun("x", [Var "p1"]), Fun("x", [Var "p2"]) 
let eqt22 = Fun("m", [Var "p1"]), Fun("y", [Var "p4"])
let eqt23 = Fun("z", [Var "p5"]), Fun("z", [Var "p6"])

let eqt31 = Fun("x", [Var "p1"]), Fun("x", [Var "p2"]) 
let eqt32 = Fun("y", [Var "p1"]), Fun("y", [Var "p4"])
let eqt33 = Fun("z", [Var "p1"]), Fun("z", [Var "p6"])

let eqt41 = Fun("a", [Var "tx"; Fun("a", [Var "ty"; Fun("a", [Var "tz";Var "t2"])])]), Fun("a", [Fun("a", [Var "ta"; Fun("a", [Var "tb"; Var "ta"])]); Var "t1"])  
let eqt42 = Var("ty"), Fun("a", [Var "tz"; Var "t4"])
let eqt43 = Var("tx"), Fun("a", [Var "tz"; Var "t3"])
let eqt44 = Var("t3"), Fun("a", [Var "t4"; Var "t2"]) 

let sym0 = [eqt00];;

let sym1 = [eqt11; eqt12; eqt13];;
let sym2 = [eqt21; eqt22; eqt23];;
let sym3 = [eqt31; eqt32; eqt33];;
let sym4 = [eqt41; eqt42; eqt43; eqt44];;

let subt = [("p1", Var("p3"));("p3", Var("p4"));("p5", Var("p6"))] 

let rec algebraic_term_to_string (at : algebraic_term) = 
    let rec impl a =
        match a with 
        | Var x -> x
        | Fun(f, l) -> f ^ "(" ^ impl_for_list l ^ ")" 
    
    and impl_for_list lt = 
        match lt with 
        | [] -> ""
        | (h::[]) -> impl h
        | (h::t) -> (impl h) ^ " " ^ (impl_for_list t)
    in
    impl at;;

let eqt_to_string (eqt : equation) = 
	match eqt with 
	| (l, r) -> algebraic_term_to_string l ^ " = " ^ algebraic_term_to_string r;; 

let rec print_substitution sub =
    match sub with 
    | [] -> print_string "\n"
    | (h::t) -> print_string ((fst h) ^ " = " ^ (algebraic_term_to_string (snd h)) ^ "\n"); print_substitution t;;   

let print_ans ans = 
    match ans with
    | Some s -> print_substitution s
    | None -> print_string "No substitution!\n";;

let check_ans ans subst = 
    match ans with
    | Some s -> print_string (string_of_bool (check_solution s subst));
                print_string "\n"
    | None -> print_string "\n";;

let maj_eqt = system_to_equation(sym1);;

let eql = apply_substitution subt (fst maj_eqt);;
let eqr = apply_substitution subt (snd maj_eqt);;

print_string ((algebraic_term_to_string eql) ^ "\n");;
print_string ((algebraic_term_to_string eqr) ^ "\n");;

let check_subt = check_solution subt sym1;;
print_string ((string_of_bool check_subt) ^ "\n");;


let ans_sym0 = solve_system sym0;;
print_ans ans_sym0;
check_ans ans_sym0 sym0;;
(*
let ans_sym1 = solve_system sym1;;
print_ans ans_sym1;
check_ans ans_sym1 sym1;;

let ans_sym2 = solve_system sym2;;
print_ans ans_sym2;
check_ans ans_sym2 sym2;;

let ans_sym3 = solve_system sym3;;
print_ans ans_sym3;
check_ans ans_sym3 sym3;;

let ans_sym4 = solve_system sym4 in
print_ans ans_sym4;
check_ans ans_sym4 sym4;;*)