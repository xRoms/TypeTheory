open Hw1;;
open Hw1_reduction;;
	
let print_bool q = match q with
| true -> print_string "true"
| false -> print_string "false";;
(*
(%f.%n.(%s.(s (%x.%a.%b.b) (%a.%b.a)) (%f.%x.x) (f s)) n) (%f.%x.f (f (f x)))

print_string(string_of_lambda(normal_beta_reduction(normal_beta_reduction(lambda_of_string "(%y.%m.y (%f.%n.(%s.(s (%x.%a.%b.b) (%a.%b.a)) (%f.%x.x) (f s)) (m n)) (%f.%x.f (f (f x)))) (%f.(%x.f (x x)) (%x.f (x x))) ((%n.%f.%x.n (%g.%h.h (g f)) (%u.x) (%u.u)))"))));;
*)
type test_for_alpha_eq = {lmd1 : lambda; lmd2 : lambda; ans : bool};;
type test_for_free_subst = {n : lambda; m : lambda; x : string; ans : bool};;
type test_free_vars = {lmd : lambda; list_ans : string list};;
type test_reduction = {lmd_r : lambda; rdt : lambda};;

let tests_fae = 
    [{lmd1 = lambda_of_string "(x)"; lmd2 = lambda_of_string "(y)"; ans = false};
    {lmd1 = lambda_of_string "x y"; lmd2 = lambda_of_string "x y"; ans = true};
    {lmd1 = lambda_of_string "%x.x y"; lmd2 = lambda_of_string "%y.y y"; ans = false};
    {lmd1 = lambda_of_string "%x1.x1"; lmd2 = lambda_of_string "%y1.y1"; ans = true};
    {lmd1 = lambda_of_string "(%x.x)(z)(w)"; lmd2 = lambda_of_string "(%y.y)(z)(w)"; ans = true};
    {lmd1 = lambda_of_string "%x1.%x2.%x3.%x4.x1 x2 x3 x4";
         lmd2 = lambda_of_string "%y1.%y2.%y3.%y4.y1 y2 y3 y4"; ans = true};
    {lmd1 = lambda_of_string "%x1.%x2.%x3.%x4.x4 x2 x3 x1";
         lmd2 = lambda_of_string "%y1.%y2.%y3.%y4.y1 y2 y3 y4"; ans = false};
    {lmd1 = lambda_of_string "%x1.%x2.x1 x2";  lmd2 = lambda_of_string "%y1.%y2.y2 y1"; ans = false}];;

let tests_ofs = 
    [{n = lambda_of_string "x"; m = lambda_of_string "%x.y"; x = "y"; ans = false};
    {n = lambda_of_string "x"; m = lambda_of_string "%x.x"; x = "y"; ans = false}; (*!!!!*)
    {n = lambda_of_string "x"; m = lambda_of_string "(x) (%x.y)"; x = "y"; ans = false};
    {n = lambda_of_string "x y %z.z"; m = lambda_of_string "%x.a"; x = "a"; ans = false};
    {n = lambda_of_string "x y %z.z"; m = lambda_of_string "%y.a"; x = "a"; ans = false};
    {n = lambda_of_string "x y %z.z"; m = lambda_of_string "%z.a"; x = "a"; ans = true};
    {n = lambda_of_string "x y %z.z"; m = lambda_of_string "a (%z.a)"; x = "a"; ans = true};
    {n = lambda_of_string "x y %z.z"; m = lambda_of_string "%x.b"; x = "a"; ans = false}];; (*!!!*)

let tests_fv = 
    [{lmd = lambda_of_string "x"; list_ans = ["x"]};
    {lmd = lambda_of_string "%x.x"; list_ans = []}; 
    {lmd = lambda_of_string "(x) (%x.y)"; list_ans = ["x";"y"]}];;

let tests_nbr = 
    [{lmd_r = lambda_of_string "(%x.x) a"; rdt = lambda_of_string "a"};
    {lmd_r = lambda_of_string "a ((%y.%z.y) (%p.p))"; rdt = lambda_of_string "a %z.%p.p"};
    {lmd_r = lambda_of_string "(%x.x) (%y.y) (%z.z)"; rdt = lambda_of_string "((%y.y) (%z.z))"};
    {lmd_r = lambda_of_string "%z.((%x.x) y)"; rdt = lambda_of_string "%z.y"};
    {lmd_r = lambda_of_string "((%x.%y.x)(%z.y)) k"; rdt = lambda_of_string "((%y.(%z.y)) k)"}];;

let tests_rnf = 
    [{lmd_r = lambda_of_string "(%x.%y.y)((%z.z z)(%z.z z))"; rdt = lambda_of_string "%y.y"};
    {lmd_r = lambda_of_string "a ((%y.%z.y) (%p.p))"; rdt = lambda_of_string "a %z.%p.p"};
    {lmd_r = lambda_of_string "(%x.x) (%y.y) (%z.z)"; rdt = lambda_of_string "(%z.z)"};
    {lmd_r = lambda_of_string "(%x.x x)(%a.%b.b b b)"; rdt = lambda_of_string "%b.b b b"};
    {lmd_r = lambda_of_string "(%x.x x x)((%x.x)(%x.x))"; rdt = lambda_of_string "%x.x"};
    {lmd_r = lambda_of_string "(%x.%y.x)(%x.x)((%x.x x)(%x.x x))"; rdt = lambda_of_string "%x.x"};
    {lmd_r = lambda_of_string "(%n.%f.%x.n (%g.%h.h (g f)) (%u.x) (%u.u)) (%f.%x.f (f (f x)))"; rdt = lambda_of_string "(%f.(%x.(f (f x))))"};
    {lmd_r = lambda_of_string "((%x.%y.x)(%z.y)) k"; rdt = lambda_of_string "%z.y"};
    {lmd_r = lambda_of_string "(%x.%y.x) k"; rdt = lambda_of_string "%y.k"};
    {lmd_r = lambda_of_string "(%f.%n.(%s.(s (%x.%a.%b.b) (%a.%b.a)) (%f.%x.x) (f s)) n) (%f.%x.f (f (f x)))"; 
     rdt = lambda_of_string "(%t13.((((t13 (%t29.(%t30.(%t31.t31)))) (%t27.(%t28.t27))) (%t25.(%t26.t26))) (%t33.(t13 (t13 (t13 t33))))))"};
    {lmd_r = lambda_of_string "(%n.%f.%x.n (%g.%h.h (g f)) (%u.x) (%u.u)) (%f.%x.f (f (f x)))"; 
     rdt = lambda_of_string "%x1.%x2.(x1 (x1 x2))"};
    (*{lmd_r = lambda_of_string "(%s.%k.%i.(((s ((s (k s)) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s ((s (k s)) ((s (k (s (k (s ((s ((s ((s i) (k (k (k i))))) (k ((s (k k)) i)))) (k ((s ((s (k s)) ((s (k k)) i))) (k i))))))))) ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k (s (k ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k k)) i))))) (k ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) (k ((s (k k)) i)))))))) ((s (k k)) ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) (k (k ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) ((s ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i))))) ((s ((s (k s)) ((s (k (s (k s)))) ((s ((s (k s)) ((s (k (s (k s)))) ((s (k (s (k k)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s (k (s i))))) ((s (k (s (k k)))) ((s (k (s i))) ((s (k k)) i)))))))))) (k (k ((s (k k)) i))))))) (k (k (k i))))) (%x.%y.%z.x z (y z)) (%x.%y.x) (%x.x)";
     rdt = lambda_of_string "(%t9.(%t2.(t9 (t9 (t9 (t9 (t9 (t9 t2))))))))"};
    {lmd_r = lambda_of_string "((%l0.((%l1.((%l2.((%l3.((%l4.((%l5.((%l6.((%l7.((%l8.((%l9.((%l10.((%l11.((%l12.((%l13.((l13 (%l14.(%l15.(l14 (l14 l15))))) (%l14.(%l15.(l14 (l14 (l14 l15))))))) (%l13.(%l14.(((l0 (%l15.(%l16.(%l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (%l18.(%l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (%l12.(%l13.(%l14.((l12 l13) (l13 l14))))))) (%l11.(%l12.(%l13.(((l11 (%l14.(%l15.(l15 (l14 l12))))) (%l14.l13)) (%l14.l14))))))) (%l10.((l10 (%l11.l3)) l2)))) (l0 (%l9.(%l10.(%l11.((%l12.((%l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (%l8.((l8 (%l9.l3)) l2)))) (%l7.(%l8.((l8 l4) l7))))) (%l6.(%l7.((l6 l5) l7))))) (%l5.(%l6.(%l7.((l5 l6) (l6 l7))))))) (%l4.(%l5.(%l6.(((l4 (%l7.(%l8.(l8 (l7 l5))))) (%l7.l6)) (%l7.l7))))))) (%l3.(%l4.l4)))) (%l2.(%l3.l2)))) (%l1.(%l2.(%l3.((l1 l2) l3)))))) (%l0.((%l1.(l0 (l1 l1))) (%l1.(l0 (l1 l1))))))";
     rdt = lambda_of_string "%x1.(%x2.(x1 (x1 (x1 (x1 (x1 (x1 (x1 (x1 (x1 x2))))))))))"};
    *)
    ];;
    

let tester_on_alpha_eq t ind =
 if (is_alpha_equivalent (t.lmd1) (t.lmd2) = t.ans)
 then true
 else (print_string ("Test#" ^ (string_of_int ind) ^ ": incorrect!" ^ "\n"); false);;
let tester_on_free_subst t ind = 
 if (free_to_subst (t.n) (t.m) (t.x) = t.ans) 
 then true 
 else (print_string ("Test#" ^ (string_of_int ind) ^ ": incorrect!" ^ "\n"); false);;
let tester_on_free_vars t ind = 
 if (free_vars t.lmd = t.list_ans) 
 then true
 else (print_string ("Test#" ^ (string_of_int ind) ^ ": incorrect!" ^ "\n"); false);;

let tester_on_normal_beta_reduction t ind = 
    let k = normal_beta_reduction t.lmd_r in
    match (is_alpha_equivalent k t.rdt) with
    | true  -> true;
    | false -> (print_string ("Test#" ^ (string_of_int ind) ^ ": incorrect! Found: " ^ string_of_lambda k ^ "\n"); false);;

let tester_on_reduce_to_normal_form t ind = 
    let k = reduce_to_normal_form t.lmd_r in
    match (is_alpha_equivalent k t.rdt) with
    | true  -> true;
    | false -> (print_string ("Test#" ^ (string_of_int ind) ^ ": incorrect! Found: " ^ string_of_lambda k ^ "\n"); false);;


let rec tester pred name l ind cor incor = 
	match l with 
	| [] ->  print_string ("Testing on <" ^ name ^ "> has been done!\nYour stats: " ^ "correct answers: " ^ (string_of_int cor) ^
	                                                          ", incorrect answers: " ^ (string_of_int incor)); print_newline(); print_newline();
    | x::xs -> if ((pred x ind) = true) then
                    (print_string ("Test#" ^ (string_of_int ind) ^ ": correct!\n");
                    tester pred name xs (ind + 1) (cor + 1) incor)
                    else
                    tester pred name xs (ind + 1) cor (incor + 1);;


tester (tester_on_alpha_eq) "is_alpha_equivalent" tests_fae 1 0 0;;
tester (tester_on_free_subst) "free_subst" tests_ofs 1 0 0;;
tester (tester_on_free_vars) "free_vars" tests_fv 1 0 0;;
tester (tester_on_normal_beta_reduction) "normal_beta_reduction" tests_nbr 1 0 0;;
tester (tester_on_reduce_to_normal_form) "reduce_to_normal_form" tests_rnf 1 0 0;;