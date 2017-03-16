open Hw1;;

print_int (int_of_peano (S (S (S (Z)))));;
print_string "\n";;

print_list (rev [1; 2; 3]);;
print_string "\n";;
print_list (merge_sort [1; 5; 7; 3; 4; 6; 11; 10; 0]);;
print_string "\n";;

print_string (string_of_lambda (App (Var "F", Abs ("x", App (Var "T", Var "x")))));;
print_string "\n";;
print_string (string_of_lambda (lambda_of_string ("(F (%x.(T x)))")));;
print_string "\n";;
print_string (string_of_lambda (lambda_of_string "T"));;
print_string "\n";;
print_string (string_of_lambda (lambda_of_string "F x"));;
print_string "\n";;
print_string (string_of_lambda (lambda_of_string "(%x.F x) (T x)"));;
print_string "\n";;