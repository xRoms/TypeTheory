type peano = Z | S of peano
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda

let rec peano_of_int x = match x with
	0 -> Z
|   x -> S (peano_of_int (x - 1)) ;;

let rec int_of_peano p = match p with
    Z -> 0
| 	S x -> 1 + int_of_peano x;;

let inc x = 
	S x;;

let rec add x y = match (x, y) with
  (x, Z) -> x
| (x, S y) ->  S (add x y);;

let rec sub x y = match (x, y) with
  (Z, x) -> Z
| (x, Z) -> x
| (S x, S y) ->  sub x y;;

let rec mul x y = match (x, y) with
  (x, Z) -> Z
| (x, S y) -> add (mul x y) x

let rec power x y = match (x, y) with
  (x, Z) -> S Z;
| (x, S y) -> mul x (power x y) ;;


                     
let rec reverse reversed straight = match straight with
| [] -> reversed
| elem::left -> reverse (elem::reversed) left;;

let rev x = reverse [] x;;

let rec print_list x = match x with
| [] -> ()
| e::x -> print_int e ; print_string " " ; print_list x;; 

let rec merge (x, y) = match (x, y) with
| (a, []) -> a
| ([], a) -> a
| (e1::a, e2::b) -> 
	if (e1>e2) then
		e2::merge (x, b)
	else 
		e1::merge (a, y);; 

let drop2 x y = match x with
| [] -> (x, y)
| e1::a -> (a, e1::y);;

let rec split x y  = match ((List.length x) - (List.length y)) with
| 0 -> (x, rev y)
| 1 -> (x, rev y)
| _ -> let (a, b) = drop2 x y in 
	split a b;;

let rec merge_sort x = match x with
| [] -> []
| [a] -> [a]
| a -> let (first, second) = split a [] in
	merge (merge_sort first, merge_sort second);;

	
                     
let rec string_of_lambda l = match l with
|	Var x -> x
|   Abs (x, y) -> "(%" ^ x ^ "." ^ string_of_lambda y ^ ")"
|   App (x, y) -> "(" ^ string_of_lambda x ^ " " ^ string_of_lambda y ^ ")";;

let rec string_of_lambda_cool l = match l with
|	Var x -> ("Var " ^ x ^ " ")
|   Abs (x, y) -> "Abs (" ^ x ^ ", " ^ string_of_lambda_cool y ^ ")"
|   App (x, y) -> "App (" ^ string_of_lambda_cool x ^ ", " ^ string_of_lambda_cool y ^ ")";;

let dot s = 
	let rec dot s ind =
		if (String.get s ind = '.') then
			ind
		else 
			dot s (ind + 1)
	in
	dot s 0;;

let lastopeningbracket s =
	let rec lob s pos bal ans = 
		if (pos >= String.length s) then
			ans
		else
			match String.get s pos with
			| '(' -> if (bal = 0) then
						lob s (pos + 1) (bal + 1) pos
					else 
						lob s (pos + 1) (bal + 1) ans
			| ')' -> lob s (pos + 1) (bal - 1) ans
			| ' ' -> if (bal = 0) then
						lob s (pos + 1) bal pos
					else
						lob s (pos + 1) bal ans 
			| _ -> lob s (pos + 1) bal ans in
	lob s 0 0 (-1);;




let rec lambda_of_string s =
	let s = String.trim s in
	match String.get s 0 with
	| '%' -> Abs ((String.sub s 1 ((dot s) - 1)), lambda_of_string (String.sub s ((dot s) + 1) (String.length s - (dot s) - 1)))
	| '(' -> let lb = lastopeningbracket s in
			 if (lb = 0) then
			 	lambda_of_string(String.sub s 1 (String.length s - 2))
			 else
			 	App (lambda_of_string (String.sub s 0 lb) , lambda_of_string (String.sub s (lb) (String.length s - lb)))
	| x -> let lb = lastopeningbracket s in
			if (lb = -1) then
				Var s
			else
			 	App (lambda_of_string (String.sub s 0 lb) , lambda_of_string (String.sub s (lb) (String.length s - lb)))