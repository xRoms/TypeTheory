open Hw1



let rec check_subst subst var = match subst with
| Var v -> if (v = var) then
				false
			else
				true
| App (x, y) -> check_subst x var && check_subst y var
| Abs (s, x) ->	if (s = var) then
					true
				else
					check_subst x var;;

let rec find_var_in_exp expr subst var s = match expr with
| Var v -> if (v = var) then 
				check_subst subst s
			else
				true
| App (x, y) -> find_var_in_exp x subst var s && find_var_in_exp y subst var s
| Abs (v, x) -> if (v = var) then
					true
				else 
					find_var_in_exp x subst var s;;

let rec free_to_subst subst expr var = match expr with 
| Var s -> true
| App (x, y) -> free_to_subst subst x var && free_to_subst subst y var
| Abs (s, x) -> find_var_in_exp x subst var s && free_to_subst subst x var;;

module MySet = Set.Make(String);;

let rec free_vars_set expr = match expr with
| Var s -> 	MySet.singleton s
| App (x, y) -> MySet.union (free_vars_set x) (free_vars_set y)
| Abs (s, x) -> MySet.diff (free_vars_set x) (MySet.singleton s);;

let free_vars expr = MySet.elements (free_vars_set expr);;


let rec substitute expr subst var = match expr with
| Var s -> if (s = var) then
				subst
			else 
				Var s
| App (x, y) -> App (substitute x subst var, substitute y subst var)
| Abs (s, x) -> if (s <> var) then
					Abs (s, substitute x subst var)
				else
					Abs (s, x);;

let rec substitute_set expr subst var set = match expr with
| Var s -> if (s = var) then
				subst
			else 
				if (MySet.mem s set) then
					Var ("substed" ^ s)
				else
					Var s 
| App (x, y) -> App (substitute_set x subst var set, substitute_set y subst var set)
| Abs (s, x) -> if (s <> var) then
					if (MySet.mem s set) then
						Abs (("substed" ^ s), substitute_set x subst var set)
					else
						Abs (s, substitute_set x subst var set)
				else
					Abs (s, x);;

let rec is_alpha_equivalent_cnt expra exprb cnt = match expra with
| Var s -> (match exprb with 
			| Var v -> if (s = v) then
							true
						else begin
							false
						end
			| _ -> false)
| App (x, y) -> (match exprb with 
				| App (a, b) ->	is_alpha_equivalent_cnt x a cnt && is_alpha_equivalent_cnt y b cnt
				| _ -> false)
| Abs (s, x) -> (match exprb with 
				| Abs (v, y) -> is_alpha_equivalent_cnt (substitute x (Var ("unique" ^ string_of_int (cnt + 1))) s) (substitute y (Var ("unique" ^ string_of_int (cnt + 1))) v) (cnt + 1)
				| _ -> false);;

let rec is_alpha_equivalent expra exprb = 
	is_alpha_equivalent_cnt expra exprb 0;;

let rec is_normal_form expra = match expra with
| Var s -> true
| Abs (x, y) -> is_normal_form y
| App (x, y) -> match x with
				| Abs (a, b) -> false
				| _ -> is_normal_form x && is_normal_form y;;

let rec reduct_exists expra = match expra with
| Var s -> false
| App (x, y) -> (match x with
				| Abs (a, b) -> true
				| _ -> reduct_exists x || reduct_exists y)
| Abs (x, y) -> reduct_exists y;;

module MyMap = Map.Make(String);;





let abstract expr = 
	let rec abstr expr cnt map = match expr with
	| Var s -> if (MyMap.mem s map) then
					(Var (MyMap.find s map), cnt)
				else 
					(expr, cnt)
	| App (x, y) -> let left = abstr x cnt map in
					let right = abstr y (snd left) map in
					(App (fst left, fst right), snd right)
	| Abs (s, x) -> let newname = "temp" ^ (string_of_int cnt) in
					let res = abstr x (cnt + 1) (MyMap.add s newname map) in
					(Abs (newname, fst res), snd res) in
	fst(abstr expr 0 MyMap.empty);;

let normal_beta_reduction expr =
	let rec normal_beta_reduction_set expr set =
	match expr with
		| Var s -> Var s
		| App (x, y) -> (match x with
						| Abs (a, b) -> substitute_set b y a set
						| _ -> if (reduct_exists x) then begin
									App (normal_beta_reduction_set x set, y)
								end
								else begin
									App (x, normal_beta_reduction_set y set)
									end)
		| Abs (x, y) -> Abs (x, normal_beta_reduction_set y (MySet.add x set)) in
	normal_beta_reduction_set (abstract expr) MySet.empty;;

let print_keys k e =
	print_string(k ^ " | " ^ e ^ "\n");;

let my_map = ref MyMap.empty;;

let reduce_to_normal_form expr =
	my_map := MyMap.empty;
	let rec reducing expr  =
		if (is_normal_form expr) then begin
			expr
		end
		else begin
			match expr with
			| Var s -> Var s
			| App (x, y) -> (match x with
							| Abs (a, b) -> let expr = abstract expr in											
											let memostring = (string_of_lambda expr) in
											if (MyMap.mem memostring !my_map) then begin					
												reducing (lambda_of_string (MyMap.find memostring !my_map))
											end
											else
												let subresult = substitute b y a  in
												let resultstring = string_of_lambda subresult in
												my_map := MyMap.add memostring resultstring !my_map;
												reducing subresult 
							| _ -> if (reduct_exists x) then
										let left = reducing x in
										reducing (App (left, y))
									else 
										let right = reducing y  in
										reducing (App (x, right)))
									
			| Abs (x, y) -> let right = reducing y in
							Abs (x, right) end in
	reducing (abstract expr);;




