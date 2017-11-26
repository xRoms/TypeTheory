type algebraic_term = Var of string | Fun of string * (algebraic_term list)

let var_counter = ref 0;;

let new_name() = 
	var_counter := !var_counter + 1;
	("temp" ^ (string_of_int !var_counter));;


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


let rec are_equal term1 term2 = match term1 with
| Var x -> (match term2 with Var y -> if (x = y) then true else false
							| _ -> false)
| Fun (s, x) -> (match term2 with Fun (v, y) -> if (s = v) then
													List.fold_left (fun boolean cmppair -> boolean && (are_equal (fst cmppair) (snd cmppair))) true (List.combine x y)
												else
													false
									| _ -> false)

let system_to_equation x = 
	let name = new_name() in
	let systemparts = List.split x in
		(Fun (name, fst systemparts), Fun (name, snd systemparts));;

let get_subst var subst =
	let iterate var substeqt  =
		if (var = Var (fst substeqt)) then
			snd substeqt
		else 
			var in
	List.fold_left iterate var subst;;


let rec apply_substitution subst eqt = match eqt with
| Var x -> (get_subst (Var x) subst)
| Fun (s, x) -> Fun (s, List.map (apply_substitution subst) x);;

let rec apply_substitution2 subst eqt = (apply_substitution subst (fst eqt), apply_substitution subst (snd eqt));;

let check_solution subst sol = 
	let eqt = system_to_equation sol in
		are_equal (apply_substitution subst (fst eqt)) (apply_substitution subst (snd eqt));;

let check_subst eqt subst = List.fold_left ((fun var boolean subst -> (((fst subst = fst var) && (snd subst <> snd var)) || boolean)) eqt) false subst;;

let rec check_rule var eqt = match eqt with 
| Var x -> (x = var) 
| Fun (s, x) -> List.fold_left ((fun var boolean elem -> (boolean || check_rule var elem)) var) false x;;


let rec reformat sys subst = match sys with
	| [] -> subst
	| (a, b)::tail -> reformat tail ((a, (apply_substitution subst b))::subst);;


let solve_system stm = 
	let rec solving stm subst = 
	match stm with 
		| [] -> (true, subst)
		| (l, r)::tail -> (match (l, r) with
							| (Var x, smth) -> 	if (smth = Var x) then
													solving tail subst
												else
													if (check_rule x smth) then 
														(false, subst)
													else
														if (check_subst (x, smth) subst) then 
															(false, subst)
														else 
															let nsubst = (x, smth)::subst in
																let tail = List.map (apply_substitution2 nsubst) tail in
																	solving tail nsubst
							| (smth, Var x) -> solving ((r, l)::tail) subst
							| (Fun (s, x), Fun(v, y)) -> if (s = v || (List.length x <> List.length y)) then
															solving (List.append (List.combine x y) tail) subst
														else  
															(false, subst)) in
		let ans = solving stm [] in
		if (fst ans) then
			let ans = (snd ans) in
				Some (reformat ans []);
		else
			None;;
