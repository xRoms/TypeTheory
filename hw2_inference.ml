open Hw1;;
open Hw1_reduction;;
open Hw2_unify;;

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

let var_counter = ref 0;;


let new_name() = 
	var_counter := !var_counter + 1;
	("temp" ^ (string_of_int !var_counter));;

module MyMap = Map.Make(String);;
module MySet = Set.Make(String);;

let rec substitute hwtype subst_map = match hwtype with
| HM_Elem x -> if (MyMap.mem x subst_map) then MyMap.find x subst_map else hwtype
| HM_Arrow (x, y) -> HM_Arrow (substitute x subst_map, substitute y subst_map)
| HM_ForAll (s, x) -> HM_ForAll (s, substitute x (MyMap.remove s subst_map));;


let rec substitute_types_map types subst = MyMap.map ((fun a b -> substitute b a) subst) types;;

let rec deleteforalls hwtype = match hwtype with
| HM_ForAll (s, x) -> substitute (deleteforalls x) (MyMap.singleton s (HM_Elem (new_name())))
| _ -> hwtype;;

let rec hm_to_term type1 = match type1 with
| HM_Elem s -> Var s
| HM_Arrow (x, y) -> Fun ("-> ", hm_to_term x :: hm_to_term y :: [])
| HM_ForAll (s, x) -> Fun ("@"^s^" ", hm_to_term x :: []);;

let rec term_to_hm term = match term with
| Var s -> HM_Elem s
| Fun (s, x::y::[]) -> HM_Arrow (term_to_hm x, term_to_hm y)
| _ -> failwith "went wrong";;

let rec simp_type_to_term t = 
	match t with
	| S_Elem(a) -> Hw2_unify.Var(a)
	| S_Arrow(a, b) -> Hw2_unify.Fun("->", [(simp_type_to_term a);(simp_type_to_term b)]);;

let rec term_to_simp_type t =
    match t with
	| Hw2_unify.Var(v) -> S_Elem(v)
	| Hw2_unify.Fun(name, [l;r]) -> S_Arrow(term_to_simp_type l, term_to_simp_type r)
| _ -> failwith "went wrong";;

let list_to_map lis = 
	let rec mapper lis map =
		match lis with 
		| [] -> map
		| (s, x)::tail -> mapper tail (MyMap.add s (term_to_hm x) map) in
	mapper lis MyMap.empty;;

let substitute_substitution subst1 subst2 = 
	let substed2 = MyMap.map ((fun subst value -> substitute value subst) subst1) subst2 in
		MyMap.fold (fun x y map -> if (MyMap.mem x map) then map else MyMap.add x y map) subst1 substed2;; 

let free_types hmtype = 
	let rec algo hmtype set = match hmtype with
	| HM_Elem s -> if (MySet.mem s set) then MySet.empty else MySet.singleton s
	| HM_Arrow (x, y) -> MySet.union (algo x set) (algo y set)
	| HM_ForAll (s, x) -> algo x (MySet.add s set) in 
	algo hmtype MySet.empty;;


let free_vars hmlam = 
	let rec algo hmlam set = match hmlam with
	| HM_Var s -> if (MySet.mem s set) then MySet.empty else MySet.singleton s
	| HM_Abs (s, x) -> algo x (MySet.add s set)
	| HM_App (x, y) -> MySet.union (algo x set) (algo y set)
	| HM_Let (x, e1, e2) -> MySet.union (algo e1 set) (algo e2 (MySet.add x set)) in 
	algo hmlam MySet.empty;; 


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



let rec bind_free_types (lam : lambda) = 
	let rec get_free_vars (lam : lambda) = match lam with
	| Var x -> MySet.singleton x
	| App (x, y) -> MySet.union (get_free_vars x) (get_free_vars y)
	| Abs (s, x) -> MySet.remove s (get_free_vars x) in 
	MySet.fold (fun a map -> MyMap.add a (S_Elem (new_name())) map) (get_free_vars lam) MyMap.empty;;
	
let rec get_system (lam : lambda) type_map = match lam with
	| Var x -> ([], MyMap.find x type_map)
	| App (p, r) -> let pi = new_name() in 
					let (ep, rp) = get_system p type_map in 
					let (er, rr) = get_system r type_map in 
					((rp, S_Arrow(rr, S_Elem pi))::(List.append ep er), S_Elem pi)
	| Abs (x, p) -> let rx = new_name() in 
					let (ep, rp) = get_system p (MyMap.add x (S_Elem rx) type_map) in 
					(ep, S_Arrow (S_Elem rx, rp));;

let rec infer_simp_type (lam : lambda) = 
	let stm, t = get_system lam (bind_free_types lam) in
	match solve_system (List.map (fun (a, b) -> (simp_type_to_term a, simp_type_to_term b)) stm) with
	| Some sltn -> Some (List.map (fun (a, b) -> (a, term_to_simp_type b)) sltn, term_to_simp_type (Hw2_unify.apply_substitution sltn (simp_type_to_term t)))
	| None -> None;;	    

let locking context hmtype = 
	let context_types = MyMap.fold (fun a b set -> MySet.union (free_types b) set) context MySet.empty in 
	let right_types = MySet.diff (free_types hmtype) context_types  in 
	let lamres = MySet.fold (fun a b -> HM_ForAll (a, b)) right_types hmtype in 
	lamres;;


let algorithm_w hmlam = 
	let rec algo hmlam type_map = match hmlam with
	| HM_Var x -> if (MyMap.mem x type_map) then 
					(true, (MyMap.empty, deleteforalls (MyMap.find x type_map)))
				  else begin 
						print_string "Var";
						(false, (MyMap.empty, HM_Elem "Var"))
					end
	| HM_App (x, y) ->
						let (b1, (s1, r1)) = algo x type_map in
						let (b2, (s2, r2)) = algo y (substitute_types_map type_map s1) in
						let b = (new_name()) in
						let new_type = substitute r1 s2 in
						let ans = solve_system ((hm_to_term new_type, hm_to_term(HM_Arrow (r2, HM_Elem b))) :: []) in
						if (ans = None || b1 = false || b2 = false) then begin 
							print_string "App\n";
							if (ans = None) then
								print_string ("Nosolve" ^ (string_of_bool b1) ^ (string_of_bool b2) ^ "\n");
							
							(false, (MyMap.empty, HM_Elem "App"))
						end
						else
							(match ans with 
							| Some vlist -> let vmap = list_to_map vlist in
								let s = substitute_substitution vmap (substitute_substitution s1 s2) in
								(true, (s, substitute (HM_Elem b) s))
							|None -> failwith "impossible")
	| HM_Abs (s, x) ->  let b = (new_name()) in
						let (b1, (s1, r1)) = algo x (MyMap.add s (HM_Elem b) (MyMap.remove s type_map)) in
						if (b1) then
							(true, (s1, HM_Arrow (substitute (HM_Elem b) s1, r1)))
						else begin 
							print_string "Abs";
							(false, (MyMap.empty, HM_Elem "Abs"))
						end

	| HM_Let (x, e1, e2) -> let (b1, (s1, r1)) = algo e1 type_map in
							if (b1 = false) then begin 
								print_string "Let1";
								(false, (MyMap.empty, HM_Elem "Let1"))
							end
							else

								let new_type_map = substitute_types_map type_map s1 in
								let (b2, (s2, r2)) = algo e2 (MyMap.add x (locking new_type_map r1) (MyMap.remove x new_type_map)) in 
								
								if (b2 = false) then begin 
									print_string "Let2";
									(false, (MyMap.empty, HM_Elem "Let2"))
								end
								else
									(true, (substitute_substitution s2 s1, r2)) in
	let (boolean, (s, r))  = algo hmlam (MySet.fold (fun a map -> MyMap.add a (HM_Elem (new_name())) map) (free_vars hmlam) MyMap.empty) in 
	if (boolean) then 
		Some (MyMap.fold (fun a b lis -> (a, b)::lis) s [], r)
	else 
		None;;
	



let test123 t = 
	let ans1 = algorithm_w t in
	match ans1 with 
	| Some (l, s) -> let ans2 = hm_to_term s in
    print_string ((algebraic_term_to_string ans2) ^ "\n")
    | None -> print_string "";;


let tt1 = HM_App(HM_Var("y"), HM_Var("y"));;
let tt2 = HM_Let("w", HM_Abs("f", HM_Abs("x", HM_App(HM_Var("f"), HM_App(HM_Var("f"), HM_Var("x"))))), HM_App(HM_Var("w"), HM_Var("w")));; 
let tt3 = HM_Let("w", HM_Abs("f", HM_Abs("x", HM_App(HM_Var("f"), HM_App(HM_Var("f"), HM_Var("x"))))), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_App(HM_Var("w"), HM_Var("w"))))))))))))));; 

test123 tt3;;