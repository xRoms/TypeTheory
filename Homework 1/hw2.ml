                     
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
