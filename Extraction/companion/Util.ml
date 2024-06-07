let rec list_index a l =
  let rec aux l' =
    match l' with
    | [] -> -1
    | a' :: l'' -> if a = a' then 0 else (aux l'' + 1)
  in aux l
