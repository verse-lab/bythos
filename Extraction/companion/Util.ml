(* some simple functions. not related to any protocol or the shim layer *)

let list_index a l =
  let rec aux l' =
    match l' with
    | [] -> -1
    | a' :: l'' -> if a = a' then 0 else (aux l'' + 1)
  in aux l

let list_nth_default l i d =
  match List.nth_opt l i with
  | Some res -> res
  | _ -> d

let rec list_take_drop l k =
  if k <= 0
  then ([], l)
  else begin
    match l with
    | [] -> ([], l)
    | a :: l' -> 
      let (pre, suf) = list_take_drop l' (k-1) in
      (a :: pre, suf)
  end
