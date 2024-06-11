(* requiring the IP of a node itself to be an argument sounds not very reasonable *)
let me_ip = ref ""
let me_port = ref (-1)
let behavior_mode = ref 0
let use_PKI = ref false

(* (IP, port) *)
type address = (string * int)
let string_of_address ((ip, port) : address) = ip ^ "@" ^ string_of_int port

let cluster : address list ref = ref []
