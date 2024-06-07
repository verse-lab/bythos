(* requiring the IP of a node itself to be an argument sounds not very reasonable *)
let me_ip = ref ""
let me_port = ref (-1)

(* (IP, port) *)
type address = (string * int)
let cluster : address list ref = ref []
