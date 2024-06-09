open Printf
open Configuration.Config

let show_help = ref false

let add_to_cluster ip port =
  cluster := !cluster @ [(ip, port)]

let parse_cluster args =
  let rec aux = function
    | ip :: port :: rest -> add_to_cluster ip (int_of_string port); aux rest
    | [] -> ()
    | _ -> raise (Arg.Bad "format error; make sure the format is like IP1 port1 IP2 port2 ...")
  in aux args

(* need a space at the beginning of the doc string to align *)
let speclist = [
  ("-me", 
    Arg.Tuple [Arg.Set_string me_ip; Arg.Set_int me_port], 
    " Specify the IP and port of the node itself");
    (* Arg.Set_int me_port, 
    " Specify the port of the node itself"); *)
  ("-cluster", 
    Arg.Rest_all parse_cluster, 
    " Specify all the peer nodes in the system as IP port pairs");
  ("-mode", 
    Arg.Set_int behavior_mode,
    " Specify the behavior mode of the node (0=non Byzantine)");
  ("-help", 
    Arg.Unit (fun () -> show_help := true), 
    " Show the help message");
  ("--help", 
    Arg.Unit (fun () -> show_help := true), 
    "") (* want to hide this *)
]

let usage_msg = ("Usage: " ^ Sys.argv.(0) ^ " [-mode <mode_id>] -me <IP> <port> -cluster [<IP> <port> ...]")

let print_help () =
  print_string (Arg.usage_string (Arg.align speclist) usage_msg);
  exit 0

let anon_fun arg = raise (Arg.Bad ("Unexpected argument: " ^ arg))

let parse_args () =
  Arg.parse (Arg.align speclist) anon_fun usage_msg;
  if !show_help then print_help () else ();
  if not (List.mem (!me_ip, !me_port) !cluster) then (add_to_cluster !me_ip !me_port) else ()
  (* if not (List.mem ("127.0.0.1", !me_port) !cluster) then (add_to_cluster "127.0.0.1" !me_port) else () *)

let debug_print () =
  printf "Me IP: %s\n" !me_ip;
  printf "Me port: %d\n" !me_port;
  printf "Cluster:\n";
  List.iter (fun addr -> printf "  %s\n" (string_of_address addr)) !cluster
