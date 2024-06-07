(* a large portion of the code is adapted from Toychain and DiSeL *)
(* unless specified, a function defined here is adapted from the function with the same name
    appearing in both Toychain and DiSeL *)

open Unix
open Configuration.Config

(* this only appears in Toychain ... do not know why
    some function calls are wrapped with this, 
    apart from which the function calls are the same as in DiSeL *)
(* Interrupt-resistant versions of system calls  *)
let rec retry_until_no_eintr f =
  try f ()
  with Unix.Unix_error (EINTR, _, _) -> retry_until_no_eintr f

let num_nodes = 32
(* NOTE: use IP port pair to index nodes, instead of using an encoded integer *)
let read_fds : (Unix.file_descr, address) Hashtbl.t = Hashtbl.create num_nodes
let write_fds : (address, Unix.file_descr) Hashtbl.t = Hashtbl.create num_nodes

(*
let get_addr_port name =
  try List.assoc name !cluster
  with Not_found -> failwith (Printf.sprintf "Unknown IP address: %s" name)
*)

let get_name_for_read_fd fd =
  Hashtbl.find read_fds fd

(* TODO FIXME: receive all at once is one of the issues with Verdi *) (* COPIED COMMENT *)
let send_chunk (fd : file_descr) (buf : bytes) : unit =
  let len = Bytes.length buf in
  (* Printf.printf "sending chunk of length %d" len; print_newline (); *) (* COPIED COMMENT *)
  (* let n = Unix.send fd (Util.raw_bytes_of_int len) 0 4 [] in *)
  let len_bytes = Bytes.create 4 in
  Bytes.set_int32_be len_bytes 0 (Int32.of_int len);
  let n = retry_until_no_eintr (fun () -> send fd len_bytes 0 4 []) in
  if n < 4 then
    failwith "send_chunk: message header failed to send all at once.";
  let n = retry_until_no_eintr (fun () -> send fd buf 0 len []) in
  if n < len then
    failwith (Printf.sprintf "send_chunk: message of length %d failed to send all at once." len)

let recv_or_close fd buf offs len flags =
  let n = retry_until_no_eintr (fun () -> recv fd buf offs len flags) in
  if n = 0 then
    failwith "recv_or_close: other side closed connection.";
  n

let receive_chunk (fd : file_descr) : bytes =
  (* let buf4 = Bytes.make 4 '\x00' in *)
  let buf4 = Bytes.create 4 in
  let n = recv_or_close fd buf4 0 4 [] in
  if n < 4 then
    failwith "receive_chunk: message header did not arrive all at once.";
  (* let len = int_of_raw_bytes buf4 in *)
  let len = Int32.to_int (Bytes.get_int32_be buf4 0) in
  (* let buf = Bytes.make len '\x00' in *)
  let buf = Bytes.create len in
  let n = recv_or_close fd buf 0 len [] in
  (* Printf.printf "received chunk of length %d" len; print_newline (); *) (* COPIED COMMENT *)
  if n < len then
    failwith
        (Printf.sprintf "receive_chunk: message of length %d did not arrive all at once." len);
  buf

(* TODO temporarily use this. 
    would it be better if we make it a lazy value? or make it allocated dynamically? *)
let listen_fd : file_descr = socket PF_INET SOCK_STREAM 0

let get_write_fd (name : address) =
  try Hashtbl.find write_fds name
  with Not_found ->
    let write_fd = socket PF_INET SOCK_STREAM 0 in
    (* let (ip, port) = get_addr_port cfg name in *)
    let (ip, port) = name in
    let entry = gethostbyname ip in
    let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
    (* let chunk = Bytes.of_string (string_of_int cfg.me) in *)
    (* NOTE: essentially sending the IP port pair, since it is not straightforward
        to obtain the client IP from the `node_addr` returned by `accept()` *)
    let chunk = Marshal.to_bytes (!me_ip, !me_port) [] in
    retry_until_no_eintr (fun () -> connect write_fd node_addr);
    send_chunk write_fd chunk;
    Hashtbl.add write_fds name write_fd;
    write_fd

let setup () =
  Printexc.record_backtrace true;
  (* the_cfg := Some cfg;
  let (_, port) = get_addr_port cfg cfg.me in *)
  let port = !me_port in
  Printf.printf "listening on port %d" port; print_newline ();
  setsockopt listen_fd SO_REUSEADDR true;
  bind listen_fd (ADDR_INET (inet_addr_any, port));
  listen listen_fd 8

let new_conn () =
  print_endline "new connection!";
  (* let (node_fd, node_addr) = retry_until_no_eintr (fun () -> accept listen_fd) in *)
  let (node_fd, _) = retry_until_no_eintr (fun () -> accept listen_fd) in
  let chunk = receive_chunk node_fd in
  (* let node = Bytes.to_string chunk in
  let name = int_of_string node in *)
  let addr : address = Marshal.from_bytes chunk 0 in
  Hashtbl.add read_fds node_fd addr;
  (* ignore (get_write_fd name); *) (* COPIED COMMENT *)
  (* Printf.printf "done processing new connection from node %s" node; *)
  Printf.printf "done processing new connection from node %s, %d" (fst addr) (snd addr);
  print_newline ()

let check_for_new_connections () =
  let fds = [listen_fd] in
  let (ready_fds, _, _) = retry_until_no_eintr (fun () -> select fds [] [] 0.0) in
  List.iter (fun _ -> new_conn ()) ready_fds

let get_all_read_fds () =
  Hashtbl.fold (fun fd _ acc -> fd :: acc) read_fds []

let serialize_packet pkt = Marshal.to_string pkt []
let deserialize_packet s = Marshal.from_string s 0

(* the following functions are adapted based on Toychain's version *)

(* NOTE: there is a design choice: for procMsg, we need to know the sender's identity. 
    it can be either found from the packet or inferred from the fd using the hash table.
    for now, choose the second approach, so that the packet on transmission can be simplified into an address msg pair *)
let recv_pkt fd =
  let chunk = receive_chunk fd in
  let s = Bytes.to_string chunk in
  let pkt = deserialize_packet s in
  let src = get_name_for_read_fd fd in
  (src, pkt)

let rec get_pkt = function
  | [] -> None
  | fd :: fds ->
      try
        (* TODO emm ... how can it raise an exception? *)
        Some (recv_pkt fd)
      with _ ->
      begin
        get_pkt fds
      end

let send_pkt dst pkt =
  let fd = get_write_fd dst in
  let s = serialize_packet pkt in
  let chunk = Bytes.of_string s in
  send_chunk fd chunk

let send_all pkts =
  List.iter (fun pkt -> send_pkt (fst pkt) (snd pkt)) pkts
