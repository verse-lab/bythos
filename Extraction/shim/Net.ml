(* a large portion of the code is adapted from Toychain and DiSeL *)
(* unless specified, a function defined here is adapted from the function with the same name
    appearing in both Toychain and DiSeL *)
(* small note: the "fd" below can be to some extent interpreted as "socket" *)

open Unix
open Configuration.Config

(* this only appears in Toychain ... it can make function calls more robust?
    some function calls are wrapped with this, 
    apart from which the function calls are the same as in DiSeL *)
(* Interrupt-resistant versions of system calls  *)
let rec retry_until_no_eintr f =
  try f ()
  with Unix.Unix_error (EINTR, _, _) -> retry_until_no_eintr f

(** low-level sending and receiving **)

(* TODO FIXME: receive all at once is one of the issues with Verdi *) (* COPIED COMMENT *)
let send_chunk (fd : file_descr) (buf : bytes) : unit =
  let len = Bytes.length buf in
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
  let buf4 = Bytes.create 4 in
  let n = recv_or_close fd buf4 0 4 [] in
  if n < 4 then
    failwith "receive_chunk: message header did not arrive all at once.";
  let len = Int32.to_int (Bytes.get_int32_be buf4 0) in
  let buf = Bytes.create len in
  let n = recv_or_close fd buf 0 len [] in
  if n < len then
    failwith
        (Printf.sprintf "receive_chunk: message of length %d did not arrive all at once." len);
  buf

(** managing connections **)

(* NOTE: use IP port pair to index nodes, instead of using an encoded integer *)
(* fd |--> addr: from fd, the current node can receive packets from another node at addr *)
let read_fds : (Unix.file_descr, address) Hashtbl.t = Hashtbl.create 32
(* addr |--> fd: through fd, the current node can send packets to another node at addr *)
let write_fds : (address, Unix.file_descr) Hashtbl.t = Hashtbl.create 32

let get_all_read_fds () =
  Hashtbl.fold (fun fd _ acc -> fd :: acc) read_fds []

let get_name_for_read_fd fd =
  Hashtbl.find read_fds fd

let build_connection_to ((ip, port) : address) =
  let write_fd = socket PF_INET SOCK_STREAM 0 in
  let entry = gethostbyname ip in
  let node_addr = ADDR_INET (Array.get entry.h_addr_list 0, port) in
  (* NOTE: send the IP port pair here, since it is not straightforward
      to obtain the client IP from the `node_addr` returned by `accept()` *)
  let self_pub_key = (if !use_PKI then (let pub = Crypto.self_pub_key () in Some pub) else None) in
  let chunk = Marshal.to_bytes ((!me_ip, !me_port), self_pub_key) [] in
  retry_until_no_eintr (fun () -> connect write_fd node_addr);
  send_chunk write_fd chunk;
  Hashtbl.add write_fds (ip, port) write_fd;
  write_fd

(* the listening socket of the current node *)
let listen_fd : file_descr = socket PF_INET SOCK_STREAM 0

(* set up the listening socket *)
let setup () =
  Printexc.record_backtrace true;
  let port = !me_port in
  Printf.printf "listening on port %d" port; print_newline ();
  (* get around those "Address already in use" error messages *)
  setsockopt listen_fd SO_REUSEADDR true;
  bind listen_fd (ADDR_INET (inet_addr_any, port));
  listen listen_fd 8

(* process newly coming connection request *)
let new_conn () =
  print_endline "new connection!";
  let (node_fd, _) = retry_until_no_eintr (fun () -> accept listen_fd) in
  let chunk = receive_chunk node_fd in
  let (addr, okey) : (address * Crypto.public_key option) = Marshal.from_bytes chunk 0 in
  Hashtbl.add read_fds node_fd addr;
  Printf.printf "done processing new connection from node %s" (string_of_address addr);
  (match okey with | Some k -> (Hashtbl.add Crypto.pub_key_map addr k; Printf.printf "; received its public key") | None -> ());
  print_newline ();
  (* if need key exchange, then reply immediately *)
  if !use_PKI && (not (Hashtbl.mem write_fds addr)) then ignore (build_connection_to addr) else ()

let check_for_new_connections () =
  let fds = [listen_fd] in
  let (ready_fds, _, _) = retry_until_no_eintr (fun () -> select fds [] [] 0.0) in
  List.iter (fun _ -> new_conn ()) ready_fds

let wait_for_the_response (addr : address) =
  while not (Hashtbl.mem Crypto.pub_key_map addr) do
    check_for_new_connections ()
  done

let get_write_fd (addr : address) =
  try Hashtbl.find write_fds addr
  with Not_found ->
    (* at this point, the current node has not made a connection to the node at addr yet *)
    let res = build_connection_to addr in
    (* if need key exchange, then must wait for the response *)
    if !use_PKI then wait_for_the_response addr else ();
    res

(** serialization and deserialization **)

let serialize_packet pkt = Marshal.to_string pkt []
let deserialize_packet s = Marshal.from_string s 0

(** packet-level sending and receiving **)

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

(* a (more debugging-friendly?) version from DiSeL *)
(* attempt to obtain one delivered packet from those ready-to-be-read sockets *)
let get_pkt =
  let max_errors = 3 in
  let errors = ref 0 in
  let rec aux = function
    | [] -> None
    | fd :: fds -> begin
      try
        Some (recv_pkt fd)
      with e -> begin
        Printf.printf "Got exception: %s\n" (Printexc.to_string e);
        Printexc.print_backtrace Stdlib.stdout;
        incr errors;
        if !errors < max_errors
        then aux fds
        else begin
          Printf.printf "Too many errors; aborting.\n%!";
          raise e
        end
      end
    end
  in aux

let send_pkt dst pkt =
  let fd = get_write_fd dst in
  let s = serialize_packet pkt in
  let chunk = Bytes.of_string s in
  send_chunk fd chunk

(* NOTE: another design choice: whether to keep dst in the packet to be sent. 
    for now, keep it for debugging purpose *)
let send_all pkts =
  List.iter (fun pkt -> send_pkt (fst pkt) pkt) pkts
