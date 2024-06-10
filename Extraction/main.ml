open Shim
open Shim.Net
open Configuration.Config

(* the wrapper of wrapper; adapted from Toychain/DiSeL *)
let procMsg_wrapper_wrapper f pr =
  let _ = check_for_new_connections () in
  (* check whether some packet has been delivered to some socket *)
  let fds = get_all_read_fds () in
  let (ready_fds, _, _) = retry_until_no_eintr (fun () -> Unix.select fds [] [] 0.0) in
  begin
    (* only process a single packet each time *)
    match get_pkt ready_fds with
    | None -> (* nothing available *) None
    | Some (src, (dst, msg)) ->
      if dst <> (!me_ip, !me_port)
      then begin
        Printf.printf "dst: %s %!" (string_of_address dst);
        Printf.printf " - packet sent in error? (we're not the destination!)";
        print_newline ();
        None
      end else begin 
        f src msg pr 
      end
  end

let main_loop () =
  (* first class module! *)
  let module RealRBP = Companions.RB.Lazymod (struct end) in
  let pr = RealRBP.run (!me_ip, !me_port) !behavior_mode in
  pr procMsg_wrapper_wrapper

let _ =
  Cli.parse_args ();
  Cli.debug_print ();
  Net.setup ();
  (* Wait so other nodes in the cluster have time to start listening *)
  Unix.sleep 1;
  main_loop ()
