open Shim
open Shim.Net
open Companions.Common
open Configuration.Config

open Companions.RB

(* the wrapper of wrapper; adapted from Toychain/DiSeL *)
let procMsg_wrapper_wrapper pr =
  let () = check_for_new_connections () in
  let fds = get_all_read_fds () in
  let (ready_fds, _, _) = retry_until_no_eintr (fun () -> Unix.select fds [] [] 0.0) in
  begin
    match get_pkt ready_fds with
    | None -> (* nothing available *) None
    | Some (src, pkt) ->
      if fst pkt <> (!me_ip, !me_port) then
      begin
        Printf.printf " - packet sent in error? (we're not the destination!)";
        print_newline ();
        None
      end else procMsg_wrapper src (snd pkt) pr
  end

let main_loop () =
  let pr = get_minimal_protocol (!me_ip, !me_port) in
  while true do
    (* a very simple logic *)
    ignore (procInt_wrapper pr);
    ignore (procMsg_wrapper_wrapper pr);
    ()
  done

let _ =
  Cli.parse_args ();
  Cli.debug_print ();
  Net.setup ();
  (* Wait so other nodes in the cluster have time to start listening *)
  Unix.sleep 1;
  main_loop ()
