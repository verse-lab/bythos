From ABCProtocol.Systems Require Export Protocol.

Module Type NetState (Export A : NetAddr) (Export M : MessageType) 
  (Export P : PacketType) (Export Pr : Protocol A M P).

(* using a map library seems to be overkill *)
(* FIXME: make this total or partial? maybe we should only represent the states of non-Byzantine nodes *)

Definition StateMap := Address -> State. 
Definition initState := (fun n => Init n).

Definition upd (n : Address) (st : State) (states : StateMap) : StateMap :=
  fun m => if Address_eqdec n m then st else states m.

Definition PacketSoup := list Packet.

(* holistic network state *)
Record World :=
  mkW {
    localState : StateMap;
    sentMsgs : PacketSoup;
  }.

Definition initWorld := mkW initState nil.

End NetState.

Module NetStateImpl (Export A : NetAddr) (Export M : MessageType) 
  (Export P : PacketType) (Export Pr : Protocol A M P) <: NetState A M P Pr.

Include (NetState A M P Pr).

End NetStateImpl.
