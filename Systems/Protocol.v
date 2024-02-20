From Coq Require Import Bool List.
From Coq Require ssrbool ssreflect.
Import (coercions) ssrbool.
Import ssreflect.SsrSyntax.
From ABCProtocol.Structures Require Export Types.

Module Type Protocol (Export A : NetAddr) (Export M : MessageType) (Export P : PacketType).

Parameter InternalTransition : Type.

Parameter State : Type.
Parameter State_eqdec : forall (s1 s2 : State), {s1 = s2} + {s1 <> s2}.

Parameter Init : Address -> State.

(* TODO later change this name to the more canonical "procMsg" *)
Parameter procMsgWithCheck : State -> Address (* sender *) -> Message -> State * list Packet.
Parameter procInt : State -> InternalTransition -> State * list Packet.

End Protocol.

(*
Module Type Protocol' (Export A : NetAddr) (Export M : MessageType) (Export P : SimplePacket A M)(* <: Protocol A M P *).

(* if do not use this instantiation, then Protocol' is essentially Protocol? *)
(* Module Export P <: PacketType := SimplePacketImpl A M. *)
Include (Protocol A M P).

End Protocol'.
*)
