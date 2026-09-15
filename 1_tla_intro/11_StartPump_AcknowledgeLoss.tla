---- MODULE 11_StartPump_AcknowledgeLoss ----
\* One step beyond 10_StartPump_MessageLoss: add an ACK handshake so
\* RackController learns when the pump has received the START.
\* 
\* Flow: RackController sends START → Pump receives and sends ACK → 
\* RackController receives ACK and marks acked=TRUE.
\* 
\* If the ACK gets lost, RackController stays stuck thinking the pump
\* hasn't been told yet. This exposes the problem: acknowledgement loss
\* breaks the sender's knowledge of success, even though the pump IS infusing.

EXTENDS Naturals, Sequences

VARIABLES channel, ackChannel, pumpState, acked

vars == <<channel, ackChannel, pumpState, acked>>

Init ==
    /\ channel = <<>>
    /\ ackChannel = <<>>
    /\ pumpState = "idle"
    /\ acked = FALSE

RackControllerSendStart ==
    /\ ~acked
    /\ channel = <<>>
    /\ channel' = <<"START">>
    /\ UNCHANGED <<ackChannel, pumpState, acked>>

PumpReceivesStart ==
    /\ channel = <<"START">>
    /\ ackChannel = <<>>
    /\ channel' = <<>>
    /\ ackChannel' = <<"ACK">>
    /\ pumpState' = "infusing"
    /\ UNCHANGED acked

RackControllerReceivesAck ==
    /\ ackChannel = <<"ACK">>
    /\ ackChannel' = <<>>
    /\ acked' = TRUE
    /\ UNCHANGED <<channel, pumpState>>

\* START can be lost.
MessageLost ==
    /\ channel = <<"START">>
    /\ channel' = <<>>
    /\ UNCHANGED <<ackChannel, pumpState, acked>>

\* ACK can be lost: pump is infusing, but RackController never learns.
AckLost ==
    /\ ackChannel = <<"ACK">>
    /\ ackChannel' = <<>>
    /\ UNCHANGED <<channel, pumpState, acked>>

Next ==
    \/ RackControllerSendStart
    \/ PumpReceivesStart
    \/ RackControllerReceivesAck
    \/ MessageLost
    \/ AckLost

Spec ==
    /\ Init
    /\ [][Next]_vars

====
