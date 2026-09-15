---- MODULE 12_StartPumpRetry_HappyPath ----
\* Retry + acknowledgement protocol: can we build something that survives
\* message loss? Ingredients: (1) RackController keeps retrying while
\* waiting for ACK, (2) Pump acknowledges when it receives START.
\* This shows the MECHANISM works, but with UNBOUNDED loss -- like 11.
\* Show this first to demonstrate the basic idea; later we add a loss bound.

EXTENDS Naturals, Sequences

\* acked is RackController's BELIEF that the pump confirmed -- not the
\* pump's actual state. pumpState is ground truth; acked is what the sender
\* thinks it knows. The two can disagree when ACK is lost.
VARIABLES channel, ackChannel, pumpState, acked

vars == <<channel, ackChannel, pumpState, acked>>

Init ==
    /\ channel = <<>>
    /\ ackChannel = <<>>
    /\ pumpState = "idle"
    /\ acked = FALSE

\* RackController keeps (re)sending START for as long as it hasn't been
\* acked -- this IS the retry. No cap on how many times it may try.
RackControllerSendStart ==
    /\ ~acked
    /\ channel = <<>>
    /\ channel' = <<"START">>
    /\ UNCHANGED <<ackChannel, pumpState, acked>>

\* Pump starts infusing and acknowledges, in the SAME step. This is
\* idempotent by construction: receiving a second, redundant START
\* (because an earlier ACK was lost) just re-sends the ACK.
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

\* Message loss: START can be lost in transit.
MessageLost ==
    /\ channel = <<"START">>
    /\ channel' = <<>>
    /\ UNCHANGED <<ackChannel, pumpState, acked>>

\* Ack loss: the acknowledgement can also be lost.
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

\* Fairness on the three "good" actions -- retry, receive, ack -- ensures
\* they keep happening. NO fairness on loss actions.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(RackControllerSendStart)
    /\ WF_vars(PumpReceivesStart)
    /\ WF_vars(RackControllerReceivesAck)

\* SAFETY: if RackController believes confirmation, pump is really infusing.
AckMeansReallyInfusing ==
    acked => (pumpState = "infusing")

====
