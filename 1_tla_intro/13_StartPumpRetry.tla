---- MODULE 13_StartPumpRetry ----
\* Second step in the training story: can we build a protocol that survives
\* message loss? Answer: yes, with retry + acknowledgement + bounded loss.
\* MaxLosses bounds it: the channel may still lose messages, just not an
\* unbounded number of them in one run. Proves BOTH safety and liveness.

EXTENDS Naturals, Sequences

CONSTANTS MaxLosses

\* acked is RackController's BELIEF that the pump confirmed -- not the
\* pump's actual state. pumpState is ground truth; acked is what the sender
\* thinks it knows. The two can disagree when ACK is lost.
VARIABLES channel, ackChannel, pumpState, acked, lossesSoFar

vars == <<channel, ackChannel, pumpState, acked, lossesSoFar>>

Init ==
    /\ channel = <<>>
    /\ ackChannel = <<>>
    /\ pumpState = "idle"
    /\ acked = FALSE
    /\ lossesSoFar = 0

\* RackController keeps (re)sending START for as long as it hasn't been
\* acked -- this IS the retry. No cap on how many times it may try.
RackControllerSendStart ==
    /\ ~acked
    /\ channel = <<>>
    /\ channel' = <<"START">>
    /\ UNCHANGED <<ackChannel, pumpState, acked, lossesSoFar>>

\* Pump starts infusing and acknowledges, in the SAME step. This is
\* idempotent by construction: receiving a second, redundant START
\* (because an earlier ACK was lost) just re-sends the ACK.
PumpReceivesStart ==
    /\ channel = <<"START">>
    /\ ackChannel = <<>>
    /\ channel' = <<>>
    /\ ackChannel' = <<"ACK">>
    /\ pumpState' = "infusing"
    /\ UNCHANGED <<acked, lossesSoFar>>

RackControllerReceivesAck ==
    /\ ackChannel = <<"ACK">>
    /\ ackChannel' = <<>>
    /\ acked' = TRUE
    /\ UNCHANGED <<channel, pumpState, lossesSoFar>>

\* Message loss: START can be lost in transit, but only up to MaxLosses.
MessageLost ==
    /\ channel = <<"START">>
    /\ lossesSoFar < MaxLosses
    /\ channel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ UNCHANGED <<ackChannel, pumpState, acked>>

\* Ack loss: the acknowledgement can also be lost, but bounded.
AckLost ==
    /\ ackChannel = <<"ACK">>
    /\ lossesSoFar < MaxLosses
    /\ ackChannel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
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

\* LIVENESS: with bounded loss and fairness, eventually confirmation arrives.
EventuallyConfirmed == <>acked

\* TLC ALIAS: show rack's belief vs ground truth in traces.
TraceView ==
    [ channel                          |-> channel,
      ackChannel                       |-> ackChannel,
      pumpState                        |-> pumpState,
      rackControllerBelievesPumpState  |-> IF acked THEN "infusing" ELSE "idle",
      acked                            |-> acked ]

====
