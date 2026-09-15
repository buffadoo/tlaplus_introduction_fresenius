---- MODULE 12_StartPumpRetry ----
\* Happy recovery witness: show retry+ack working when loss happens.
\* With bounded loss and fairness, use a latch to force loss to occur,
\* then show the recovery. Demonstrates: loss happens, retry kicks in,
\* RackController finally gets confirmation.

EXTENDS Naturals, Sequences

CONSTANTS MaxLosses

\* acked is RackController's BELIEF that the pump confirmed -- not the
\* pump's actual state. pumpState is ground truth; acked is what the sender
\* thinks it knows. They diverge when ACK is lost.
VARIABLES channel, ackChannel, pumpState, acked, lossesSoFar, lossOccurred

vars == <<channel, ackChannel, pumpState, acked, lossesSoFar, lossOccurred>>

Init ==
    /\ channel = <<>>
    /\ ackChannel = <<>>
    /\ pumpState = "idle"
    /\ acked = FALSE
    /\ lossesSoFar = 0
    /\ lossOccurred = FALSE

\* RackController keeps (re)sending START for as long as it hasn't been
\* acked -- this IS the retry. No cap on how many times it may try.
RackControllerSendStart ==
    /\ ~acked
    /\ channel = <<>>
    /\ channel' = <<"START">>
    /\ UNCHANGED <<ackChannel, pumpState, acked, lossesSoFar, lossOccurred>>

\* Pump starts infusing and acknowledges, in the SAME step. This is
\* idempotent by construction: receiving a second, redundant START
\* (because an earlier ACK was lost) just re-sends the ACK.
PumpReceivesStart ==
    /\ channel = <<"START">>
    /\ ackChannel = <<>>
    /\ channel' = <<>>
    /\ ackChannel' = <<"ACK">>
    /\ pumpState' = "infusing"
    /\ UNCHANGED <<acked, lossesSoFar, lossOccurred>>

RackControllerReceivesAck ==
    /\ ackChannel = <<"ACK">>
    /\ ackChannel' = <<>>
    /\ acked' = TRUE
    /\ UNCHANGED <<channel, pumpState, lossesSoFar, lossOccurred>>

\* Message loss: START can be lost in transit, but bounded.
\* Marks that loss occurred ONLY if pump hasn't started yet (lost message
\* prevents pump from receiving, forcing retry). Losses after pump has started
\* don't count toward the story (redundant retries).
MessageLost ==
    /\ channel = <<"START">>
    /\ pumpState = "idle"
    /\ lossesSoFar < MaxLosses
    /\ channel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ lossOccurred' = TRUE
    /\ UNCHANGED <<ackChannel, pumpState, acked>>

\* Ack loss: the acknowledgement can also be lost, but bounded.
AckLost ==
    /\ ackChannel = <<"ACK">>
    /\ lossesSoFar < MaxLosses
    /\ ackChannel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ lossOccurred' = TRUE
    /\ UNCHANGED <<channel, pumpState, acked>>

Next ==
    \/ RackControllerSendStart
    \/ PumpReceivesStart
    \/ RackControllerReceivesAck
    \/ MessageLost
    \/ AckLost

\* Fairness on the three "good" actions -- retry, receive, ack.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(RackControllerSendStart)
    /\ WF_vars(PumpReceivesStart)
    /\ WF_vars(RackControllerReceivesAck)

\* SAFETY: if RackController believes confirmation, pump is really infusing.
AckMeansReallyInfusing ==
    acked => (pumpState = "infusing")

\* Witness: force TLC to show a path where loss happened (before pump started)
\* AND the protocol still recovered to confirmed state. This shows retry at work.
ShowsRecovery ==
    ~(lossOccurred /\ acked)

\* TLC ALIAS (set in .cfg): show what RackController believes vs ground truth.
\* Rack believes pump is infusing when acked=TRUE, but ground truth is pumpState.
\* On ACK loss, these diverge (pump has moved on, rack still thinks it's idle).
TraceView ==
    [ channel                          |-> channel,
      ackChannel                       |-> ackChannel,
      pumpState                        |-> pumpState,
      rackControllerBelievesPumpState  |-> IF acked THEN "infusing" ELSE "idle",
      acked                            |-> acked,
      lossOccurred                     |-> lossOccurred ]

====
