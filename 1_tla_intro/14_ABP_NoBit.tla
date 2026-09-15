---- MODULE 14_ABP_NoBit ----
\* Next step after 12_StartPumpRetry: generalize from ONE command to a STREAM.
\* RackController sends CommandSeq (e.g., <<START, STOP>>) one by one.
\* Each uses the same retry+ack pattern as spec 12. But now we expose a fatal
\* flaw: with no tag on messages/acks, a resend and a genuinely new message
\* look identical to the pump. Spec 12 worked because re-applying "START"
\* twice was harmless (pump stays "infusing"). Applying "START" then "STOP"
\* twice each is not. TLC finds the duplicate application immediately.

EXTENDS Naturals, Sequences

CONSTANTS CommandSeq, MaxLosses

\* Concrete value for the .cfg to bind via "CommandSeq <- ExampleCommandSeq"
\* -- TLC's own .cfg parser doesn't accept a literal <<...>> on a CONSTANTS
\* line directly, only a name defined in the module.
ExampleCommandSeq == <<"START", "STOP">>

VARIABLES channel, ackChannel, nextToSend, pumpApplied, lossesSoFar

vars == <<channel, ackChannel, nextToSend, pumpApplied, lossesSoFar>>

Init ==
    /\ channel = <<>>
    /\ ackChannel = <<>>
    /\ nextToSend = 1
    /\ pumpApplied = <<>>
    /\ lossesSoFar = 0

\* Sends (or, indistinguishably, RE-sends) the current command. Nothing here
\* can tell "first attempt" from "retry" apart -- that is exactly the point.
RackControllerSend ==
    /\ nextToSend <= Len(CommandSeq)
    /\ channel = <<>>
    /\ channel' = <<CommandSeq[nextToSend]>>
    /\ UNCHANGED <<ackChannel, nextToSend, pumpApplied, lossesSoFar>>

\* Applies whatever arrived and acks it -- no way to recognize a duplicate.
PumpReceivesAndApplies ==
    /\ channel # <<>>
    /\ pumpApplied' = Append(pumpApplied, Head(channel))
    /\ channel' = <<>>
    /\ ackChannel' = <<"ACK">>
    /\ UNCHANGED <<nextToSend, lossesSoFar>>

RackControllerReceivesAck ==
    /\ ackChannel # <<>>
    /\ ackChannel' = <<>>
    /\ nextToSend' = nextToSend + 1
    /\ UNCHANGED <<channel, pumpApplied, lossesSoFar>>

MessageLost ==
    /\ channel # <<>>
    /\ lossesSoFar < MaxLosses
    /\ channel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ UNCHANGED <<ackChannel, nextToSend, pumpApplied>>

AckLost ==
    /\ ackChannel # <<>>
    /\ lossesSoFar < MaxLosses
    /\ ackChannel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ UNCHANGED <<channel, nextToSend, pumpApplied>>

Next ==
    \/ RackControllerSend
    \/ PumpReceivesAndApplies
    \/ RackControllerReceivesAck
    \/ MessageLost
    \/ AckLost

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(RackControllerSend)
    /\ WF_vars(PumpReceivesAndApplies)
    /\ WF_vars(RackControllerReceivesAck)

\* Milner's own correctness criterion for this exact class of protocol
\* ("Communication and Concurrency"): the receiver's applied sequence is
\* always a genuine, in-order PREFIX of what was sent -- no loss, no
\* reordering, no duplication. Deliberately checkable as one invariant.
DeliveryIsExactlyOnce ==
    pumpApplied = SubSeq(CommandSeq, 1, Len(pumpApplied))

====
