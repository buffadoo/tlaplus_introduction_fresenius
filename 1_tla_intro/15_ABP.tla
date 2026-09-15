---- MODULE 15_ABP ----
\* The Alternating Bit Protocol (Bartlett, Scantlebury & Wilkinson, 1969).
\* Fixes the duplicate-application bug that spec 16 (ABP_NoBit) exposes.
\* The fix: tag every message and every ack with ONE alternating bit.
\* - Sender flips bit when current command is acked (proves receiver got it)
\* - Receiver flips bit when it accepts a new message (bit matches)
\* - Stale/resent messages (old bit) get acked but NOT re-applied
\*
\* Result: scales spec 12's retry+ack pattern to streams of commands,
\* guarantees exactly-once delivery (no duplicates) under bounded loss,
\* and works over unbounded latency delays (bit-matching handles old acks).
\* This is why MQTT QoS 2 exists; ABP is its core mechanism.

EXTENDS Naturals, Sequences

CONSTANTS CommandSeq, MaxLosses

ExampleCommandSeq == <<"START", "STOP">>

VARIABLES channel, ackChannel, nextToSend, bitOut, pumpApplied, expectedBit, lossesSoFar

vars == <<channel, ackChannel, nextToSend, bitOut, pumpApplied, expectedBit, lossesSoFar>>

Init ==
    /\ channel = <<>>
    /\ ackChannel = <<>>
    /\ nextToSend = 1
    /\ bitOut = 0
    /\ pumpApplied = <<>>
    /\ expectedBit = 0
    /\ lossesSoFar = 0

\* Sends (or resends -- same action, same message, indistinguishable to an
\* outside observer, exactly as in Milner's own SEND/SENDING) the current
\* command tagged with the CURRENT bitOut. bitOut only changes once THIS
\* command is actually acked (RackControllerReceivesAck below) -- so every
\* resend of the same command carries the identical bit.
RackControllerSend ==
    /\ nextToSend <= Len(CommandSeq)
    /\ channel = <<>>
    /\ channel' = <<[cmd |-> CommandSeq[nextToSend], bit |-> bitOut]>>
    /\ UNCHANGED <<ackChannel, nextToSend, bitOut, pumpApplied, expectedBit, lossesSoFar>>

\* Milner's REPLYING: if the arriving bit matches what the receiver is
\* waiting for, this is genuinely the NEXT message -- apply it, flip
\* expectedBit, and ack with that bit. If the bit does NOT match, this is a
\* resend of the message already applied last round -- do NOT re-apply it,
\* but DO ack it (with the bit actually received) so the sender's own
\* resend eventually gets the ack it's waiting for and can move on.
PumpReceivesAndApplies ==
    /\ channel # <<>>
    /\ LET msg == Head(channel)
       IN /\ channel' = <<>>
          /\ ackChannel' = <<msg.bit>>
          /\ IF msg.bit = expectedBit
             THEN /\ pumpApplied' = Append(pumpApplied, msg.cmd)
                  /\ expectedBit' = 1 - expectedBit
             ELSE UNCHANGED <<pumpApplied, expectedBit>>
    /\ UNCHANGED <<nextToSend, bitOut, lossesSoFar>>

\* Only an ack matching the CURRENT outstanding bit actually advances the
\* protocol -- a stale ack (bit doesn't match bitOut, left over from an
\* earlier round replaying through a slow channel) is consumed and ignored.
RackControllerReceivesAck ==
    /\ ackChannel # <<>>
    /\ LET b == Head(ackChannel)
       IN /\ ackChannel' = <<>>
          /\ IF b = bitOut
             THEN /\ nextToSend' = nextToSend + 1
                  /\ bitOut' = 1 - bitOut
             ELSE UNCHANGED <<nextToSend, bitOut>>
    /\ UNCHANGED <<channel, pumpApplied, expectedBit, lossesSoFar>>

MessageLost ==
    /\ channel # <<>>
    /\ lossesSoFar < MaxLosses
    /\ channel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ UNCHANGED <<ackChannel, nextToSend, bitOut, pumpApplied, expectedBit>>

AckLost ==
    /\ ackChannel # <<>>
    /\ lossesSoFar < MaxLosses
    /\ ackChannel' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ UNCHANGED <<channel, nextToSend, bitOut, pumpApplied, expectedBit>>

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

\* SAFETY (Milner's BUFF property, restated as an invariant rather than a
\* process-equivalence claim): the receiver's applied sequence is always an
\* honest, in-order, duplicate-free prefix of what was sent. True even
\* without the bound on loss or any fairness assumption.
DeliveryIsExactlyOnce ==
    pumpApplied = SubSeq(CommandSeq, 1, Len(pumpApplied))

\* LIVENESS: given bounded loss (not adversarial forever) and fairness on
\* the three real actions, every command eventually gets through.
EventuallyAllDelivered == <>(pumpApplied = CommandSeq)

====
