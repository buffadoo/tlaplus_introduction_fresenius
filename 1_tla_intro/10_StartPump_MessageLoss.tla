---- MODULE 10_StartPump_MessageLoss ----
\* Extends the happy path from 9_StartPump_HappyPath.tla to add message loss.
\* Same base setup: RackController sends one START command to one Pump over a channel.
\* This scenario adds the possibility of message loss.

EXTENDS Naturals, Sequences

VARIABLES channel, pumpState, startWasSent

\* startWasSent is a ghost variable: it exists only to state the property
\* below, not to run the system. Without it, TLC's counterexample would be
\* the boring, meaningless one -- "nothing was ever sent, so the pump isn't
\* infusing" -- true on the very first state. startWasSent rules that out:
\* it only ever flips on once RackController genuinely sends something.

Init ==
    /\ channel = <<>>
    /\ pumpState = "idle"
    /\ startWasSent = FALSE

\* RackController's only action: put "START" on the wire.
RackControllerSendStart ==
    /\ channel = <<>>
    /\ channel' = <<"START">>
    /\ pumpState' = pumpState
    /\ startWasSent' = TRUE

\* Pump's only action: take "START" off the wire and actually start.
PumpReceivesStart ==
    /\ channel = <<"START">>
    /\ channel' = <<>>
    /\ pumpState' = "infusing"
    /\ UNCHANGED startWasSent

\* The channel is not reliable: a message sitting in it can simply vanish.
\* Nothing "goes wrong" here in the model -- this is a plain, always-available
\* action, exactly as legal as delivery.
MessageLost ==
    /\ channel = <<"START">>
    /\ channel' = <<>>
    /\ UNCHANGED <<pumpState, startWasSent>>

Next ==
    \/ RackControllerSendStart
    \/ PumpReceivesStart
    \/ MessageLost

Spec == Init /\ [][Next]_<<channel, pumpState, startWasSent>>

\* The naive assumption: "once the rack has sent START and the channel is
\* clear again, the pump must be infusing." Deliberately false -- TLC's
\* counterexample IS the teaching point.
StartAlwaysArrives ==
    (startWasSent /\ channel = <<>>) => (pumpState = "infusing")

====
