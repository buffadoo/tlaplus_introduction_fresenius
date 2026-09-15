---- MODULE 9_StartPump_HappyPath ----
\* Minimal training example: a RackController sends one START command to one
\* Pump over a channel. Deliberately as small as possible -- just enough to
\* show two things: (1) components only ever touch the shared channel, never
\* each other's state directly, and (2) a message sitting in the channel is
\* not the same thing as a message that arrives.
\*
\* Base specification with the happy path only (no message loss).
\* See 10_StartPump_MessageLoss.tla which extends this to add message loss.

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

Next ==
    \/ RackControllerSendStart
    \/ PumpReceivesStart

Spec == Init /\ [][Next]_<<channel, pumpState, startWasSent>>

\* NeverInfusing is deliberately false, satisfied only by the ordinary happy
\* path (the only way to reach pumpState = "infusing" at all is
\* RackControllerSendStart immediately followed by PumpReceivesStart).
\* TLC's shortest counterexample is the clean 3-state "it just works" trace.
NeverInfusing ==
    pumpState # "infusing"

====
