------------- MODULE 8c_AirInLineExercise_Solution -------------
\* The fix: a separate StopOnAirDetection action, not a change to DetectAir itself.
\* DetectAir only ever raises the sensor flag; StopOnAirDetection is the pump's own
\* reaction to that flag. Detecting air and stopping the pump are two
\* distinct steps, each visible on its own in the trace.
\*
\* Because they're separate steps, "never infusing with air" can't hold as
\* a plain invariant: the state right after DetectAir fires (pump still
\* infusing, air now flagged) is real and reachable, one step before
\* StopOnAirDetection gets to run. No tracking variable is needed to express the
\* real requirement, though: CanAlwaysStopOnAirDetection says directly that
\* whenever the pump is infusing with air detected, StopOnAirDetection is available
\* to fix it, using ENABLED instead of a hand-kept flag.
\*
\* stoppedByAir is a ghost variable, latched only by StopOnAirDetection. It doesn't
\* affect pumpState or airInLine; it exists so 8d's trap invariant can
\* demand a trace where the interlock itself reacts, not just any path
\* that happens to end with the pump stopped (the operator's own plain
\* Stop reaches the same pumpState/airInLine values without proving
\* anything about the interlock).
EXTENDS FiniteSets, TLC

VARIABLES pumpState, airInLine, stoppedByAir

Init ==
    /\ pumpState = "stopped"
    /\ airInLine = FALSE
    /\ stoppedByAir = FALSE

Start ==
    /\ pumpState = "stopped"
    /\ airInLine = FALSE
    /\ pumpState' = "infusing"
    /\ UNCHANGED airInLine
    /\ UNCHANGED stoppedByAir

Stop ==
    /\ pumpState = "infusing"
    /\ pumpState' = "stopped"
    /\ UNCHANGED airInLine
    /\ UNCHANGED stoppedByAir

DetectAir ==
    /\ airInLine = FALSE
    /\ airInLine' = TRUE
    /\ UNCHANGED pumpState
    /\ UNCHANGED stoppedByAir

StopOnAirDetection ==
    /\ pumpState = "infusing"
    /\ airInLine = TRUE
    /\ pumpState' = "stopped"
    /\ UNCHANGED airInLine
    /\ stoppedByAir' = TRUE

ClearAir ==
    /\ airInLine = TRUE
    /\ airInLine' = FALSE
    /\ UNCHANGED pumpState
    /\ UNCHANGED stoppedByAir

Next ==
    \/ Start
    \/ Stop
    \/ DetectAir
    \/ StopOnAirDetection
    \/ ClearAir

Spec ==
    Init /\ [][Next]_<<pumpState, airInLine, stoppedByAir>>

CanAlwaysStopOnAirDetection ==
    (pumpState = "infusing" /\ airInLine = TRUE) => ENABLED StopOnAirDetection

====
