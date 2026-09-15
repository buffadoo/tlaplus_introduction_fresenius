------------------- MODULE 8a_AirInLineExercise -------------------
\* EXERCISE. Same action shape as 8_SimpleStateMachine.tla (a guard on the
\* current state, an update to the next), now with a second variable and a
\* real domain safety rule to check: the pump must never be "infusing"
\* while air is detected in the line.
\*
\* This module deliberately has no invariant yet -- writing it is the
\* exercise. Add it to 8a_AirInLineExercise.cfg once you've written it,
\* then run TLC and see what it reports.
EXTENDS FiniteSets, TLC

VARIABLES pumpState, airInLine

Init ==
    /\ pumpState = "idle"
    /\ airInLine = FALSE

Start ==
    /\ pumpState = "idle"
    /\ airInLine = FALSE
    /\ pumpState' = "infusing"
    /\ UNCHANGED airInLine

Stop ==
    /\ pumpState = "infusing"
    /\ pumpState' = "idle"
    /\ UNCHANGED airInLine

DetectAir ==
    /\ airInLine' = TRUE
    /\ UNCHANGED pumpState

ClearAir ==
    /\ airInLine' = FALSE
    /\ UNCHANGED pumpState

Next ==
    \/ Start
    \/ Stop
    \/ DetectAir
    \/ ClearAir

Spec ==
    Init /\ [][Next]_<<pumpState, airInLine>>

====
