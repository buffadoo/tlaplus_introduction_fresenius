----------------------- MODULE 8_SimpleStateMachine -----------------------
\* Simple state machine for an infusion pump.
\* The pump can be in one of two states: "idle" or "infusing".
\* Point of this one is purely the shape of an action -- a guard on the
\* CURRENT state, an update to the NEXT (primed) state.
\* 
\* This is a prelude to 8a_AirInLineExercise, which adds a second variable
\* (airInLine) and a safety constraint.
EXTENDS FiniteSets, TLC

VARIABLE pumpState

Start ==
    /\ pumpState = "idle"
    /\ pumpState' = "infusing"

Stop ==
    /\ pumpState = "infusing"
    /\ pumpState' = "idle"

Init ==
    pumpState = "idle"

Next ==
    \/ Start
    \/ Stop

Spec ==
    Init /\ [][Next]_<<pumpState>>

====
