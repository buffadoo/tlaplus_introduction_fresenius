-------- MODULE 8b_AirInLineExercise_Invariant --------
\* Companion to 8a_AirInLineExercise.tla: adds the invariant a candidate
\* should have written for the exercise, without changing any action.
\* NoInfusingWithAir is not deliberately false -- it's the real safety
\* property -- and TLC finds a genuine violation: DetectAir has no effect
\* on pumpState, so the pump keeps infusing once air is detected.
EXTENDS 8a_AirInLineExercise

NoInfusingWithAir ==
    ~(pumpState = "infusing" /\ airInLine = TRUE)

====
