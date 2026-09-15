--------- MODULE 8d_AirInLineExercise_SolutionTrace ---------
\* Companion to 8c_AirInLineExercise_Solution.tla, same "trap invariant"
\* trick as 9_StartPump_HappyPath.tla: NeverStoppedWithAirStillFlagged is
\* deliberately false, so TLC's shortest counterexample IS the
\* demonstration -- Start, then DetectAir, then StopOnAirDetection reacting to it.
\* Uses 8c's own stoppedByAir ghost rather than pumpState/airInLine alone:
\* the operator's plain Stop can reach the same pumpState/airInLine values
\* while air is present, which would make TLC report that shorter, less
\* interesting trace instead of the interlock actually reacting.
EXTENDS 8c_AirInLineExercise_Solution

NeverStoppedByAir ==
    ~stoppedByAir

====
