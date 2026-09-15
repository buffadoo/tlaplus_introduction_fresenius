---- MODULE 7_WolfGoatCabbage_SolutionTrace ----
\* Pair with 7_WolfGoatCabbage_SolutionTrace.cfg: TLC violates this invariant at Solved and prints
\* a shortest safe crossing sequence (BFS counterexample) -- this is the payoff step: TLC isn't
\* reporting a bug here, it's being used as a SOLVER, and the "violation" it reports is the
\* solution itself (Solved being reached at all is what the deliberately-false invariant forces
\* TLC to search for and print).
EXTENDS 6_WolfGoatCabbage_Solution

\* Invariant: we haven't reached Solved yet. TLC finds when this is violated (the solution).
NotSolved ==
    ~Solved

====
