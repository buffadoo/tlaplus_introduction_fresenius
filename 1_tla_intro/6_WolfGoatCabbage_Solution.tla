---- MODULE 6_WolfGoatCabbage_Solution ----
\* Extends the base model: only boat moves that keep shores safe (SafeShores in the next state).
\* Invariant AllCargoOnRightMeansSolved states the solution -- if everything is on the right bank,
\* the farmer is there too (the usual puzzle goal).
EXTENDS 5_WolfGoatCabbage

\* Named steps so TLC error traces label each crossing.
SafeCrossAloneToRight ==
    CrossAloneToRight /\ SafeShores'

SafeCrossAloneToLeft ==
    CrossAloneToLeft /\ SafeShores'

SafeCrossWithToRight(x) ==
    CrossWithToRight(x) /\ SafeShores'

SafeCrossWithToLeft(x) ==
    CrossWithToLeft(x) /\ SafeShores'

SafeNext ==
    \/ SafeCrossAloneToRight
    \/ SafeCrossAloneToLeft
    \/ \E x \in Items : SafeCrossWithToRight(x)
    \/ \E x \in Items : SafeCrossWithToLeft(x)

SolutionSpec ==
    Init /\ [][SafeNext]_vars

\* Winning layout: all cargo across the river iff the full Solved predicate holds (farmer on right).
AllCargoOnRightMeansSolved ==
    (leftBank = {} /\ rightBank = Items) <=> Solved

====
