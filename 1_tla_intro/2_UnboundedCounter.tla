------------------------ MODULE 2_UnboundedCounter ------------------------
\* Ported from ~/Projects/tlaplus/vending_machine_kata/2_constraining_state.tla.
\* A counter with no upper bound at all. XBound is deliberately false -- the
\* teaching point is that TLC WILL find the violation (it just keeps
\* incrementing until x reaches 10), and that without any bound at all, an
\* unconstrained Nat variable has an infinite state space: TLC can still
\* falsify an invariant here (a finite prefix suffices), but could never
\* finish an EXHAUSTIVE check of this Next as written. See
\* 3_BoundedCounter.tla for the fix.
EXTENDS Naturals

VARIABLE x

Init ==
    x = 0

Next ==
    x' = x + 1

Spec ==
    Init /\ [][Next]_<<x>>

XBound ==
    x < 10

====
