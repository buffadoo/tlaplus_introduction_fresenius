------------------------ MODULE 3_BoundedCounter ------------------------
\* Ported from ~/Projects/tlaplus/vending_machine_kata/3_constraining_state_part_3.tla
\* (the Increment/Decrement-operator version, not the inline part_2 variant --
\* same behavior, cleaner to read). Fixes 2_UnboundedCounter.tla's problem by
\* actually bounding the variable in Next itself (min_value/max_value), not
\* by adding a CONSTRAINT on top of an unbounded Next -- x can never reach 10
\* here, so XBound now holds.
EXTENDS Naturals

CONSTANTS min_value, max_value

VARIABLE x

Increment(v) ==
    /\ v < max_value
    /\ v' = v + 1

Decrement(v) ==
    /\ v > min_value
    /\ v' = v - 1

Init ==
    x = 0

Next ==
    \/ Increment(x)
    \/ Decrement(x)

Spec ==
    Init /\ [][Next]_<<x>>

XBound ==
    x < 10

====
