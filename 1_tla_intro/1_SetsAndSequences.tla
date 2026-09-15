------------------------ MODULE 1_SetsAndSequences ------------------------
\* Very first TLA+ scenario: no state change, just the operators. Ported
\* from ~/Projects/tlaplus/vending_machine_kata/1_sequences_and_sets.tla (the
\* same live-demo material this deck's own "Vending machine" section builds
\* on) -- copied here as the true starting point, before anything
\* domain-specific.
EXTENDS FiniteSets, Sequences, TLC

VARIABLES
    chars1,
    chars2,
    numbers1,
    numbers2

Init ==
    /\ chars1 = {"a", "b", "c"}
    /\ chars2 = {"c", "d", "f"}
    /\ numbers1 = {1, 2}
    /\ numbers2 = {3, 4}

Next ==
    /\ PrintT ("chars1 \\union chars2")
    /\ PrintT (chars1 \union chars2)

    /\ PrintT ("chars1 \\intersect chars2")
    /\ PrintT (chars1 \intersect chars2)

    \* The elements in chars1 not in chars2
    /\ PrintT ("chars1 \\ chars2")
    /\ PrintT (chars1 \ chars2)

    \* cross product
    /\ PrintT ("chars1 \\X numbers2")
    /\ PrintT (chars1 \X numbers2)

    \* SUBSET numbers1
    /\ PrintT ("SUBSET numbers1")
    /\ PrintT (SUBSET numbers1)

    /\ chars1' = chars1
    /\ chars2' = chars2
    /\ numbers1' = numbers1
    /\ numbers2' = numbers2

Spec ==
    Init /\ [][Next]_<<chars1, chars2, numbers1, numbers2>>

====
