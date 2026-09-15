---- MODULE 5_WolfGoatCabbage ----
\* Ported from ~/Projects/medtronic_models/1_tla_intro/6_WolfGoatCabbage.tla. A
\* deliberate change of register from steps 1-4: TLC isn't just checking an
\* invariant here, it's about to be used to FIND A SOLUTION -- a genuinely
\* different use of the same tool, worth calling out explicitly (see
\* 6_WolfGoatCabbage_Solution.tla and 7_WolfGoatCabbage_SolutionTrace.tla).
\*
\* River crossing: farmer, wolf, goat, cabbage. Boat holds farmer plus at most one cargo.
\* Wolf eats goat if alone together; goat eats cabbage if alone together.
\*
\* Items is {Wolf, Goat, Cabbage}. Next allows any legal boat move; SafeShores is the
\* safety invariant (nothing eaten). Careless moves violate it -- TLC finds a short trace.

CONSTANTS Wolf, Goat, Cabbage

Items == {Wolf, Goat, Cabbage}

VARIABLES farmer, leftBank, rightBank

vars == <<farmer, leftBank, rightBank>>

\* Danger conditions: prey and predator left on the same bank.
WolfEatsGoat(items) ==
    Wolf \in items /\ Goat \in items

GoatEatsCabbage(items) ==
    Goat \in items /\ Cabbage \in items

\* No danger: neither predator nor prey pairs are together.
NoDanger(items) ==
    /\ ~WolfEatsGoat(items)
    /\ ~GoatEatsCabbage(items)

\* Farmer is supervising this bank.
FarmerPresent(bankName) ==
    farmer = bankName

\* A bank is safe: either the farmer is there, or there is no danger.
BankSafe(bankName, items) ==
    FarmerPresent(bankName) \/ NoDanger(items)

SafeShores ==
    /\ BankSafe("left", leftBank)
    /\ BankSafe("right", rightBank)

\* Standard winning configuration (farmer and all cargo on the right bank).
Solved ==
    /\ farmer = "right"
    /\ leftBank = {}
    /\ rightBank = Items

Init ==
    /\ farmer = "left"
    /\ leftBank = Items
    /\ rightBank = {}

CrossAloneToRight ==
    /\ farmer = "left"
    /\ farmer' = "right"
    /\ UNCHANGED <<leftBank, rightBank>>

CrossAloneToLeft ==
    /\ farmer = "right"
    /\ farmer' = "left"
    /\ UNCHANGED <<leftBank, rightBank>>

CrossWithToRight(x) ==
    /\ farmer = "left"
    /\ x \in leftBank
    /\ farmer' = "right"
    /\ leftBank' = leftBank \ {x}
    /\ rightBank' = rightBank \union {x}

CrossWithToLeft(x) ==
    /\ farmer = "right"
    /\ x \in rightBank
    /\ farmer' = "left"
    /\ rightBank' = rightBank \ {x}
    /\ leftBank' = leftBank \union {x}

Next ==
    \/ CrossAloneToRight
    \/ CrossAloneToLeft
    \/ \E x \in Items : CrossWithToRight(x)
    \/ \E x \in Items : CrossWithToLeft(x)

Spec == Init /\ [][Next]_vars

====
