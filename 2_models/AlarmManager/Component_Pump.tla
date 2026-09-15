---- MODULE Component_Pump ----
\* One infusion pump, modeled here ONLY as an alarm-CONDITION SOURCE (not as the
\* start/stop-command participant 2_models/InfusionPumpRack/Component_Pump.tla models --
\* this is a separate app folder, scoped narrowly to the Alarm Manager's own
\* responsibilities). A pump can independently raise and clear each of a fixed set of
\* alarm conditions (AlarmTypes); it never receives anything on this channel, it only
\* ever publishes.
\*
\* GROUND TRUTH, LOCAL-FIRST: `pump.conditions[type]` IS the real, authoritative state of
\* whether this pump currently has condition `type` active -- updated in the SAME atomic
\* step as the publish that announces it (a real pump detects a condition and reports it
\* as one indivisible local act; there is no separate "detected but not yet told anyone"
\* state modeled here). The Alarm Manager's own belief about this pump (see
\* Component_AlarmManager.tla) is a SEPARATE, remote copy that only updates once the
\* announcement has actually traveled the channel's dispatching->inbox hop and been
\* processed -- the gap between the two is exactly what this model exists to make
\* representable.
\*
\* Per the composition rule (.cursor/rules/mqtt-tla-composition-and-traces.mdc sec 3,
\* generalized to this channel primitive): every action here reads/writes only `pump`
\* and `channel` -- never the Alarm Manager's own variable, even indirectly.
\*
\* NO PER-APP INFRASTRUCTURE WRAPPER, and channel universe (ClientIds/TopicNames/
\* Payloads/Subscribers) AND the fixed alarm-type domain baked directly into this
\* component's own definitions, duplicated by hand across every site that shares the
\* `channel` variable -- same idiom 2_models/InfusionPumpRack/Component_Pump.tla already
\* uses for its own Infrastructure_Channel INSTANCE. AlarmTypes is a plain literal
\* definition here, NOT a CONSTANT: it is fixed domain vocabulary (like the ClientIds/
\* TopicNames literals below), not something any scenario in this app wants to vary --
\* same reasoning as Component_RackController.tla's own MaxCommitDeadline-as-literal
\* choice in the InfusionPumpRack sibling (threading it as a CONSTANT would force every
\* .cfg in this directory to also assign it).

EXTENDS Naturals, Sequences

CONSTANTS
    MaxQueueDepth,  \* pass-through to Infrastructure_Channel -- the one genuinely free
                     \* constant in this app, same as the InfusionPumpRack sibling
    PumpId,         \* this pump's own channel ClientId ("Pump1" or "Pump2")
    ConditionTopic  \* this pump's own condition-report topic ("cond/Pump1" or "cond/Pump2")

ASSUME PumpId \in {"Pump1", "Pump2"}
ASSUME ConditionTopic \in {"cond/Pump1", "cond/Pump2"}

VARIABLES pump, channel

\* Fixed universe of alarm condition types this app models -- see header on why this is a
\* literal, not a CONSTANT. Must stay byte-identical to Component_AlarmManager.tla's own
\* copy.
AlarmTypes == {"OCCLUSION", "LOW_BATTERY"}

\* Same fixed literal universe as Component_AlarmManager.tla's/BaseSpec_AlarmManager.tla's
\* own INSTANCE -- must stay byte-identical across all three sites (they all operate on
\* the SAME shared `channel` variable, see this file's header). Payloads is a union of
\* the two payload shapes this app's topics ever carry: a condition-report record (this
\* module's own concern) and a top-priority announcement record (Component_
\* AlarmManager.tla's own "alarm/top" concern) -- every component instances the FULL
\* union even though this one only ever constructs the first shape, exactly as
\* Infrastructure_Channel.tla's single shared `Payloads` CONSTANT requires. Both variants
\* carry a `kind` discriminant field even though it is never branched on here -- TLC's
\* `\in`/equality on a heterogeneous set throws rather than returning FALSE when it has to
\* compare a record against a bare string of a different shape, so the top-priority
\* variant is a one-field RECORD (kind + top), not a bare string, purely so this union
\* stays two record-shaped sets (safe to compare) instead of a record-shaped set and a
\* string-shaped set (unsafe). "alarm/top" has no subscriber yet (no downstream consumer
\* modeled in this first cut) -- still a legal, well-typed topic to publish on (empty
\* recipient set).
Channel == INSTANCE Infrastructure_Channel WITH
    ClientIds     <- {"Pump1", "Pump2", "AlarmManager"},
    TopicNames    <- {"cond/Pump1", "cond/Pump2", "alarm/top"},
    Payloads      <- ([kind: {"CONDITION"}, type: AlarmTypes, event: {"RAISED", "CLEARED"}]
                           \cup [kind: {"TOP_PRIORITY"}, top: AlarmTypes \cup {"NONE"}]),
    MaxQueueDepth <- MaxQueueDepth,
    Subscribers   <- [t \in {"cond/Pump1", "cond/Pump2", "alarm/top"} |->
                          CASE t = "cond/Pump1" -> {"AlarmManager"}
                            [] t = "cond/Pump2" -> {"AlarmManager"}
                            [] t = "alarm/top"  -> {}]

\* A freshly-modeled pump starts with every condition clear -- no alarm is active until an
\* explicit Raise action fires.
Init ==
    pump = [conditions |-> [t \in AlarmTypes |-> FALSE]]

\* ---------- Pump channel actions ----------
PumpGoReachable ==
    /\ Channel!goReachable(PumpId)
    /\ UNCHANGED pump

PumpGoUnreachable ==
    /\ Channel!goUnreachable(PumpId)
    /\ UNCHANGED pump

\* Raises condition `type`: guarded on it not already being active (a real pump does not
\* re-announce a condition it already reported and never cleared -- re-raising an
\* ALREADY-active condition is out of scope for this first cut, flagged not solved, same
\* as this project's other documented duplicate/replay caveats). Local truth flips AND the
\* announcement is published in the SAME atomic step -- see header.
PumpRaiseCondition(type) ==
    /\ type \in AlarmTypes
    /\ ~pump.conditions[type]
    /\ Channel!publish(PumpId, ConditionTopic, [kind |-> "CONDITION", type |-> type, event |-> "RAISED"])
    /\ pump' = [pump EXCEPT !.conditions[type] = TRUE]

\* Clears condition `type`: guarded on it currently being active.
PumpClearCondition(type) ==
    /\ type \in AlarmTypes
    /\ pump.conditions[type]
    /\ Channel!publish(PumpId, ConditionTopic, [kind |-> "CONDITION", type |-> type, event |-> "CLEARED"])
    /\ pump' = [pump EXCEPT !.conditions[type] = FALSE]

\* ---------- Pump Next (standalone, for parse/reachability use only -- BaseSpec_
\* AlarmManager.tla defines its own composed Next from named proxy actions, same
\* convention as 2_models/InfusionPumpRack/Component_Pump.tla) ----------
Next ==
    \/ PumpGoReachable
    \/ PumpGoUnreachable
    \/ \E type \in AlarmTypes : PumpRaiseCondition(type)
    \/ \E type \in AlarmTypes : PumpClearCondition(type)

TypeOK ==
    pump.conditions \in [AlarmTypes -> BOOLEAN]

====
