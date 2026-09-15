---- MODULE BaseSpec_AlarmManager ----
\* Alarm Manager app -- pure composition of two Component_Pump condition-source instances
\* and one Component_AlarmManager over the shared Infrastructure_Channel broker, per the
\* project's composition rule (.cursor/rules/mqtt-tla-composition-and-traces.mdc,
\* generalized to this channel primitive): "the base spec only INSTANCEs components and
\* the shared broker, builds the single shared state in Init, and calls each component's
\* Init"; "one disjunction of all proxy actions" for Next, no inline component logic.
\*
\* SCOPE: composition only. No scenario CONSTANTS, no fault injection, no invariants/
\* properties section here -- see the scenario specs in this directory (Smoke_BaseSpec.tla,
\* AlarmPriority_settles_correctly.tla) for what actually gets checked.

EXTENDS Naturals

CONSTANTS
    MaxQueueDepth   \* pass-through to Infrastructure_Channel -- the one genuinely free
                     \* constant in this app, same as the InfusionPumpRack sibling

VARIABLES pump1, pump2, alarmManager, channel

vars == <<pump1, pump2, alarmManager, channel>>

\* Fixed literal -- see Component_Pump.tla/Component_AlarmManager.tla's own headers on
\* why AlarmTypes is not a CONSTANT. Must stay byte-identical to those copies.
AlarmTypes == {"OCCLUSION", "LOW_BATTERY"}

\* Same fixed literal universe as each component's own INSTANCE -- see Component_Pump.tla's
\* header on why these are duplicated by hand rather than shared via a per-app
\* infrastructure wrapper module.
ChannelInfra == INSTANCE Infrastructure_Channel WITH
    channel       <- channel,
    ClientIds     <- {"Pump1", "Pump2", "AlarmManager"},
    TopicNames    <- {"cond/Pump1", "cond/Pump2", "alarm/top"},
    Payloads      <- ([kind: {"CONDITION"}, type: AlarmTypes, event: {"RAISED", "CLEARED"}]
                           \cup [kind: {"TOP_PRIORITY"}, top: AlarmTypes \cup {"NONE"}]),
    MaxQueueDepth <- MaxQueueDepth,
    Subscribers   <- [t \in {"cond/Pump1", "cond/Pump2", "alarm/top"} |->
                          CASE t = "cond/Pump1" -> {"AlarmManager"}
                            [] t = "cond/Pump2" -> {"AlarmManager"}
                            [] t = "alarm/top"  -> {}]

Pump1 == INSTANCE Component_Pump WITH
    PumpId          <- "Pump1",
    ConditionTopic  <- "cond/Pump1",
    pump            <- pump1,
    channel         <- channel,
    MaxQueueDepth   <- MaxQueueDepth

Pump2 == INSTANCE Component_Pump WITH
    PumpId          <- "Pump2",
    ConditionTopic  <- "cond/Pump2",
    pump            <- pump2,
    channel         <- channel,
    MaxQueueDepth   <- MaxQueueDepth

AlarmManager == INSTANCE Component_AlarmManager WITH
    AlarmManagerId  <- "AlarmManager",
    alarmManager    <- alarmManager,
    channel         <- channel,
    MaxQueueDepth   <- MaxQueueDepth

Init ==
    /\ Pump1!Init
    /\ Pump2!Init
    /\ AlarmManager!Init
    /\ ChannelInfra!Init

\* ---------- Named proxy actions ----------
Pump1GoReachable        == Pump1!PumpGoReachable                    /\ UNCHANGED <<pump2, alarmManager>>
Pump1GoUnreachable      == Pump1!PumpGoUnreachable                  /\ UNCHANGED <<pump2, alarmManager>>
Pump1RaiseOccl          == Pump1!PumpRaiseCondition("OCCLUSION")    /\ UNCHANGED <<pump2, alarmManager>>
Pump1ClearOccl          == Pump1!PumpClearCondition("OCCLUSION")    /\ UNCHANGED <<pump2, alarmManager>>
Pump1RaiseLowBattery    == Pump1!PumpRaiseCondition("LOW_BATTERY")  /\ UNCHANGED <<pump2, alarmManager>>
Pump1ClearLowBattery    == Pump1!PumpClearCondition("LOW_BATTERY")  /\ UNCHANGED <<pump2, alarmManager>>

Pump2GoReachable        == Pump2!PumpGoReachable                    /\ UNCHANGED <<pump1, alarmManager>>
Pump2GoUnreachable      == Pump2!PumpGoUnreachable                  /\ UNCHANGED <<pump1, alarmManager>>
Pump2RaiseOccl          == Pump2!PumpRaiseCondition("OCCLUSION")    /\ UNCHANGED <<pump1, alarmManager>>
Pump2ClearOccl          == Pump2!PumpClearCondition("OCCLUSION")    /\ UNCHANGED <<pump1, alarmManager>>
Pump2RaiseLowBattery    == Pump2!PumpRaiseCondition("LOW_BATTERY")  /\ UNCHANGED <<pump1, alarmManager>>
Pump2ClearLowBattery    == Pump2!PumpClearCondition("LOW_BATTERY")  /\ UNCHANGED <<pump1, alarmManager>>

AlarmManagerGoReachable        == AlarmManager!AlarmManagerGoReachable        /\ UNCHANGED <<pump1, pump2>>
AlarmManagerGoUnreachable      == AlarmManager!AlarmManagerGoUnreachable      /\ UNCHANGED <<pump1, pump2>>
AlarmManagerDeliverCondition   == AlarmManager!AlarmManagerDeliverCondition   /\ UNCHANGED <<pump1, pump2>>
AlarmManagerProcessCondition   == AlarmManager!AlarmManagerProcessCondition   /\ UNCHANGED <<pump1, pump2>>
AlarmManagerPublishTopPriority == AlarmManager!AlarmManagerPublishTopPriority /\ UNCHANGED <<pump1, pump2>>

Next ==
    \/ Pump1GoReachable
    \/ Pump1GoUnreachable
    \/ Pump1RaiseOccl
    \/ Pump1ClearOccl
    \/ Pump1RaiseLowBattery
    \/ Pump1ClearLowBattery
    \/ Pump2GoReachable
    \/ Pump2GoUnreachable
    \/ Pump2RaiseOccl
    \/ Pump2ClearOccl
    \/ Pump2RaiseLowBattery
    \/ Pump2ClearLowBattery
    \/ AlarmManagerGoReachable
    \/ AlarmManagerGoUnreachable
    \/ AlarmManagerDeliverCondition
    \/ AlarmManagerProcessCondition
    \/ AlarmManagerPublishTopPriority

Spec == Init /\ [][Next]_vars

====
