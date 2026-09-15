---- MODULE AlarmBelief_agrees_when_reachable_and_settled ----
\* Scenario spec (README "Trace / scenario specs" pattern). PROVE scenario, narrower than
\* the sibling AlarmBelief_drifts_if_unreachable.tla's disprove finding: given the Alarm
\* Manager is reachable from the very start and STAYS reachable for the whole behavior
\* (TraceNext excludes AlarmManagerGoUnreachable entirely, not merely unfair -- same
\* restricted-TraceNext scoping idiom 2_models/InfusionPumpRack/RackStartStop_commit.tla's
\* own header documents: "proves the claim GIVEN uninterrupted reachability for its
\* duration"), belief EXACTLY agrees with ground truth once settled (nothing left in
\* flight to the Alarm Manager) -- no permanent drift, no silent staleness, once the one
\* precondition the sibling scenario shows this domain actually needs is met.
\*
\* TraceInit pins `channel.reachable = {"AlarmManager"}` from State 1 (rather than the
\* base Init's `{}`) specifically so NO publish targeting the Alarm Manager can ever be
\* silently dropped for being unreachable, from the very first step -- pinning reachable
\* AFTER Init (e.g. via a guarded first action) would leave exactly the gap the sibling
\* scenario demonstrates, for however many steps precede that action.
\*
\* SECOND GUARD, discovered empirically while building this scenario (not anticipated up
\* front): reachability alone was NOT enough -- an initial cut of this file, unguarded,
\* still found a violation via a DIFFERENT mechanism. Infrastructure_Channel.tla's own
\* `publish` drops a message when the recipient's dispatching queue is already at
\* MaxQueueDepth ("drop rather than block", same idiom MQTTBroker_v1 itself uses -- see
\* that module's own header), but a Pump's `PumpRaiseCondition`/`PumpClearCondition` flips
\* its OWN local ground truth in the SAME atomic step regardless of whether the publish
\* actually landed in the queue or was silently dropped by capacity. TLC (which explores
\* EVERY interleaving, including ones that never fire AlarmManagerDeliverCondition/
\* AlarmManagerProcessCondition at all) can always find a path that fires enough raises/
\* clears back-to-back to overflow ANY finite MaxQueueDepth before the Alarm Manager ever
\* drains it -- no finite queue bound alone closes this gap; it needs either fairness (a
\* genuine liveness treatment, not attempted here) or, as done below, a pacing guard on
\* the SOURCE side. RoomForAlarmManager below models that: pumps stop announcing new
\* condition changes once the Alarm Manager's own queue has no room left, only resuming
\* once it drains -- a deliberate, scenario-local simplification (real backpressure would
\* need round-trip signaling this simple channel doesn't have) to isolate and prove the
\* claim this scenario is actually about (state agreement once reachable and settled),
\* separately from the queue-capacity finding, which is its own real, separate
\* architectural question for the coaching conversation, not solved here.
EXTENDS BaseSpec_AlarmManager, Sequences

RoomForAlarmManager == Len(ChannelInfra!GetDispatching("AlarmManager")) < MaxQueueDepth

TraceInit ==
    /\ Pump1!Init
    /\ Pump2!Init
    /\ AlarmManager!Init
    /\ channel = [
           dispatching |-> {[client |-> c, queue |-> <<>>] : c \in {"Pump1", "Pump2", "AlarmManager"}},
           inbox       |-> {[client |-> c, queue |-> <<>>] : c \in {"Pump1", "Pump2", "AlarmManager"}},
           reachable   |-> {"AlarmManager"}]

\* Same 16 named proxy actions BaseSpec_AlarmManager.tla's own Next uses, MINUS
\* AlarmManagerGoUnreachable (see header), and with every Pump Raise/Clear action
\* additionally guarded by RoomForAlarmManager (see header's second guard).
TraceNext ==
    \/ Pump1GoReachable
    \/ Pump1GoUnreachable
    \/ (RoomForAlarmManager /\ Pump1RaiseOccl)
    \/ (RoomForAlarmManager /\ Pump1ClearOccl)
    \/ (RoomForAlarmManager /\ Pump1RaiseLowBattery)
    \/ (RoomForAlarmManager /\ Pump1ClearLowBattery)
    \/ Pump2GoReachable
    \/ Pump2GoUnreachable
    \/ (RoomForAlarmManager /\ Pump2RaiseOccl)
    \/ (RoomForAlarmManager /\ Pump2ClearOccl)
    \/ (RoomForAlarmManager /\ Pump2RaiseLowBattery)
    \/ (RoomForAlarmManager /\ Pump2ClearLowBattery)
    \/ AlarmManagerGoReachable
    \/ AlarmManagerDeliverCondition
    \/ AlarmManagerProcessCondition
    \/ AlarmManagerPublishTopPriority

TrueCondition(source, type) == CASE source = "Pump1" -> pump1.conditions[type]
                                 [] source = "Pump2" -> pump2.conditions[type]

TrueBelief == [s \in {"Pump1", "Pump2"} |-> [t \in AlarmTypes |-> TrueCondition(s, t)]]

AlarmManagerSettled ==
    /\ ChannelInfra!GetDispatching("AlarmManager") = <<>>
    /\ ChannelInfra!GetInbox("AlarmManager") = <<>>

\* The claim that DOES hold, given the precondition above -- see header.
AlarmManagerBeliefAgreesWhenSettled ==
    AlarmManagerSettled => (alarmManager.belief = TrueBelief)

====
