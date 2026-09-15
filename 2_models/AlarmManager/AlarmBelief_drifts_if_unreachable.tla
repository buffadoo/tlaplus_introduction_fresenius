---- MODULE AlarmBelief_drifts_if_unreachable ----
\* Full-space spec (README "Trace / scenario specs" pattern, "full-space" variant, same
\* shape as 2_models/MQTT/QoS0_holds.tla / RackStartStop_desync.tla): no restricted
\* TraceNext -- runs BaseSpec_AlarmManager's own unrestricted Next. DISPROVE scenario,
\* same shape as RackStartStop_desync.tla: states a naive expectation ("once nothing is
\* in flight to the Alarm Manager, its belief matches ground truth") and lets TLC find the
\* counterexample that shows it does NOT hold unconditionally.
\*
\* WHAT TLC FINDS (verified, see scenarios.yaml's own entry for the concrete trace):
\* Pump1 goes reachable, raises OCCLUSION -- but the Alarm Manager itself was NEVER made
\* reachable first. Infrastructure_Channel.tla's own `publish` only fans a message into
\* CURRENTLY-reachable recipients' dispatching queues (see that module's header: "a
\* currently-UNREACHABLE subscriber... simply does not receive this publish at all -- no
\* queued-for-later semantics"). The Alarm Manager's own dispatching queue and inbox are
\* therefore BOTH empty -- "settled" by this file's own definition -- while its belief
\* still says FALSE and the real pump condition is TRUE. Belief does not merely lag; it
\* has PERMANENTLY missed this condition report, with no mechanism in this model to ever
\* recover it (no retained-message equivalent, no periodic full-state resync).
\*
\* NOT a defect in Infrastructure_Channel.tla's delivery semantics -- same "architectural,
\* not a bug" framing as RackStartStop_desync.tla's own caveat: the channel honored every
\* hop it actually owned. The gap is that this app, as modeled, has no mechanism for a
\* SUBSCRIBER (the Alarm Manager) to catch up on what it missed while unreachable -- no
\* retained-message-style "tell me current state on (re)connect" primitive exists on this
\* base (Infrastructure_Channel.tla's header explicitly notes this domain never exercises
\* RETAIN). For a safety-relevant centralized alarm view, permanently missing a condition
\* because the Alarm Manager itself had a connectivity blip is a genuine, concrete
\* architectural question this scenario exists to surface -- see the sibling scenario
\* AlarmBelief_agrees_when_reachable_and_settled.tla for the narrower claim that DOES hold
\* (state agreement, GIVEN the Alarm Manager stays continuously reachable).
EXTENDS BaseSpec_AlarmManager

TrueCondition(source, type) == CASE source = "Pump1" -> pump1.conditions[type]
                                 [] source = "Pump2" -> pump2.conditions[type]

TrueBelief == [s \in {"Pump1", "Pump2"} |-> [t \in AlarmTypes |-> TrueCondition(s, t)]]

AlarmManagerSettled ==
    /\ ChannelInfra!GetDispatching("AlarmManager") = <<>>
    /\ ChannelInfra!GetInbox("AlarmManager") = <<>>

\* Deliberately-false invariant (DISPROVE shape) -- see header.
AlarmManagerBeliefAgreesWhenSettled ==
    AlarmManagerSettled => (alarmManager.belief = TrueBelief)

====
