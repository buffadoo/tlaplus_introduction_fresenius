---- MODULE Component_AlarmManager ----
\* The Alarm Manager: a centralized subscriber over an otherwise-distributed set of
\* condition sources (here, two pumps). Scope of THIS first model -- deliberately narrow,
\* per the parent design conversation: only "handling alarm conditions reported by other
\* services", "deciding the current top-priority alarm", and "publishing alarm state
\* changes" (here, over this app's own Infrastructure_Channel, not dBus). NOT modeled yet,
\* on purpose (flagged, not silently dropped): the latched/muted lifecycle states, alarm
\* configuration/priority-override rules (Priority below is a fixed literal, not
\* runtime-configurable), and EventLog generation. A future yak can extend this component;
\* this one proves out the two hardest architectural questions first -- centralized state
\* built from distributed, independently-timed reports, and priority arbitration across
\* sources -- before adding lifecycle complexity on top.
\*
\* BELIEF IS A REMOTE COPY, NOT GROUND TRUTH: `alarmManager.belief[source][type]` is this
\* component's own view of whether `source` currently has `type` active -- built ENTIRELY
\* from condition-report messages it has actually received and processed (Channel!take),
\* never by reading a pump's own `pump.conditions` directly (would violate the "components
\* communicate only through the channel" rule, see Component_Pump.tla's header). This
\* belief can and does lag behind the real, distributed truth -- that gap is the whole
\* point of modeling this centrally at all: see the scenario specs in this directory for
\* what TLC can and cannot promise about how far it can lag.
\*
\* PRIORITY ARBITRATION: `Priority` (a fixed, injective [AlarmTypes -> Nat] literal, see
\* ASSUME below -- not a CONSTANT, same "fixed domain vocabulary" reasoning as
\* Component_Pump.tla's own AlarmTypes literal) totally orders AlarmTypes; ties are out
\* of scope for this first cut (flagged, not solved -- a future yak modeling two
\* conditions of genuinely EQUAL priority needs an explicit tie-break rule, which this
\* model does not attempt). CurrentTopPriority computes, from `belief` alone, the
\* highest-priority condition currently believed active across every source, or the
\* NoAlarm sentinel if none is.
\*
\* Per the composition rule: every action here reads/writes only `alarmManager` and
\* `channel` -- never a pump's own `pump` variable, even indirectly.

EXTENDS Naturals, Sequences

CONSTANTS
    MaxQueueDepth,   \* pass-through to Infrastructure_Channel
    AlarmManagerId   \* this component's own channel ClientId -- fixed "AlarmManager"

ASSUME AlarmManagerId = "AlarmManager"

\* Fixed literals -- see header on why these are not CONSTANTS. Must stay byte-identical
\* to Component_Pump.tla's own copy of AlarmTypes.
AlarmTypes == {"OCCLUSION", "LOW_BATTERY"}
Sources    == {"Pump1", "Pump2"}

\* Higher number = more urgent. Injective (no ties) -- see header.
Priority == [t \in AlarmTypes |-> CASE t = "OCCLUSION"   -> 2
                                     [] t = "LOW_BATTERY" -> 1]

ASSUME \A t1, t2 \in AlarmTypes : (t1 # t2) => (Priority[t1] # Priority[t2])  \* no ties, see header

NoAlarm == "NONE"
ASSUME NoAlarm \notin AlarmTypes

VARIABLES alarmManager, channel

\* Same fixed literal universe as Component_Pump.tla's own INSTANCE -- see that file's
\* header on why these stay byte-identical across every site sharing this `channel`.
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

\* Which source owns a given condition topic -- the topic itself IS the source's identity
\* here, same "topic as identity" idiom 2_models/InfusionPumpRack/Component_RackController.tla
\* already uses for its own per-pump ack topics.
SourceOf(topic) == CASE topic = "cond/Pump1" -> "Pump1"
                     [] topic = "cond/Pump2" -> "Pump2"

\* The highest-priority condition currently believed active across every source, or
\* NoAlarm if none is believed active. Pure function of `belief` alone -- see header.
CurrentTopPriority(belief) ==
    LET Actives == {r \in [source: Sources, type: AlarmTypes] : belief[r.source][r.type]}
    IN IF Actives = {}
       THEN NoAlarm
       ELSE (CHOOSE r \in Actives : \A r2 \in Actives : Priority[r.type] >= Priority[r2.type]).type

\* Starts believing every source has every condition clear (matches every pump's own
\* Init), and has never published a top-priority announcement yet.
Init ==
    alarmManager = [
        belief        |-> [s \in Sources |-> [t \in AlarmTypes |-> FALSE]],
        lastPublished |-> NoAlarm
    ]

\* ---------- AlarmManager channel actions ----------
AlarmManagerGoReachable ==
    /\ Channel!goReachable(AlarmManagerId)
    /\ UNCHANGED alarmManager

AlarmManagerGoUnreachable ==
    /\ Channel!goUnreachable(AlarmManagerId)
    /\ UNCHANGED alarmManager

\* Broker -> AlarmManager wire hop for a matched condition report -- the one, load-
\* bearing, independently-timed per-recipient step that makes this component's belief a
\* genuinely separate, lagging copy of the real per-pump ground truth (see header).
AlarmManagerDeliverCondition ==
    /\ Channel!deliver(AlarmManagerId)
    /\ UNCHANGED alarmManager

\* The one action where this component's own local state actually changes: applies a
\* delivered condition report's RAISED/CLEARED semantics to `belief[source][type]` and, in
\* the SAME atomic step, consumes it off this component's own inbox (Channel!take) -- same
\* "the message crossing the wire IS the whole hand-off" idiom Component_Pump.tla and its
\* InfusionPumpRack sibling both already use.
AlarmManagerProcessCondition ==
    /\ Channel!HasInbox(AlarmManagerId)
    /\ Channel!GetInbox(AlarmManagerId) # <<>>
    /\ LET msg    == Head(Channel!GetInbox(AlarmManagerId))
           source == SourceOf(msg.topic)
       IN /\ alarmManager' = [alarmManager EXCEPT
                !.belief[source][msg.payload.type] = (msg.payload.event = "RAISED")]
          /\ Channel!take(AlarmManagerId)

\* Publishes a top-priority announcement only when CurrentTopPriority(belief) actually
\* differs from the last one announced -- avoids re-announcing "nothing changed" on every
\* possible firing, same "owed-ness gates the publish" shape Component_Pump.tla's own
\* PumpPublishAck (InfusionPumpRack sibling) uses for pendingAck.
AlarmManagerPublishTopPriority ==
    /\ LET top == CurrentTopPriority(alarmManager.belief)
       IN /\ top # alarmManager.lastPublished
          /\ Channel!publish(AlarmManagerId, "alarm/top", [kind |-> "TOP_PRIORITY", top |-> top])
          /\ alarmManager' = [alarmManager EXCEPT !.lastPublished = top]

\* ---------- AlarmManager Next (standalone, for parse/reachability use only) ----------
Next ==
    \/ AlarmManagerGoReachable
    \/ AlarmManagerGoUnreachable
    \/ AlarmManagerDeliverCondition
    \/ AlarmManagerProcessCondition
    \/ AlarmManagerPublishTopPriority

TypeOK ==
    /\ alarmManager.belief \in [Sources -> [AlarmTypes -> BOOLEAN]]
    /\ alarmManager.lastPublished \in AlarmTypes \cup {NoAlarm}

====
