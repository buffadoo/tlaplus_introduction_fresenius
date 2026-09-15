---- MODULE Infrastructure_Channel ----
\* Minimal abstract pub-sub channel/broker primitive -- same module as
\* 2_models/InfusionPumpRack/Infrastructure_Channel.tla, copied into this app folder per
\* this project's own "no cross-app reuse boundary" convention (see that file's header,
\* and .cursor/rules/mqtt-tla-composition-and-traces.mdc sec 5's MQTTBroker_v1 contrast):
\* this primitive lives IN each app folder that uses it, duplicated by hand, because
\* (unlike MQTTBroker_v1.tla) it is not a cross-app canonical protocol module.
\*
\* THE ONE PROPERTY THAT MUST SURVIVE: independent, asynchronously-timed, PER-RECIPIENT
\* delivery. A publish and its eventual delivery to a given recipient are two separate,
\* separately-timed steps -- never one atomic send-and-receive -- and two different
\* recipients of "the same" logical publish are never delivered to in the same atomic
\* step. This is what makes it possible to represent an Alarm Manager's centralized view
\* as GENUINELY LAGGING BEHIND the real, distributed condition sources, rather than
\* magically always up to date.
\*
\* Single flat state variable `channel`:
\*   dispatching -- set of [client, queue], one record per ClientIds. Not-yet-delivered,
\*                  per-RECIPIENT queue -- written by `publish`'s fan-out, drained one
\*                  message at a time by `deliver`.
\*   inbox       -- set of [client, queue], one record per ClientIds. Delivered-but-not-
\*                  yet-taken queue -- written by `deliver`, drained by `take`.
\*   reachable   -- SUBSET ClientIds. Which participants can currently receive a delivery.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    ClientIds,      \* fixed universe of channel participants (publishers and/or subscribers)
    TopicNames,     \* fixed universe of topics
    Payloads,       \* fixed universe of message payloads (opaque to this module)
    MaxQueueDepth,  \* per-recipient bound shared by both dispatching and inbox queues
    Subscribers     \* [TopicNames -> SUBSET ClientIds] -- fixed, CONSTANT-driven
                    \* topic->subscriber mapping

ASSUME ClientIds # {}
ASSUME Subscribers \in [TopicNames -> SUBSET ClientIds]
ASSUME MaxQueueDepth \in Nat

VARIABLES channel

dispatching == channel.dispatching
inbox       == channel.inbox
reachable   == channel.reachable

Message == [topic: TopicNames, payload: Payloads]

TypeOK ==
    /\ \A m \in dispatching : m.client \in ClientIds /\ m.queue \in Seq(Message)
    /\ \A m1, m2 \in dispatching : m1.client = m2.client => m1 = m2
    /\ \A c \in ClientIds : \E m \in dispatching : m.client = c
    /\ \A m \in inbox : m.client \in ClientIds /\ m.queue \in Seq(Message)
    /\ \A m1, m2 \in inbox : m1.client = m2.client => m1 = m2
    /\ \A c \in ClientIds : \E m \in inbox : m.client = c
    /\ reachable \subseteq ClientIds

HasDispatching(client) == \E m \in dispatching : m.client = client
GetDispatching(client) == (CHOOSE m \in dispatching : m.client = client).queue

HasInbox(client) == \E m \in inbox : m.client = client
GetInbox(client) == (CHOOSE m \in inbox : m.client = client).queue

IsReachable(client) == client \in reachable

Init ==
    channel = [
        dispatching |-> {[client |-> c, queue |-> <<>>] : c \in ClientIds},
        inbox       |-> {[client |-> c, queue |-> <<>>] : c \in ClientIds},
        reachable   |-> {}
    ]

goReachable(client) ==
    /\ client \in ClientIds
    /\ client \notin reachable
    /\ channel' = [channel EXCEPT !.reachable = @ \cup {client}]

goUnreachable(client) ==
    /\ client \in ClientIds
    /\ client \in reachable
    /\ channel' = [channel EXCEPT !.reachable = @ \ {client}]

publish(publisher, topic, payload) ==
    /\ publisher \in ClientIds
    /\ topic \in TopicNames
    /\ payload \in Payloads
    /\ IsReachable(publisher)
    /\ LET recipients == {c \in Subscribers[topic] : IsReachable(c)}
       IN channel' = [channel EXCEPT
              !.dispatching = {
                  IF m.client \in recipients /\ Len(m.queue) < MaxQueueDepth
                  THEN [m EXCEPT !.queue = Append(@, [topic |-> topic, payload |-> payload])]
                  ELSE m
                  : m \in dispatching}]

deliver(client) ==
    /\ client \in ClientIds
    /\ HasDispatching(client)
    /\ GetDispatching(client) # <<>>
    /\ Len(GetInbox(client)) < MaxQueueDepth
    /\ LET msg == Head(GetDispatching(client))
       IN channel' = [channel EXCEPT
              !.dispatching = {IF m.client = client THEN [m EXCEPT !.queue = Tail(@)] ELSE m : m \in dispatching},
              !.inbox       = {IF m.client = client THEN [m EXCEPT !.queue = Append(@, msg)] ELSE m : m \in inbox}]

take(client) ==
    /\ client \in ClientIds
    /\ HasInbox(client)
    /\ GetInbox(client) # <<>>
    /\ channel' = [channel EXCEPT
           !.inbox = {IF m.client = client THEN [m EXCEPT !.queue = Tail(@)] ELSE m : m \in inbox}]

Next ==
    \/ \E c \in ClientIds : goReachable(c)
    \/ \E c \in ClientIds : goUnreachable(c)
    \/ \E p \in ClientIds, t \in TopicNames, pl \in Payloads : publish(p, t, pl)
    \/ \E c \in ClientIds : deliver(c)
    \/ \E c \in ClientIds : take(c)

Spec == Init /\ [][Next]_channel

====
