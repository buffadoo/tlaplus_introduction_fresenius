---------------------------- MODULE 4_Records ----------------------------
\* Ported from ~/Projects/medtronic_models/1_tla_intro/4_Records.tla -- the
\* one basic (records) not covered by the vending-machine kata's own early
\* files, grouped with the other syntax basics (steps 1-3) rather than
\* later, since it's really just another "here's a type" basic. Worth
\* having early anyway, since Step9 onward (StartPump's messages, and
\* especially the Alternating Bit Protocol's [cmd |-> ..., bit |-> ...]
\* messages) lean on record syntax directly.
\*
\* A parcel moves through a delivery system as a record: id, status,
\* location. Dispatch and Deliver each update only status and location with
\* EXCEPT; id is unchanged. This .cfg checks ShowParcelDelivered so TLC
\* prints Init -> Dispatch -> Deliver as a witness trace.
\*
\* To verify the real rules instead, swap in INVARIANT TypeOK, INVARIANT
\* LocationMatchesStatus, and PROPERTY IdNeverChanges (and remove
\* ShowParcelDelivered).

CONSTANTS ParcelIDs, Locations, HomeLocation

ASSUME
    /\ ParcelIDs # {}
    /\ HomeLocation \in Locations

VARIABLES parcel

Init ==
    parcel = [ id |-> CHOOSE p \in ParcelIDs : TRUE,
               status |-> "pending",
               location |-> HomeLocation ]

Dispatch ==
    /\ parcel.status = "pending"
    /\ parcel' = [ parcel EXCEPT !.status = "dispatched", !.location = "truck" ]

Deliver ==
    /\ parcel.status = "dispatched"
    /\ parcel' = [ parcel EXCEPT !.status = "delivered", !.location = "doorstep" ]

Next ==
    \/ Dispatch
    \/ Deliver

Spec == Init /\ [][Next]_parcel

TypeOK ==
    parcel \in [ id       : ParcelIDs,
                 status   : {"pending", "dispatched", "delivered"},
                 location : Locations ]

LocationMatchesStatus ==
    /\ parcel.status = "pending"    => parcel.location = HomeLocation
    /\ parcel.status = "dispatched" => parcel.location = "truck"
    /\ parcel.status = "delivered"  => parcel.location = "doorstep"

IdNeverChanges ==
    [][parcel.id = parcel'.id]_parcel

\* ---------------------------------------------------------------------------
\* Witness
\* ShowParcelDelivered is FALSE once the parcel has been delivered.
\* ---------------------------------------------------------------------------
ShowParcelDelivered ==
    ~(parcel.status = "delivered")

=============================================================================
