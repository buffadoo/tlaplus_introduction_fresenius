---- MODULE 16_AlarmToVSS_NoPersistence ----
\* Capstone: Pump → Combobox → VSS using ABP (spec 15).
\*
\* Setup: Pump detects ALARM (e.g., OCCLUSION) and sends to Combobox.
\* Combobox receives via ABP (perfectly), but can CRASH before forwarding to VSS.
\* VSS never sees the alarm.
\*
\* Teaching: Protocol correctness (ABP) is NOT application correctness.
\* Even though Pump→Combobox delivery is guaranteed exactly-once,
\* Combobox can fail mid-flow. Operator never sees the alert.
\* This is why 60601-1-8 requires END-TO-END handshakes and recovery.

EXTENDS Naturals, Sequences

CONSTANTS MaxLosses

VARIABLES
    \* Pump → Combobox channel (using ABP bit protocol)
    pumpToComboboxCh, pumpBit,
    \* Combobox's internal state
    comboboxAlarmState, comboboxExpectedBit, comboboxCrashed,
    \* Combobox → VSS channel (NO protocol, best-effort)
    comboboxToVSSCh,
    \* VSS's received alarm
    vssReceivedAlarm,
    \* Loss counter
    lossesSoFar

vars == <<pumpToComboboxCh, pumpBit, comboboxAlarmState, comboboxExpectedBit,
           comboboxCrashed, comboboxToVSSCh, vssReceivedAlarm, lossesSoFar>>

Init ==
    /\ pumpToComboboxCh = <<>>
    /\ pumpBit = 0
    /\ comboboxAlarmState = "idle"
    /\ comboboxExpectedBit = 0
    /\ comboboxCrashed = FALSE
    /\ comboboxToVSSCh = <<>>
    /\ vssReceivedAlarm = FALSE
    /\ lossesSoFar = 0

\* Pump sends ALARM to Combobox, tagged with current bit (ABP style).
PumpSendsAlarm ==
    /\ ~comboboxCrashed  \* Can't send if Combobox is already down
    /\ pumpToComboboxCh = <<>>
    /\ pumpToComboboxCh' = <<[alarm |-> "OCCLUSION", bit |-> pumpBit]>>
    /\ UNCHANGED <<pumpBit, comboboxAlarmState, comboboxExpectedBit,
                   comboboxCrashed, comboboxToVSSCh, vssReceivedAlarm, lossesSoFar>>

\* Combobox receives alarm via ABP: only applies if bit matches (proving it's new).
ComboboxReceivesAlarm ==
    /\ ~comboboxCrashed
    /\ pumpToComboboxCh # <<>>
    /\ LET msg == Head(pumpToComboboxCh)
       IN /\ pumpToComboboxCh' = <<>>
          /\ IF msg.bit = comboboxExpectedBit
             THEN \* New alarm: process it
                  /\ comboboxAlarmState' = msg.alarm
                  /\ comboboxExpectedBit' = 1 - comboboxExpectedBit
             ELSE \* Resend of old alarm: ignore it
                  /\ UNCHANGED <<comboboxAlarmState, comboboxExpectedBit>>
    /\ UNCHANGED <<pumpBit, comboboxCrashed, comboboxToVSSCh, vssReceivedAlarm, lossesSoFar>>

\* Combobox forwards received alarm to VSS (only if not crashed and has an alarm to send).
ComboboxForwardsToVSS ==
    /\ ~comboboxCrashed
    /\ comboboxAlarmState # "idle"
    /\ comboboxToVSSCh = <<>>
    /\ comboboxToVSSCh' = <<comboboxAlarmState>>
    /\ comboboxAlarmState' = "idle"  \* Clear after forwarding
    /\ UNCHANGED <<pumpToComboboxCh, pumpBit, comboboxExpectedBit,
                   comboboxCrashed, vssReceivedAlarm, lossesSoFar>>

\* THE CRITICAL FAILURE: Combobox CRASHES while holding the alarm,
\* BEFORE forwarding it to VSS. Operator never sees it.
ComboboxCrashesBeforeForwarding ==
    /\ ~comboboxCrashed
    /\ comboboxAlarmState # "idle"  \* It has an alarm to send but hasn't sent it yet
    /\ comboboxCrashed' = TRUE
    /\ UNCHANGED <<pumpToComboboxCh, pumpBit, comboboxAlarmState,
                   comboboxExpectedBit, comboboxToVSSCh, vssReceivedAlarm, lossesSoFar>>

\* VSS receives the forwarded alarm (simple, no protocol).
VSSSReceivesAlarm ==
    /\ comboboxToVSSCh # <<>>
    /\ vssReceivedAlarm' = TRUE
    /\ comboboxToVSSCh' = <<>>
    /\ UNCHANGED <<pumpToComboboxCh, pumpBit, comboboxAlarmState,
                   comboboxExpectedBit, comboboxCrashed, lossesSoFar>>

\* Message loss on Pump→Combobox channel (bounded).
MessageLostPumpToCombobox ==
    /\ pumpToComboboxCh # <<>>
    /\ lossesSoFar < MaxLosses
    /\ pumpToComboboxCh' = <<>>
    /\ lossesSoFar' = lossesSoFar + 1
    /\ UNCHANGED <<pumpBit, comboboxAlarmState, comboboxExpectedBit,
                   comboboxCrashed, comboboxToVSSCh, vssReceivedAlarm>>

\* Pump advances bit once alarm is fully processed (Combobox received it).
\* This is the ABP acknowledgement: Pump learns "Combobox got it" by seeing
\* the reply implicitly (in a real system, there'd be an ACK channel back).
\* For this model, we simplify: Pump can retry/re-send the alarm if needed.
\* In reality, Pump would receive a bit-ack from Combobox.
\* Here we skip that for simplicity and just let Pump retry with same bit.

Next ==
    \/ PumpSendsAlarm
    \/ ComboboxReceivesAlarm
    \/ ComboboxForwardsToVSS
    \/ ComboboxCrashesBeforeForwarding
    \/ VSSSReceivesAlarm
    \/ MessageLostPumpToCombobox

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(ComboboxReceivesAlarm)
    /\ WF_vars(ComboboxForwardsToVSS)
    /\ WF_vars(VSSSReceivesAlarm)

\* SAFETY: If VSS received the alarm, it means Combobox never crashed.
\* This is trivially true but shows the structure.
IfVSSReceivedThenComboboxSurvived ==
    vssReceivedAlarm => ~comboboxCrashed

\* LIVENESS (deliberately FALSE with crashes):
\* Does the alarm ALWAYS reach the operator?
\* NO -- Combobox can crash and hold the alarm forever.
AlarmReachedOperator == <>(vssReceivedAlarm)

====
