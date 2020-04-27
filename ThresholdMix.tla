---------------------------- MODULE ThresholdMix ----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS pool_size, threshold, no_of_msgs

(* --algorithm ThresholdMix

variables recieved_msgs, sent_msgs, msgs_in_buffer, messages = 1..no_of_msgs, buffer_lock = FALSE;

define 
    LEN(s) == Cardinality(s) \* Added operator for convinience
    APPEND(base, newValue) == base \o newValue
end define

macro unlock_mix_buffer() begin
    buffer_lock := FALSE;
end macro

macro lock_mix_buffer() begin
    await buffer_lock = FALSE;
    buffer_lock := TRUE;
end macro;

macro forward_msgs_to_reciever() begin
    sent_msgs := APPEND(sent_msgs, sent_msgs);
end macro;

macro forward_msg_to_mix(msg) begin
    msgs_in_buffer := APPEND(msgs_in_buffer, msg);
end macro;

process mix_msg_forwarder = 0
begin FORWARD:
        while TRUE do
            if LEN(msgs_in_buffer) = threshold then
                LOCK: lock_mix_buffer();
                forward_msgs_to_reciever();
                UNLOCK: unlock_mix_buffer();
            end if;
        end while;
end process;

process send_messages = 1 \* only one client for now
variables i = 0;
begin CLIENT:
    while sent_msgs < LEN(messages) do
        LOCK: lock_mix_buffer();
        forward_msg_to_mix(messages.i);
        UNLOCK: unlock_mix_buffer();
        i := i + 1;
    end while
end process

end algorithm; *)
\* BEGIN TRANSLATION
\* Label LOCK of process mix_msg_forwarder at line 20 col 5 changed to LOCK_
\* Label UNLOCK of process mix_msg_forwarder at line 16 col 5 changed to UNLOCK_
CONSTANT defaultInitValue
VARIABLES recieved_msgs, sent_msgs, msgs_in_buffer, messages, buffer_lock, pc

(* define statement *)
LEN(s) == Cardinality(s)
APPEND(base, newValue) == base \o newValue

VARIABLE i

vars == << recieved_msgs, sent_msgs, msgs_in_buffer, messages, buffer_lock, 
           pc, i >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ recieved_msgs = defaultInitValue
        /\ sent_msgs = defaultInitValue
        /\ msgs_in_buffer = defaultInitValue
        /\ messages = 1..no_of_msgs
        /\ buffer_lock = FALSE
        (* Process send_messages *)
        /\ i = 0
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "FORWARD"
                                        [] self = 1 -> "CLIENT"]

FORWARD == /\ pc[0] = "FORWARD"
           /\ IF LEN(msgs_in_buffer) = threshold
                 THEN /\ pc' = [pc EXCEPT ![0] = "LOCK_"]
                 ELSE /\ pc' = [pc EXCEPT ![0] = "FORWARD"]
           /\ UNCHANGED << recieved_msgs, sent_msgs, msgs_in_buffer, messages, 
                           buffer_lock, i >>

LOCK_ == /\ pc[0] = "LOCK_"
         /\ buffer_lock = FALSE
         /\ buffer_lock' = TRUE
         /\ sent_msgs' = APPEND(sent_msgs, sent_msgs)
         /\ pc' = [pc EXCEPT ![0] = "UNLOCK_"]
         /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, i >>

UNLOCK_ == /\ pc[0] = "UNLOCK_"
           /\ buffer_lock' = FALSE
           /\ pc' = [pc EXCEPT ![0] = "FORWARD"]
           /\ UNCHANGED << recieved_msgs, sent_msgs, msgs_in_buffer, messages, 
                           i >>

mix_msg_forwarder == FORWARD \/ LOCK_ \/ UNLOCK_

CLIENT == /\ pc[1] = "CLIENT"
          /\ IF sent_msgs < LEN(messages)
                THEN /\ pc' = [pc EXCEPT ![1] = "LOCK"]
                ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
          /\ UNCHANGED << recieved_msgs, sent_msgs, msgs_in_buffer, messages, 
                          buffer_lock, i >>

LOCK == /\ pc[1] = "LOCK"
        /\ buffer_lock = FALSE
        /\ buffer_lock' = TRUE
        /\ msgs_in_buffer' = APPEND(msgs_in_buffer, (messages.i))
        /\ pc' = [pc EXCEPT ![1] = "UNLOCK"]
        /\ UNCHANGED << recieved_msgs, sent_msgs, messages, i >>

UNLOCK == /\ pc[1] = "UNLOCK"
          /\ buffer_lock' = FALSE
          /\ i' = i + 1
          /\ pc' = [pc EXCEPT ![1] = "CLIENT"]
          /\ UNCHANGED << recieved_msgs, sent_msgs, msgs_in_buffer, messages >>

send_messages == CLIENT \/ LOCK \/ UNLOCK

Next == mix_msg_forwarder \/ send_messages

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

NoMessageLoss == ((recieved_msgs \UNION sent_msgs) \UNION msgs_in_buffer) = messages
NoMessageDuplication == LEN(recieved_msgs) + LEN(sent_msgs) + LEN(msgs_in_buffer) = no_of_msgs
=============================================================================
\* Modification History
\* Last modified Mon Apr 27 14:58:34 CDT 2020 by shiva
\* Created Sun Apr 26 20:17:15 CDT 2020 by shiva
