---------------------------- MODULE ThresholdMix ----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS pool_size, threshold, no_of_msgs

(* --algorithm ThresholdMix

variables recieved_msgs = <<>>,
msgs_in_buffer = <<>>, 
messages = <<1,2,3,4,5,6,7,8>>, 
buffer_lock = FALSE,
i = 1,
check = 1;

macro forward_msg_to_mix(msg) begin
    
end macro;

macro forward_msgs_to_recipient() begin
    recieved_msgs := recieved_msgs \o msgs_in_buffer
    ||
    msgs_in_buffer := <<>>
end macro;

procedure lock() begin
  LOCK: await buffer_lock = FALSE;
  buffer_lock := TRUE;
  return;
end procedure;

procedure unlock() begin
  UNLOCK:buffer_lock := FALSE;
  return;
end procedure;

fair process mix_msg_forwarder = "mix"
begin FORWARD:
        while TRUE do
            MIX_LOCK: call lock();
            
            FORWARD_TO_RECIPIENT_CHECK:
            if Len(msgs_in_buffer) = threshold then
                forward_msgs_to_recipient();
            end if;
            check := check + 1;
            MIX_UNLOCK: call unlock();
        end while;
end process;

fair process send_messages = "client"
begin CLIENT:
    while i <= Len(messages) do
        CLIENT_LOCK: call lock();
        FORWARD_TO_MIX: 
        msgs_in_buffer := msgs_in_buffer \o <<messages[i]>>
        ||
        i := i + 1;
        CLIENT_UNLOCK: call unlock();
    end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES recieved_msgs, msgs_in_buffer, messages, buffer_lock, i, check, pc, 
          stack

vars == << recieved_msgs, msgs_in_buffer, messages, buffer_lock, i, check, pc, 
           stack >>

ProcSet == {"mix"} \cup {"client"}

Init == (* Global variables *)
        /\ recieved_msgs = <<>>
        /\ msgs_in_buffer = <<>>
        /\ messages = <<1,2,3,4,5,6,7,8>>
        /\ buffer_lock = FALSE
        /\ i = 1
        /\ check = 1
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "mix" -> "FORWARD"
                                        [] self = "client" -> "CLIENT"]

LOCK(self) == /\ pc[self] = "LOCK"
              /\ buffer_lock = FALSE
              /\ buffer_lock' = TRUE
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, i, 
                              check >>

lock(self) == LOCK(self)

UNLOCK(self) == /\ pc[self] = "UNLOCK"
                /\ buffer_lock' = FALSE
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, i, 
                                check >>

unlock(self) == UNLOCK(self)

FORWARD == /\ pc["mix"] = "FORWARD"
           /\ pc' = [pc EXCEPT !["mix"] = "MIX_LOCK"]
           /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, 
                           buffer_lock, i, check, stack >>

MIX_LOCK == /\ pc["mix"] = "MIX_LOCK"
            /\ stack' = [stack EXCEPT !["mix"] = << [ procedure |->  "lock",
                                                      pc        |->  "FORWARD_TO_RECIPIENT_CHECK" ] >>
                                                  \o stack["mix"]]
            /\ pc' = [pc EXCEPT !["mix"] = "LOCK"]
            /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, 
                            buffer_lock, i, check >>

FORWARD_TO_RECIPIENT_CHECK == /\ pc["mix"] = "FORWARD_TO_RECIPIENT_CHECK"
                              /\ IF Len(msgs_in_buffer) = threshold
                                    THEN /\ /\ msgs_in_buffer' = <<>>
                                            /\ recieved_msgs' = recieved_msgs \o msgs_in_buffer
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << recieved_msgs, 
                                                         msgs_in_buffer >>
                              /\ check' = check + 1
                              /\ pc' = [pc EXCEPT !["mix"] = "MIX_UNLOCK"]
                              /\ UNCHANGED << messages, buffer_lock, i, stack >>

MIX_UNLOCK == /\ pc["mix"] = "MIX_UNLOCK"
              /\ stack' = [stack EXCEPT !["mix"] = << [ procedure |->  "unlock",
                                                        pc        |->  "FORWARD" ] >>
                                                    \o stack["mix"]]
              /\ pc' = [pc EXCEPT !["mix"] = "UNLOCK"]
              /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, 
                              buffer_lock, i, check >>

mix_msg_forwarder == FORWARD \/ MIX_LOCK \/ FORWARD_TO_RECIPIENT_CHECK
                        \/ MIX_UNLOCK

CLIENT == /\ pc["client"] = "CLIENT"
          /\ IF i <= Len(messages)
                THEN /\ pc' = [pc EXCEPT !["client"] = "CLIENT_LOCK"]
                ELSE /\ pc' = [pc EXCEPT !["client"] = "Done"]
          /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, buffer_lock, 
                          i, check, stack >>

CLIENT_LOCK == /\ pc["client"] = "CLIENT_LOCK"
               /\ stack' = [stack EXCEPT !["client"] = << [ procedure |->  "lock",
                                                            pc        |->  "FORWARD_TO_MIX" ] >>
                                                        \o stack["client"]]
               /\ pc' = [pc EXCEPT !["client"] = "LOCK"]
               /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, 
                               buffer_lock, i, check >>

FORWARD_TO_MIX == /\ pc["client"] = "FORWARD_TO_MIX"
                  /\ /\ i' = i + 1
                     /\ msgs_in_buffer' = msgs_in_buffer \o <<messages[i]>>
                  /\ pc' = [pc EXCEPT !["client"] = "CLIENT_UNLOCK"]
                  /\ UNCHANGED << recieved_msgs, messages, buffer_lock, check, 
                                  stack >>

CLIENT_UNLOCK == /\ pc["client"] = "CLIENT_UNLOCK"
                 /\ stack' = [stack EXCEPT !["client"] = << [ procedure |->  "unlock",
                                                              pc        |->  "CLIENT" ] >>
                                                          \o stack["client"]]
                 /\ pc' = [pc EXCEPT !["client"] = "UNLOCK"]
                 /\ UNCHANGED << recieved_msgs, msgs_in_buffer, messages, 
                                 buffer_lock, i, check >>

send_messages == CLIENT \/ CLIENT_LOCK \/ FORWARD_TO_MIX \/ CLIENT_UNLOCK

Next == mix_msg_forwarder \/ send_messages
           \/ (\E self \in ProcSet: lock(self) \/ unlock(self))

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(mix_msg_forwarder)
           /\ WF_vars(lock("mix"))
           /\ WF_vars(unlock("mix"))
        /\ /\ WF_vars(send_messages)
           /\ WF_vars(lock("client"))
           /\ WF_vars(unlock("client"))

\* END TRANSLATION
\*
NoBufferOverflows == Len(msgs_in_buffer) <= threshold
AllMessagesRecieved == <>(Len(recieved_msgs) = 8)
NoMessageDuplication == Len(recieved_msgs) + Len(msgs_in_buffer) = i - 1
=============================================================================
\* Modification History
\* Last modified Fri May 01 11:58:38 CDT 2020 by shiva
\* Created Sun Apr 26 20:17:15 CDT 2020 by shiva
