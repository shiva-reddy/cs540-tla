---------------------------- MODULE ThresholdMix ----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS threshold, messages

(* --algorithm ThresholdMix

variables recieved_msgs = <<>>,
msgs_in_buffer = <<>>, 
buffer_lock = "",
i = 1,
stop_listening = FALSE;
check = 1;

macro forward_msgs_to_recipient() begin
    recieved_msgs := recieved_msgs \o msgs_in_buffer
    ||
    msgs_in_buffer := <<>>
end macro;

fair process mix_msg_forwarder = "mix"
begin MIX_PROCESS_INIT:
        while stop_listening = FALSE do
            if buffer_lock # "mix" then
                MIX_LOCK: await (buffer_lock = "");
                buffer_lock := "mix";
             end if;
            
            FORWARD_TO_RECIPIENT_CHECK:
            if Len(msgs_in_buffer) >= threshold then
                forward_msgs_to_recipient();
            end if;
            if i = Len(messages) + 1 then
                stop_listening := TRUE
            end if;
            MIX_UNLOCK: buffer_lock := "";
        end while;
end process;

fair process send_messages = "client"
begin CLIENT:
    while i <= Len(messages) do
        if buffer_lock # "client" then
            CLIENT_LOCK: await (buffer_lock = "");
            await Len(msgs_in_buffer) < threshold;
            buffer_lock := "client";
        end if;
            
        FORWARD_TO_MIX: 
        msgs_in_buffer := msgs_in_buffer \o <<messages[i]>>
        ||
        i := i + 1;
        CLIENT_UNLOCK: buffer_lock := "";
    end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES recieved_msgs, msgs_in_buffer, buffer_lock, i, stop_listening, 
          check, pc

vars == << recieved_msgs, msgs_in_buffer, buffer_lock, i, stop_listening, 
           check, pc >>

ProcSet == {"mix"} \cup {"client"}

Init == (* Global variables *)
        /\ recieved_msgs = <<>>
        /\ msgs_in_buffer = <<>>
        /\ buffer_lock = ""
        /\ i = 1
        /\ stop_listening = FALSE
        /\ check = 1
        /\ pc = [self \in ProcSet |-> CASE self = "mix" -> "MIX_PROCESS_INIT"
                                        [] self = "client" -> "CLIENT"]

MIX_PROCESS_INIT == /\ pc["mix"] = "MIX_PROCESS_INIT"
                    /\ IF stop_listening = FALSE
                          THEN /\ IF buffer_lock # "mix"
                                     THEN /\ pc' = [pc EXCEPT !["mix"] = "MIX_LOCK"]
                                     ELSE /\ pc' = [pc EXCEPT !["mix"] = "FORWARD_TO_RECIPIENT_CHECK"]
                          ELSE /\ pc' = [pc EXCEPT !["mix"] = "Done"]
                    /\ UNCHANGED << recieved_msgs, msgs_in_buffer, buffer_lock, 
                                    i, stop_listening, check >>

FORWARD_TO_RECIPIENT_CHECK == /\ pc["mix"] = "FORWARD_TO_RECIPIENT_CHECK"
                              /\ IF Len(msgs_in_buffer) >= threshold
                                    THEN /\ /\ msgs_in_buffer' = <<>>
                                            /\ recieved_msgs' = recieved_msgs \o msgs_in_buffer
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << recieved_msgs, 
                                                         msgs_in_buffer >>
                              /\ IF i = Len(messages) + 1
                                    THEN /\ stop_listening' = TRUE
                                    ELSE /\ TRUE
                                         /\ UNCHANGED stop_listening
                              /\ pc' = [pc EXCEPT !["mix"] = "MIX_UNLOCK"]
                              /\ UNCHANGED << buffer_lock, i, check >>

MIX_UNLOCK == /\ pc["mix"] = "MIX_UNLOCK"
              /\ buffer_lock' = ""
              /\ pc' = [pc EXCEPT !["mix"] = "MIX_PROCESS_INIT"]
              /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, stop_listening, 
                              check >>

MIX_LOCK == /\ pc["mix"] = "MIX_LOCK"
            /\ (buffer_lock = "")
            /\ buffer_lock' = "mix"
            /\ pc' = [pc EXCEPT !["mix"] = "FORWARD_TO_RECIPIENT_CHECK"]
            /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, stop_listening, 
                            check >>

mix_msg_forwarder == MIX_PROCESS_INIT \/ FORWARD_TO_RECIPIENT_CHECK
                        \/ MIX_UNLOCK \/ MIX_LOCK

CLIENT == /\ pc["client"] = "CLIENT"
          /\ IF i <= Len(messages)
                THEN /\ IF buffer_lock # "client"
                           THEN /\ pc' = [pc EXCEPT !["client"] = "CLIENT_LOCK"]
                           ELSE /\ pc' = [pc EXCEPT !["client"] = "FORWARD_TO_MIX"]
                ELSE /\ pc' = [pc EXCEPT !["client"] = "Done"]
          /\ UNCHANGED << recieved_msgs, msgs_in_buffer, buffer_lock, i, 
                          stop_listening, check >>

FORWARD_TO_MIX == /\ pc["client"] = "FORWARD_TO_MIX"
                  /\ /\ i' = i + 1
                     /\ msgs_in_buffer' = msgs_in_buffer \o <<messages[i]>>
                  /\ pc' = [pc EXCEPT !["client"] = "CLIENT_UNLOCK"]
                  /\ UNCHANGED << recieved_msgs, buffer_lock, stop_listening, 
                                  check >>

CLIENT_UNLOCK == /\ pc["client"] = "CLIENT_UNLOCK"
                 /\ buffer_lock' = ""
                 /\ pc' = [pc EXCEPT !["client"] = "CLIENT"]
                 /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, 
                                 stop_listening, check >>

CLIENT_LOCK == /\ pc["client"] = "CLIENT_LOCK"
               /\ (buffer_lock = "")
               /\ Len(msgs_in_buffer) < threshold
               /\ buffer_lock' = "client"
               /\ pc' = [pc EXCEPT !["client"] = "FORWARD_TO_MIX"]
               /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, 
                               stop_listening, check >>

send_messages == CLIENT \/ FORWARD_TO_MIX \/ CLIENT_UNLOCK \/ CLIENT_LOCK

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == mix_msg_forwarder \/ send_messages
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(mix_msg_forwarder)
        /\ WF_vars(send_messages)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
\*
NoBufferOverflows == Len(msgs_in_buffer) <= threshold
IsDivisible == Len(messages) % threshold = 0
AllMessagesRecieved == IsDivisible /\ stop_listening ~> (Len(recieved_msgs) = Len(messages))
NoMessageDuplication == Len(recieved_msgs) + Len(msgs_in_buffer) = i - 1
=============================================================================
\* Modification History
\* Last modified Fri May 01 14:31:57 CDT 2020 by shiva
\* Created Sun Apr 26 20:17:15 CDT 2020 by shiva
