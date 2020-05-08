---------------------------- MODULE ThresholdMix ----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS threshold, messages

(* --algorithm ThresholdMix

variables recieved_msgs = <<>>,
msgs_in_buffer = <<>>, 
wants_to_enter = <<FALSE, FALSE>>,
i = 1,
turn = 1;

fair process mix_msg_forwarder = "mix"
begin MIX_PROCESS_INIT:
        while TRUE do
        
            P01:wants_to_enter[1] := TRUE;
            p0While: while wants_to_enter[2] do
            P02:if turn = 2 then
                P03:wants_to_enter[1] := FALSE;
                P04:await turn # 2;
                P05:wants_to_enter[1] := TRUE;
                end if;
            end while;
            
            csm: skip;
            FORWARD_TO_RECIPIENT_CHECK:
            if Len(msgs_in_buffer) >= threshold then
                M3:recieved_msgs := recieved_msgs \o msgs_in_buffer;
                msgs_in_buffer := <<>>;
            end if;
            
            P08: turn := 2;
            P09: wants_to_enter[1] := FALSE;
        end while;
end process;

fair process send_messages = "client"
begin CLIENT:
    while i <= Len(messages) do
    
        P11:wants_to_enter[2] := TRUE;
        p1While: while wants_to_enter[1] do
            P12:if turn = 1 then
                P13:wants_to_enter[2] := FALSE;
                P14:await turn # 1;
                P15:wants_to_enter[2] := TRUE;
            end if;
        end while;
        
        csc: skip;
        FORWARD_TO_MIX: 
        msgs_in_buffer := msgs_in_buffer \o <<messages[i]>>;
        i := i + 1;
        
        P18:turn := 1;
        P19:wants_to_enter[2] := FALSE;
    end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn, pc

vars == << recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn, pc >>

ProcSet == {"mix"} \cup {"client"}

Init == (* Global variables *)
        /\ recieved_msgs = <<>>
        /\ msgs_in_buffer = <<>>
        /\ wants_to_enter = <<FALSE, FALSE>>
        /\ i = 1
        /\ turn = 1
        /\ pc = [self \in ProcSet |-> CASE self = "mix" -> "MIX_PROCESS_INIT"
                                        [] self = "client" -> "CLIENT"]

MIX_PROCESS_INIT == /\ pc["mix"] = "MIX_PROCESS_INIT"
                    /\ pc' = [pc EXCEPT !["mix"] = "P01"]
                    /\ UNCHANGED << recieved_msgs, msgs_in_buffer, 
                                    wants_to_enter, i, turn >>

P01 == /\ pc["mix"] = "P01"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
       /\ pc' = [pc EXCEPT !["mix"] = "p0While"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

p0While == /\ pc["mix"] = "p0While"
           /\ IF wants_to_enter[2]
                 THEN /\ pc' = [pc EXCEPT !["mix"] = "P02"]
                 ELSE /\ pc' = [pc EXCEPT !["mix"] = "csm"]
           /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, 
                           turn >>

P02 == /\ pc["mix"] = "P02"
       /\ IF turn = 2
             THEN /\ pc' = [pc EXCEPT !["mix"] = "P03"]
             ELSE /\ pc' = [pc EXCEPT !["mix"] = "p0While"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn >>

P03 == /\ pc["mix"] = "P03"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT !["mix"] = "P04"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

P04 == /\ pc["mix"] = "P04"
       /\ turn # 2
       /\ pc' = [pc EXCEPT !["mix"] = "P05"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn >>

P05 == /\ pc["mix"] = "P05"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
       /\ pc' = [pc EXCEPT !["mix"] = "p0While"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

csm == /\ pc["mix"] = "csm"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["mix"] = "FORWARD_TO_RECIPIENT_CHECK"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn >>

FORWARD_TO_RECIPIENT_CHECK == /\ pc["mix"] = "FORWARD_TO_RECIPIENT_CHECK"
                              /\ IF Len(msgs_in_buffer) >= threshold
                                    THEN /\ pc' = [pc EXCEPT !["mix"] = "M3"]
                                    ELSE /\ pc' = [pc EXCEPT !["mix"] = "P08"]
                              /\ UNCHANGED << recieved_msgs, msgs_in_buffer, 
                                              wants_to_enter, i, turn >>

M3 == /\ pc["mix"] = "M3"
      /\ recieved_msgs' = recieved_msgs \o msgs_in_buffer
      /\ msgs_in_buffer' = <<>>
      /\ pc' = [pc EXCEPT !["mix"] = "P08"]
      /\ UNCHANGED << wants_to_enter, i, turn >>

P08 == /\ pc["mix"] = "P08"
       /\ turn' = 2
       /\ pc' = [pc EXCEPT !["mix"] = "P09"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i >>

P09 == /\ pc["mix"] = "P09"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT !["mix"] = "MIX_PROCESS_INIT"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

mix_msg_forwarder == MIX_PROCESS_INIT \/ P01 \/ p0While \/ P02 \/ P03
                        \/ P04 \/ P05 \/ csm \/ FORWARD_TO_RECIPIENT_CHECK
                        \/ M3 \/ P08 \/ P09

CLIENT == /\ pc["client"] = "CLIENT"
          /\ IF i <= Len(messages)
                THEN /\ pc' = [pc EXCEPT !["client"] = "P11"]
                ELSE /\ pc' = [pc EXCEPT !["client"] = "Done"]
          /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, 
                          turn >>

P11 == /\ pc["client"] = "P11"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
       /\ pc' = [pc EXCEPT !["client"] = "p1While"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

p1While == /\ pc["client"] = "p1While"
           /\ IF wants_to_enter[1]
                 THEN /\ pc' = [pc EXCEPT !["client"] = "P12"]
                 ELSE /\ pc' = [pc EXCEPT !["client"] = "csc"]
           /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, 
                           turn >>

P12 == /\ pc["client"] = "P12"
       /\ IF turn = 1
             THEN /\ pc' = [pc EXCEPT !["client"] = "P13"]
             ELSE /\ pc' = [pc EXCEPT !["client"] = "p1While"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn >>

P13 == /\ pc["client"] = "P13"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
       /\ pc' = [pc EXCEPT !["client"] = "P14"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

P14 == /\ pc["client"] = "P14"
       /\ turn # 1
       /\ pc' = [pc EXCEPT !["client"] = "P15"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn >>

P15 == /\ pc["client"] = "P15"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
       /\ pc' = [pc EXCEPT !["client"] = "p1While"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

csc == /\ pc["client"] = "csc"
       /\ TRUE
       /\ pc' = [pc EXCEPT !["client"] = "FORWARD_TO_MIX"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i, turn >>

FORWARD_TO_MIX == /\ pc["client"] = "FORWARD_TO_MIX"
                  /\ msgs_in_buffer' = msgs_in_buffer \o <<messages[i]>>
                  /\ i' = i + 1
                  /\ pc' = [pc EXCEPT !["client"] = "P18"]
                  /\ UNCHANGED << recieved_msgs, wants_to_enter, turn >>

P18 == /\ pc["client"] = "P18"
       /\ turn' = 1
       /\ pc' = [pc EXCEPT !["client"] = "P19"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, wants_to_enter, i >>

P19 == /\ pc["client"] = "P19"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
       /\ pc' = [pc EXCEPT !["client"] = "CLIENT"]
       /\ UNCHANGED << recieved_msgs, msgs_in_buffer, i, turn >>

send_messages == CLIENT \/ P11 \/ p1While \/ P12 \/ P13 \/ P14 \/ P15
                    \/ csc \/ FORWARD_TO_MIX \/ P18 \/ P19

Next == mix_msg_forwarder \/ send_messages

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(mix_msg_forwarder)
        /\ WF_vars(send_messages)

\* END TRANSLATION
\*
(*     PlusCal options (wf)                                                *)
NoBufferOverflows == Len(msgs_in_buffer) <= threshold
IsDivisible == Len(messages) % threshold = 0
AllMessagesRecieved == IsDivisible ~> (Len(recieved_msgs) = Len(messages))
MutualExlusion == ~((pc["mix"] = "csm") /\ (pc["client"] = "csc"))
NoMessageDuplication == Len(recieved_msgs) + Len(msgs_in_buffer) = i - 1
=============================================================================
\* Modification History
\* Last modified Tue May 05 19:23:34 CDT 2020 by shiva
\* Created Sun Apr 26 20:17:15 CDT 2020 by shiva
