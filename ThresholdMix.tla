---------------------------- MODULE ThresholdMix ----------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS pool_size, threshold, msgs_pool_size

(* --algorithm ThresholdMix

variables recieved_msgs, sent_msgs, msgs_in_buffer, messages = 1..msgs_pool_size, buffer_lock;

define 
    LEN(s) == Cardinality(S)
end define

macro add_to_set(base_set, new_value)  begin

end macro

macro forward_msgs_to_reciever() begin
    lock_mix_buffer();
    add_to_set(sent_msgs, msg);
    unlock_mix_buffer();
end macro

macro forward_msg_to_mix(msg) begin
    lock_mix_buffer();
    add_to_set(msgs_in_buffer, msg);
    unlock_mix_buffer();
end macro

macro lock_mix_buffer() begin
end macro

macro unlock_mix_buffer() begin
end macro

process mix_msg_forwarder = 0
begin FORWARD:
        while TRUE do
            if LEN(msgs_in_buffer) = threshold then
                forward_msgs_to_reciever();
            end if;
        end while;
end process;

process send_messages = 1 \* only one client for now
variables i = 0;
begin CLIENT:
    while sent_msgs < LEN(messages) do
        forward_msg_to_mix(messages.i);
        i := i + 1;
    end while
end process

end algorithm; *)


=============================================================================
\* Modification History
\* Last modified Mon Apr 27 14:34:42 CDT 2020 by shiva
\* Created Sun Apr 26 20:17:15 CDT 2020 by shiva
