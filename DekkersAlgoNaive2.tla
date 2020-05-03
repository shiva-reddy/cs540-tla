------------------------- MODULE DekkersAlgoNaive2 -------------------------
(* --algorithm Dekkers

variables thread1 = FALSE, thread2 = FALSE , 
p0CriticalAccess = FALSE, p1CriticalAccess = FALSE;

fair process p0 = 0
begin P0_INIT:
    while TRUE do
        await thread2 # TRUE;
        SET_THREAD1:thread1 := TRUE;
        p0CriticalAccess := TRUE;
        A:p0CriticalAccess := FALSE;
        RELEASE_0: thread1 := FALSE;
    end while;
end process;

fair process p1 = 1
begin P1_INIT:
     while TRUE do
        await thread1 # TRUE;
        SET_THREAD2:thread2 := TRUE;
        p1CriticalAccess := TRUE;
        B:p1CriticalAccess := FALSE;
        RELEASE_1 : thread2 := FALSE;
     end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES thread1, thread2, p0CriticalAccess, p1CriticalAccess, pc

vars == << thread1, thread2, p0CriticalAccess, p1CriticalAccess, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ thread1 = FALSE
        /\ thread2 = FALSE
        /\ p0CriticalAccess = FALSE
        /\ p1CriticalAccess = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P0_INIT"
                                        [] self = 1 -> "P1_INIT"]

P0_INIT == /\ pc[0] = "P0_INIT"
           /\ thread2 # TRUE
           /\ pc' = [pc EXCEPT ![0] = "SET_THREAD1"]
           /\ UNCHANGED << thread1, thread2, p0CriticalAccess, 
                           p1CriticalAccess >>

SET_THREAD1 == /\ pc[0] = "SET_THREAD1"
               /\ thread1' = TRUE
               /\ p0CriticalAccess' = TRUE
               /\ pc' = [pc EXCEPT ![0] = "A"]
               /\ UNCHANGED << thread2, p1CriticalAccess >>

A == /\ pc[0] = "A"
     /\ p0CriticalAccess' = FALSE
     /\ pc' = [pc EXCEPT ![0] = "RELEASE_0"]
     /\ UNCHANGED << thread1, thread2, p1CriticalAccess >>

RELEASE_0 == /\ pc[0] = "RELEASE_0"
             /\ thread1' = FALSE
             /\ pc' = [pc EXCEPT ![0] = "P0_INIT"]
             /\ UNCHANGED << thread2, p0CriticalAccess, p1CriticalAccess >>

p0 == P0_INIT \/ SET_THREAD1 \/ A \/ RELEASE_0

P1_INIT == /\ pc[1] = "P1_INIT"
           /\ thread1 # TRUE
           /\ pc' = [pc EXCEPT ![1] = "SET_THREAD2"]
           /\ UNCHANGED << thread1, thread2, p0CriticalAccess, 
                           p1CriticalAccess >>

SET_THREAD2 == /\ pc[1] = "SET_THREAD2"
               /\ thread2' = TRUE
               /\ p1CriticalAccess' = TRUE
               /\ pc' = [pc EXCEPT ![1] = "B"]
               /\ UNCHANGED << thread1, p0CriticalAccess >>

B == /\ pc[1] = "B"
     /\ p1CriticalAccess' = FALSE
     /\ pc' = [pc EXCEPT ![1] = "RELEASE_1"]
     /\ UNCHANGED << thread1, thread2, p0CriticalAccess >>

RELEASE_1 == /\ pc[1] = "RELEASE_1"
             /\ thread2' = FALSE
             /\ pc' = [pc EXCEPT ![1] = "P1_INIT"]
             /\ UNCHANGED << thread1, p0CriticalAccess, p1CriticalAccess >>

p1 == P1_INIT \/ SET_THREAD2 \/ B \/ RELEASE_1

Next == p0 \/ p1

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(p0)
        /\ WF_vars(p1)

\* END TRANSLATION

CriticalSectionSafety == (p0CriticalAccess /\ p1CriticalAccess) = FALSE
=============================================================================
\* Modification History
\* Last modified Sun May 03 15:23:44 CDT 2020 by shiva
\* Created Sun May 03 13:21:24 CDT 2020 by shiva
