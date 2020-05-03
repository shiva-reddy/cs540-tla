-------------------------- MODULE DekkersAlgoNaive --------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS p0_max, p1_max
(* --algorithm Dekkers

variables threadNumber = 1,
p0_count = 0, p1_count = 0, 
p1Critical = FALSE, p2Critical = FALSE;

fair process p0 = 0
begin P0_INIT:
    while p0_count < p0_max do
        await threadNumber = 1;
        \*Critical section
        p0_count := p0_count + 1;
        p1Critical := TRUE;
        RELEASE_P0:
        p1Critical := FALSE;
        threadNumber := 2;
     end while;
end process;

fair process p1 = 1
begin P1_INIT:
     while p1_count < p1_max do
        await threadNumber = 2;
        p1_count := p1_count + 1;
        p2Critical := TRUE;
        RELEASE_P1:
        p2Critical := FALSE;
        threadNumber := 1;
     end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES threadNumber, p0_count, p1_count, p1Critical, p2Critical, pc

vars == << threadNumber, p0_count, p1_count, p1Critical, p2Critical, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ threadNumber = 1
        /\ p0_count = 0
        /\ p1_count = 0
        /\ p1Critical = FALSE
        /\ p2Critical = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P0_INIT"
                                        [] self = 1 -> "P1_INIT"]

P0_INIT == /\ pc[0] = "P0_INIT"
           /\ IF p0_count < 3
                 THEN /\ threadNumber = 1
                      /\ p0_count' = p0_count + 1
                      /\ p1Critical' = TRUE
                      /\ pc' = [pc EXCEPT ![0] = "RELEASE_P0"]
                 ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                      /\ UNCHANGED << p0_count, p1Critical >>
           /\ UNCHANGED << threadNumber, p1_count, p2Critical >>

RELEASE_P0 == /\ pc[0] = "RELEASE_P0"
              /\ p1Critical' = FALSE
              /\ threadNumber' = 2
              /\ pc' = [pc EXCEPT ![0] = "P0_INIT"]
              /\ UNCHANGED << p0_count, p1_count, p2Critical >>

p0 == P0_INIT \/ RELEASE_P0

P1_INIT == /\ pc[1] = "P1_INIT"
           /\ IF p1_count < 5
                 THEN /\ threadNumber = 2
                      /\ p1_count' = p1_count + 1
                      /\ p2Critical' = TRUE
                      /\ pc' = [pc EXCEPT ![1] = "RELEASE_P1"]
                 ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                      /\ UNCHANGED << p1_count, p2Critical >>
           /\ UNCHANGED << threadNumber, p0_count, p1Critical >>

RELEASE_P1 == /\ pc[1] = "RELEASE_P1"
              /\ p2Critical' = FALSE
              /\ threadNumber' = 1
              /\ pc' = [pc EXCEPT ![1] = "P1_INIT"]
              /\ UNCHANGED << p0_count, p1_count, p1Critical >>

p1 == P1_INIT \/ RELEASE_P1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == p0 \/ p1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(p0)
        /\ WF_vars(p1)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sun May 03 13:12:32 CDT 2020 by shiva
\* Created Sun May 03 13:04:37 CDT 2020 by shiva
