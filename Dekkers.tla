------------------------------ MODULE Dekkers ------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

(* --algorithm Dekkers

variables 
wants_to_enter = <<FALSE, FALSE>>,
turn = 1,
p1AccessingCritical = FALSE,
p2AccessingCritical = FALSE, p0Finished = FALSE, p1Finished = FALSE;

fair process p0 = 0
begin P0_INIT:
        wants_to_enter[1] := TRUE;
        p0While: while wants_to_enter[2] do
            A:if turn = 2 then
                wants_to_enter[1] := FALSE;
                await turn # 2;
                B:wants_to_enter[1] := TRUE;
            end if;
        end while;
        p1AccessingCritical := TRUE;
        E:p1AccessingCritical := FALSE;
        \*Critical section
        turn := 2;
        wants_to_enter[1] := FALSE;
        p0Finished := TRUE;
        
end process;

fair process p1 = 1
begin P1_INIT:
        wants_to_enter[2] := TRUE;
        p1While : while wants_to_enter[1] do
            C:if turn = 1 then
                wants_to_enter[2] := FALSE;
                await turn # 1;
                D:wants_to_enter[2] := TRUE;
            end if;
        end while;
        \*Critical section
        p2AccessingCritical := TRUE;
        F:p2AccessingCritical := FALSE;
        turn := 1;
        wants_to_enter[2] := FALSE;
        p1Finished := TRUE;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES wants_to_enter, turn, p1AccessingCritical, p2AccessingCritical, 
          p0Finished, p1Finished, pc

vars == << wants_to_enter, turn, p1AccessingCritical, p2AccessingCritical, 
           p0Finished, p1Finished, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ wants_to_enter = <<FALSE, FALSE>>
        /\ turn = 1
        /\ p1AccessingCritical = FALSE
        /\ p2AccessingCritical = FALSE
        /\ p0Finished = FALSE
        /\ p1Finished = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P0_INIT"
                                        [] self = 1 -> "P1_INIT"]

P0_INIT == /\ pc[0] = "P0_INIT"
           /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
           /\ pc' = [pc EXCEPT ![0] = "p0While"]
           /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical, 
                           p0Finished, p1Finished >>

p0While == /\ pc[0] = "p0While"
           /\ IF wants_to_enter[2]
                 THEN /\ pc' = [pc EXCEPT ![0] = "A"]
                      /\ UNCHANGED p1AccessingCritical
                 ELSE /\ p1AccessingCritical' = TRUE
                      /\ pc' = [pc EXCEPT ![0] = "E"]
           /\ UNCHANGED << wants_to_enter, turn, p2AccessingCritical, 
                           p0Finished, p1Finished >>

A == /\ pc[0] = "A"
     /\ IF turn = 2
           THEN /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
                /\ turn # 2
                /\ pc' = [pc EXCEPT ![0] = "B"]
           ELSE /\ pc' = [pc EXCEPT ![0] = "p0While"]
                /\ UNCHANGED wants_to_enter
     /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical, 
                     p0Finished, p1Finished >>

B == /\ pc[0] = "B"
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
     /\ pc' = [pc EXCEPT ![0] = "p0While"]
     /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical, 
                     p0Finished, p1Finished >>

E == /\ pc[0] = "E"
     /\ p1AccessingCritical' = FALSE
     /\ turn' = 2
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
     /\ p0Finished' = TRUE
     /\ pc' = [pc EXCEPT ![0] = "Done"]
     /\ UNCHANGED << p2AccessingCritical, p1Finished >>

p0 == P0_INIT \/ p0While \/ A \/ B \/ E

P1_INIT == /\ pc[1] = "P1_INIT"
           /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
           /\ pc' = [pc EXCEPT ![1] = "p1While"]
           /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical, 
                           p0Finished, p1Finished >>

p1While == /\ pc[1] = "p1While"
           /\ IF wants_to_enter[1]
                 THEN /\ pc' = [pc EXCEPT ![1] = "C"]
                      /\ UNCHANGED p2AccessingCritical
                 ELSE /\ p2AccessingCritical' = TRUE
                      /\ pc' = [pc EXCEPT ![1] = "F"]
           /\ UNCHANGED << wants_to_enter, turn, p1AccessingCritical, 
                           p0Finished, p1Finished >>

C == /\ pc[1] = "C"
     /\ IF turn = 1
           THEN /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
                /\ turn # 1
                /\ pc' = [pc EXCEPT ![1] = "D"]
           ELSE /\ pc' = [pc EXCEPT ![1] = "p1While"]
                /\ UNCHANGED wants_to_enter
     /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical, 
                     p0Finished, p1Finished >>

D == /\ pc[1] = "D"
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
     /\ pc' = [pc EXCEPT ![1] = "p1While"]
     /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical, 
                     p0Finished, p1Finished >>

F == /\ pc[1] = "F"
     /\ p2AccessingCritical' = FALSE
     /\ turn' = 1
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
     /\ p1Finished' = TRUE
     /\ pc' = [pc EXCEPT ![1] = "Done"]
     /\ UNCHANGED << p1AccessingCritical, p0Finished >>

p1 == P1_INIT \/ p1While \/ C \/ D \/ F

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

CriticalSectionSafety == (p1AccessingCritical /\ p2AccessingCritical) = FALSE
Progress == ([]p0Finished ~> <>p1Finished) /\ ([]p1Finished ~> <>p0Finished)
=============================================================================
\* Modification History
\* Last modified Sun May 03 14:54:51 CDT 2020 by shiva
\* Created Sat May 02 14:24:47 CDT 2020 by shiva
