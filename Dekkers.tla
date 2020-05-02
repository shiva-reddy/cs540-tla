------------------------------ MODULE Dekkers ------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

(* --algorithm Dekkers

variables 
wants_to_enter = <<FALSE, FALSE>>,
turn = 0,
p1AccessingCritical = FALSE,
p2AccessingCritical = FALSE;

fair process p0 = 0
begin P0_INIT:
    while TRUE do
        wants_to_enter[1] := TRUE;
        A:while wants_to_enter[2] do
            if turn = 1 then
                wants_to_enter[1] := FALSE;
                await turn = 1;
                B:wants_to_enter[1] := TRUE;
            end if;
        end while;
        p1AccessingCritical := TRUE;
        E:p1AccessingCritical := FALSE;
        \*Critical section
        turn := 1;
        wants_to_enter[1] := FALSE
     end while;
end process;

fair process p1 = 1
begin P1_INIT:
     while TRUE do
        wants_to_enter[2] := TRUE;
        C:while wants_to_enter[1] do
            if turn = 0 then
                wants_to_enter[2] := FALSE;
                await turn = 0;
                D:wants_to_enter[2] := TRUE;
            end if;
        end while;
        \*Critical section
        p2AccessingCritical := TRUE;
        F:p2AccessingCritical := FALSE;
        turn := 0;
        wants_to_enter[2] := FALSE;
     end while;
end process

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES wants_to_enter, turn, p1AccessingCritical, p2AccessingCritical, pc

vars == << wants_to_enter, turn, p1AccessingCritical, p2AccessingCritical, pc
        >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ wants_to_enter = <<FALSE, FALSE>>
        /\ turn = 0
        /\ p1AccessingCritical = FALSE
        /\ p2AccessingCritical = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P0_INIT"
                                        [] self = 1 -> "P1_INIT"]

P0_INIT == /\ pc[0] = "P0_INIT"
           /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
           /\ pc' = [pc EXCEPT ![0] = "A"]
           /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical >>

A == /\ pc[0] = "A"
     /\ IF wants_to_enter[2]
           THEN /\ IF turn = 1
                      THEN /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
                           /\ turn = 1
                           /\ pc' = [pc EXCEPT ![0] = "B"]
                      ELSE /\ pc' = [pc EXCEPT ![0] = "A"]
                           /\ UNCHANGED wants_to_enter
                /\ UNCHANGED p1AccessingCritical
           ELSE /\ p1AccessingCritical' = TRUE
                /\ pc' = [pc EXCEPT ![0] = "E"]
                /\ UNCHANGED wants_to_enter
     /\ UNCHANGED << turn, p2AccessingCritical >>

B == /\ pc[0] = "B"
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
     /\ pc' = [pc EXCEPT ![0] = "A"]
     /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical >>

E == /\ pc[0] = "E"
     /\ p1AccessingCritical' = FALSE
     /\ turn' = 1
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
     /\ pc' = [pc EXCEPT ![0] = "P0_INIT"]
     /\ UNCHANGED p2AccessingCritical

p0 == P0_INIT \/ A \/ B \/ E

P1_INIT == /\ pc[1] = "P1_INIT"
           /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
           /\ pc' = [pc EXCEPT ![1] = "C"]
           /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical >>

C == /\ pc[1] = "C"
     /\ IF wants_to_enter[1]
           THEN /\ IF turn = 0
                      THEN /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
                           /\ turn = 0
                           /\ pc' = [pc EXCEPT ![1] = "D"]
                      ELSE /\ pc' = [pc EXCEPT ![1] = "C"]
                           /\ UNCHANGED wants_to_enter
                /\ UNCHANGED p2AccessingCritical
           ELSE /\ p2AccessingCritical' = TRUE
                /\ pc' = [pc EXCEPT ![1] = "F"]
                /\ UNCHANGED wants_to_enter
     /\ UNCHANGED << turn, p1AccessingCritical >>

D == /\ pc[1] = "D"
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
     /\ pc' = [pc EXCEPT ![1] = "C"]
     /\ UNCHANGED << turn, p1AccessingCritical, p2AccessingCritical >>

F == /\ pc[1] = "F"
     /\ p2AccessingCritical' = FALSE
     /\ turn' = 0
     /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
     /\ pc' = [pc EXCEPT ![1] = "P1_INIT"]
     /\ UNCHANGED p1AccessingCritical

p1 == P1_INIT \/ C \/ D \/ F

Next == p0 \/ p1

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(p0)
        /\ WF_vars(p1)

\* END TRANSLATION

CriticalSectionSafety == (p1AccessingCritical /\ p2AccessingCritical) = FALSE
=============================================================================
\* Modification History
\* Last modified Sat May 02 16:09:36 CDT 2020 by shiva
\* Created Sat May 02 14:24:47 CDT 2020 by shiva
