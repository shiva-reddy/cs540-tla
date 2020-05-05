------------------------------ MODULE Dekkers ------------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

(* --algorithm Dekkers

variables 
wants_to_enter = <<FALSE, FALSE>>,
turn = 1;
p0i = 1, p1i = 1;

fair process p0 = 0
begin P0_INIT:
    while(p0i < 5) do
        P01:wants_to_enter[1] := TRUE;
        p0While: while wants_to_enter[2] do
            P02:if turn = 2 then
                P03:wants_to_enter[1] := FALSE;
                P04:await turn # 2;
                P05:wants_to_enter[1] := TRUE;
            end if;
        end while;
        
        cs0:skip;
        
        P08:turn := 2;
        P09:wants_to_enter[1] := FALSE;
        P09i:p0i := p0i + 1;
    end while;
end process;

fair process p1 = 1
begin P1_INIT:
    while(p1i < 5) do
        P11:wants_to_enter[2] := TRUE;
        p1While: while wants_to_enter[1] do
            P12:if turn = 1 then
                P13:wants_to_enter[2] := FALSE;
                P14:await turn # 1;
                P15:wants_to_enter[2] := TRUE;
            end if;
        end while;
        
        cs1:skip;
        
        P18:turn := 1;
        P19:wants_to_enter[2] := FALSE;
        P19i: p1i := p1i + 1;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES wants_to_enter, turn, p0i, p1i, pc

vars == << wants_to_enter, turn, p0i, p1i, pc >>

ProcSet == {0} \cup {1}

Init == (* Global variables *)
        /\ wants_to_enter = <<FALSE, FALSE>>
        /\ turn = 1
        /\ p0i = 1
        /\ p1i = 1
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "P0_INIT"
                                        [] self = 1 -> "P1_INIT"]

P0_INIT == /\ pc[0] = "P0_INIT"
           /\ IF (p0i < 5)
                 THEN /\ pc' = [pc EXCEPT ![0] = "P01"]
                 ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
           /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P01 == /\ pc[0] = "P01"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
       /\ pc' = [pc EXCEPT ![0] = "p0While"]
       /\ UNCHANGED << turn, p0i, p1i >>

p0While == /\ pc[0] = "p0While"
           /\ IF wants_to_enter[2]
                 THEN /\ pc' = [pc EXCEPT ![0] = "P02"]
                 ELSE /\ pc' = [pc EXCEPT ![0] = "cs0"]
           /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P02 == /\ pc[0] = "P02"
       /\ IF turn = 2
             THEN /\ pc' = [pc EXCEPT ![0] = "P03"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "p0While"]
       /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P03 == /\ pc[0] = "P03"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![0] = "P04"]
       /\ UNCHANGED << turn, p0i, p1i >>

P04 == /\ pc[0] = "P04"
       /\ turn # 2
       /\ pc' = [pc EXCEPT ![0] = "P05"]
       /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P05 == /\ pc[0] = "P05"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = TRUE]
       /\ pc' = [pc EXCEPT ![0] = "p0While"]
       /\ UNCHANGED << turn, p0i, p1i >>

cs0 == /\ pc[0] = "cs0"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![0] = "P08"]
       /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P08 == /\ pc[0] = "P08"
       /\ turn' = 2
       /\ pc' = [pc EXCEPT ![0] = "P09"]
       /\ UNCHANGED << wants_to_enter, p0i, p1i >>

P09 == /\ pc[0] = "P09"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![1] = FALSE]
       /\ pc' = [pc EXCEPT ![0] = "P09i"]
       /\ UNCHANGED << turn, p0i, p1i >>

P09i == /\ pc[0] = "P09i"
        /\ p0i' = p0i + 1
        /\ pc' = [pc EXCEPT ![0] = "P0_INIT"]
        /\ UNCHANGED << wants_to_enter, turn, p1i >>

p0 == P0_INIT \/ P01 \/ p0While \/ P02 \/ P03 \/ P04 \/ P05 \/ cs0 \/ P08
         \/ P09 \/ P09i

P1_INIT == /\ pc[1] = "P1_INIT"
           /\ IF (p1i < 5)
                 THEN /\ pc' = [pc EXCEPT ![1] = "P11"]
                 ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
           /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P11 == /\ pc[1] = "P11"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
       /\ pc' = [pc EXCEPT ![1] = "p1While"]
       /\ UNCHANGED << turn, p0i, p1i >>

p1While == /\ pc[1] = "p1While"
           /\ IF wants_to_enter[1]
                 THEN /\ pc' = [pc EXCEPT ![1] = "P12"]
                 ELSE /\ pc' = [pc EXCEPT ![1] = "cs1"]
           /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P12 == /\ pc[1] = "P12"
       /\ IF turn = 1
             THEN /\ pc' = [pc EXCEPT ![1] = "P13"]
             ELSE /\ pc' = [pc EXCEPT ![1] = "p1While"]
       /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P13 == /\ pc[1] = "P13"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "P14"]
       /\ UNCHANGED << turn, p0i, p1i >>

P14 == /\ pc[1] = "P14"
       /\ turn # 1
       /\ pc' = [pc EXCEPT ![1] = "P15"]
       /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P15 == /\ pc[1] = "P15"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = TRUE]
       /\ pc' = [pc EXCEPT ![1] = "p1While"]
       /\ UNCHANGED << turn, p0i, p1i >>

cs1 == /\ pc[1] = "cs1"
       /\ TRUE
       /\ pc' = [pc EXCEPT ![1] = "P18"]
       /\ UNCHANGED << wants_to_enter, turn, p0i, p1i >>

P18 == /\ pc[1] = "P18"
       /\ turn' = 1
       /\ pc' = [pc EXCEPT ![1] = "P19"]
       /\ UNCHANGED << wants_to_enter, p0i, p1i >>

P19 == /\ pc[1] = "P19"
       /\ wants_to_enter' = [wants_to_enter EXCEPT ![2] = FALSE]
       /\ pc' = [pc EXCEPT ![1] = "P19i"]
       /\ UNCHANGED << turn, p0i, p1i >>

P19i == /\ pc[1] = "P19i"
        /\ p1i' = p1i + 1
        /\ pc' = [pc EXCEPT ![1] = "P1_INIT"]
        /\ UNCHANGED << wants_to_enter, turn, p0i >>

p1 == P1_INIT \/ P11 \/ p1While \/ P12 \/ P13 \/ P14 \/ P15 \/ cs1 \/ P18
         \/ P19 \/ P19i

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

MutualExlcusion == ~ (pc[0] = "cs0" /\ pc[1] = "cs1")
StarvationFree ==  ((pc[0] = "P01") ~> (pc[0] = "cs0")) /\((pc[1] = "P11") ~> (pc[1] = "cs1"))
DeadlockFree == ((pc[0] = "P04") => (pc[1] = "cs1")) /\ ((pc[1] = "P14") => (pc[0] = "cs0"))
                     
(*     PlusCal options (wf)                                                *)
(***************************************************************************)
(*                               LIVENESS                                  *)
(*                                                                         *)
(* If you are a sophisticated PlusCal user and know a little temporal      *)
(* logic, you can continue reading about the liveness properties of the    *)
(* algorithm.                                                              *)
(*                                                                         *)
(* Dijkstra's algorithm is "deadlock free", which for a mutual exclusion   *)
(* algorithm means that if some process is trying to enter its critical    *)
(* section, then some process (not necessarily the same one) will          *)
(* eventually enter its critical section.  Since a process begins trying   *)
(* to enter its critical section when it is at the control point labeled   *)
(* Li0, and it is in its critical section when it is at control point cs,  *)
(* the following formula asserts deadlock freedom.                         *)
(***************************************************************************)
=============================================================================
\* Modification History
\* Last modified Tue May 05 18:14:13 CDT 2020 by shiva
\* Created Sat May 02 14:24:47 CDT 2020 by shiva
