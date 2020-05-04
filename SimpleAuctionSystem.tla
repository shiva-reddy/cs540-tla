------------------------ MODULE SimpleAuctionSystem ------------------------


EXTENDS TLC,Integers

(* --algorithm auction

variables sellReserve = 10,winner = -1,bidder \in 1 .. 100;

begin 
    if bidder > sellReserve then
        winner := bidder;
    end if;
    print winner;
    
end algorithm; 
*)
\* BEGIN TRANSLATION
VARIABLES sellReserve, winner, bidder, pc

vars == << sellReserve, winner, bidder, pc >>

Init == (* Global variables *)
        /\ sellReserve = 10
        /\ winner = -1
        /\ bidder \in 1 .. 100
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF bidder > sellReserve
               THEN /\ winner' = bidder
               ELSE /\ TRUE
                    /\ UNCHANGED winner
         /\ PrintT(winner')
         /\ pc' = "Done"
         /\ UNCHANGED << sellReserve, bidder >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION




=============================================================================
\* Modification History
\* Last modified Sun May 03 21:51:53 CDT 2020 by anoopnagabhushan
\* Created Sun May 03 18:06:42 CDT 2020 by anoopnagabhushan
