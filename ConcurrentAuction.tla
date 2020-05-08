------------------------- MODULE ConcurrentAuction -------------------------

EXTENDS TLC,Integers

(* --algorithm auction

variable winner=-1;
process p \in 1..3
variables sellReserve = 10,bidder \in 1 .. 100,bidPrice;
begin
  A:
    if winner \in 10..20 then
  B:
        if  bidder > sellReserve then
            winner := self;
            bidPrice := bidder;
        end if;
     print winner;
     end if
    
  
end process; 

end algorithm; 
*)
\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES winner, pc, sellReserve, bidder, bidPrice

vars == << winner, pc, sellReserve, bidder, bidPrice >>

ProcSet == (1..3)

Init == (* Global variables *)
        /\ winner = -1
        (* Process p *)
        /\ sellReserve = [self \in 1..3 |-> 10]
        /\ bidder \in [1..3 -> 1 .. 100]
        /\ bidPrice = [self \in 1..3 |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "A"]

A(self) == /\ pc[self] = "A"
           /\ IF winner \in 10..20
                 THEN /\ pc' = [pc EXCEPT ![self] = "B"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << winner, sellReserve, bidder, bidPrice >>

B(self) == /\ pc[self] = "B"
           /\ IF bidder[self] > sellReserve[self]
                 THEN /\ winner' = self
                      /\ bidPrice' = [bidPrice EXCEPT ![self] = bidder[self]]
                 ELSE /\ TRUE
                      /\ UNCHANGED << winner, bidPrice >>
           /\ PrintT(winner')
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << sellReserve, bidder >>

p(self) == A(self) \/ B(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..3: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION



=============================================================================
\* Modification History
\* Last modified Fri May 08 16:57:13 CDT 2020 by anoopnagabhushan
\* Created Fri May 08 16:55:50 CDT 2020 by anoopnagabhushan
