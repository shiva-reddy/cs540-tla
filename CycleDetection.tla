--------------------------- MODULE CycleDetection ---------------------------

EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat

Nodes == 1..N

NIL == CHOOSE NIL : NIL \notin Nodes

(*
--algorithm TortoiseAndHare

variables
    start \in Nodes,
    succ \in [Nodes -> Nodes \union {NIL}],
    cycle, tortoise, hare, done, steps_taken, step_limit;
begin
h0: tortoise := start;
    hare := start;
    done := FALSE;
    steps_taken := 0;
    step_limit := 2;
h1: while ~done do
    h2: hare := succ[hare];
        steps_taken := steps_taken + 1;
    h3: if tortoise = NIL \/ hare = NIL then
                cycle := FALSE;
                done := TRUE;
        elsif tortoise = hare then
                cycle := TRUE; 
                done := TRUE;
        end if;
    h4: if steps_taken = step_limit then
                steps_taken := 0;
                step_limit := step_limit * 2;
                tortoise := hare;
        end if;
    end while;

end algorithm
*)
\* BEGIN TRANSLATION  PCal-4c07b545b43764e1b786a14691d6aea7
CONSTANT defaultInitValue
VARIABLES start, succ, cycle, tortoise, hare, done, steps_taken, step_limit, 
          pc

vars == << start, succ, cycle, tortoise, hare, done, steps_taken, step_limit, 
           pc >>

Init == (* Global variables *)
        /\ start \in Nodes
        /\ succ \in [Nodes -> Nodes \union {NIL}]
        /\ cycle = defaultInitValue
        /\ tortoise = defaultInitValue
        /\ hare = defaultInitValue
        /\ done = defaultInitValue
        /\ steps_taken = defaultInitValue
        /\ step_limit = defaultInitValue
        /\ pc = "h0"

h0 == /\ pc = "h0"
      /\ tortoise' = start
      /\ hare' = start
      /\ done' = FALSE
      /\ steps_taken' = 0
      /\ step_limit' = 2
      /\ pc' = "h1"
      /\ UNCHANGED << start, succ, cycle >>

h1 == /\ pc = "h1"
      /\ IF ~done
            THEN /\ pc' = "h2"
            ELSE /\ pc' = "Done"
      /\ UNCHANGED << start, succ, cycle, tortoise, hare, done, steps_taken, 
                      step_limit >>

h2 == /\ pc = "h2"
      /\ hare' = succ[hare]
      /\ steps_taken' = steps_taken + 1
      /\ pc' = "h3"
      /\ UNCHANGED << start, succ, cycle, tortoise, done, step_limit >>

h3 == /\ pc = "h3"
      /\ IF tortoise = NIL \/ hare = NIL
            THEN /\ cycle' = FALSE
                 /\ done' = TRUE
            ELSE /\ IF tortoise = hare
                       THEN /\ cycle' = TRUE
                            /\ done' = TRUE
                       ELSE /\ TRUE
                            /\ UNCHANGED << cycle, done >>
      /\ pc' = "h4"
      /\ UNCHANGED << start, succ, tortoise, hare, steps_taken, step_limit >>

h4 == /\ pc = "h4"
      /\ IF steps_taken = step_limit
            THEN /\ steps_taken' = 0
                 /\ step_limit' = step_limit * 2
                 /\ tortoise' = hare
            ELSE /\ TRUE
                 /\ UNCHANGED << tortoise, steps_taken, step_limit >>
      /\ pc' = "h1"
      /\ UNCHANGED << start, succ, cycle, hare, done >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == h0 \/ h1 \/ h2 \/ h3 \/ h4
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION  TLA-59369fa95e4d36ee4eeadf6a794f0c9e

\* Transitive closure
TC(R) ==
  LET Support(X) == {r[1] : r \in X} \cup {r[2] : r \in X}
      S == Support(R)
      RECURSIVE TCR(_)
      TCR(T) == IF T = {} 
                  THEN R
                  ELSE LET r == CHOOSE s \in T : TRUE
                           RR == TCR(T \ {r})
                       IN  RR \cup {<<s, t>> \in S \X S : 
                                      <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN  TCR(S)

HasCycle(node) == LET R == {<<s, t>> \in Nodes \X (Nodes \union {NIL}): succ[s] = t }
                  IN <<node, NIL>> \notin TC(R)


\* An alternate definition of HasCycle

HasCycle2(node) ==
  LET R == {<<s, t>> \in Nodes \X (Nodes \union {NIL}): succ[s] = t }
  IN \E n \in Nodes : /\ <<node, n>> \in TC(R) 
                      /\ <<n, n>> \in TC(R)
                  
PartialCorrectness == pc="Done" => (cycle <=> HasCycle(start))


=============================================================================
\* Modification History
\* Last modified Thu May 07 12:50:53 CDT 2020 by yukth
