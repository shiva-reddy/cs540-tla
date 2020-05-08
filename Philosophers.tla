---------------------------- MODULE Philosophers ----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets
CONSTANTS NumPhilosophers, MaxEatCount, NULL
ASSUME NumPhilosophers > 1
ASSUME MaxEatCount > 0
NP == NumPhilosophers

(* --algorithm dining_philosophers
variables 
  forks = [fork \in 1..NP |-> NULL],
  lock =  0;

define
LeftFork(p) == p

RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = p}

AvailableForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = NULL}
end define;

fair process philosopher \in 1..NP
variables eatCount = 0;
begin
Wait:
  while TRUE do
    await lock = 0; 
    if Cardinality(AvailableForks(self)) = 2 then
      lock := 1;
      GrabLeftFork:
        forks[LeftFork(self)] := self;
      GrabRightFork:
        forks[RightFork(self)] := self;
      lock := 0;
      goto Eat;
    end if;
  end while;
Eat:
  assert Cardinality(HeldForks(self)) = 2;
  forks[LeftFork(self)] := NULL ||
  forks[RightFork(self)] := NULL;
  eatCount := eatCount + 1;
  if eatCount <= MaxEatCount then
    Decide:
      either
        goto Wait
      or
        skip;
      end either;
  end if;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES forks, lock, pc

(* define statement *)
LeftFork(p) == p

RightFork(p) == IF p = NP THEN 1 ELSE p + 1

HeldForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = p}

AvailableForks(p) ==
  { x \in {LeftFork(p), RightFork(p)}: forks[x] = NULL}

VARIABLE eatCount

vars == << forks, lock, pc, eatCount >>

ProcSet == (1..NP)

Init == (* Global variables *)
        /\ forks = [fork \in 1..NP |-> NULL]
        /\ lock = 0
        (* Process philosopher *)
        /\ eatCount = [self \in 1..NP |-> 0]
        /\ pc = [self \in ProcSet |-> "Wait"]

Wait(self) == /\ pc[self] = "Wait"
              /\ lock = 0
              /\ IF Cardinality(AvailableForks(self)) = 2
                    THEN /\ lock' = 1
                         /\ pc' = [pc EXCEPT ![self] = "GrabLeftFork"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "Wait"]
                         /\ lock' = lock
              /\ UNCHANGED << forks, eatCount >>

GrabLeftFork(self) == /\ pc[self] = "GrabLeftFork"
                      /\ forks' = [forks EXCEPT ![LeftFork(self)] = self]
                      /\ pc' = [pc EXCEPT ![self] = "GrabRightFork"]
                      /\ UNCHANGED << lock, eatCount >>

GrabRightFork(self) == /\ pc[self] = "GrabRightFork"
                       /\ forks' = [forks EXCEPT ![RightFork(self)] = self]
                       /\ lock' = 0
                       /\ pc' = [pc EXCEPT ![self] = "Eat"]
                       /\ UNCHANGED eatCount

Eat(self) == /\ pc[self] = "Eat"
             /\ Assert(Cardinality(HeldForks(self)) = 2, 
                       "Failure of assertion at line 42, column 3.")
             /\ forks' = [forks EXCEPT ![LeftFork(self)] = NULL,
                                       ![RightFork(self)] = NULL]
             /\ eatCount' = [eatCount EXCEPT ![self] = eatCount[self] + 1]
             /\ IF eatCount'[self] <= MaxEatCount
                   THEN /\ pc' = [pc EXCEPT ![self] = "Decide"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ lock' = lock

Decide(self) == /\ pc[self] = "Decide"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "Wait"]
                   \/ /\ TRUE
                      /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << forks, lock, eatCount >>

philosopher(self) == Wait(self) \/ GrabLeftFork(self)
                        \/ GrabRightFork(self) \/ Eat(self) \/ Decide(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 1..NP: philosopher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..NP : WF_vars(philosopher(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

\* Invariants
NotDone == \E self \in ProcSet: pc[self] /= "Done"
OneOrLessEating == Cardinality({ x \in 1..NP: forks[x] /= NULL }) < 4
NoStarvation == eatCount /= <<MaxEatCount, MaxEatCount, MaxEatCount, MaxEatCount, 0>>
=============================================================================
\* Modification History
\* Last modified Thu May 07 23:37:09 CDT 2020 by wicho
\* Created Sun May 03 16:13:01 CDT 2020 by wicho
