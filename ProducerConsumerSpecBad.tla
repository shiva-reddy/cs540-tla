---------------------------- MODULE ProducerConsumerSpecBad ----------------------------

EXTENDS Naturals, Sequences

CONSTANTS BufCapacity, \* the fix size of the buffer
          Producers,   \* producers set          
          DataItems,     \* the data items to be produced and consumed
          Consumers   \* consumers set                 

ASSUME /\ Producers # {}                      \* non empty producer
       /\ Consumers # {}                      \*non empty consumer
       /\ Producers \cap Consumers = {}      \* a thread cannot be both prod. and cons.
       /\ BufCapacity > 0                     \* buffer capacity is non zero *)
       /\ DataItems # {}                           \* there is some type of data to add 

VARIABLES buffer, \*the buffer
          inactiveSet \* a set of inactive threads            

allThreads == Producers \cup Consumers
ActiveThreads == allThreads \ inactiveSet

Wait(thread) == inactiveSet' = inactiveSet \union {thread}           \* The wait() method of Java

Signal == IF inactiveSet # {}                                        \* The signal() in C or notify()
          THEN \E thread \in inactiveSet : inactiveSet' = inactiveSet \ {thread}
          ELSE UNCHANGED inactiveSet
    
Init ==/\buffer = <<>>
       /\inactiveSet = {}

Consume(t) == IF Len(buffer) > 0
          THEN /\ buffer' = Tail(buffer)
               /\ Signal
          ELSE /\ Wait(t)
               /\ UNCHANGED buffer

Produce(t,item) == IF Len(buffer) < BufCapacity
            THEN /\ buffer' = Append(buffer, item)
                 /\ Signal
            ELSE /\ Wait(t)
                 /\ UNCHANGED buffer

Next == \E t \in ActiveThreads : \/ t \in Consumers /\ Consume(t)
                                 \/ t \in Producers /\ \E item \in DataItems : Produce(t,item)
                                  
Spec == Init /\ [][Next]_<<buffer, inactiveSet>> 

\* Invariant
NeverDeadlock == [](ActiveThreads # {})

=============================================================================

