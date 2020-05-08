-------------------------- MODULE ProducerConsumerwithSemaphores --------------------------

EXTENDS Naturals, Sequences

CONSTANTS BufferCapacity, \* the fix size of the buffer
          Producers,   \* producers set          
          DataItems,     \* the data items to be produced and consumed
          Consumers   \* consumers set                 

ASSUME /\ Producers # {}                      \* non empty producer
       /\ Consumers # {}                      \*non empty consumer
       /\ Producers \cap Consumers = {}      \* a thread cannot be both prod. and cons.
       /\ BufferCapacity > 0                     \* buffer capacity is non zero *)
       /\ DataItems # {}                           \* there is some type of data to add 


VARIABLES buffer, 
          inactiveSet , 
          empty, full , mutex
          
allThreads == Producers \cup Consumers
ActiveThreads == allThreads \ inactiveSet

Wait(thread) == inactiveSet' = inactiveSet \union {thread}           \* The wait() method of Java

Signal == IF inactiveSet # {}                                        \* The signal() in C or notify()
          THEN \E thread \in inactiveSet : inactiveSet' = inactiveSet \ {thread}
          ELSE UNCHANGED inactiveSet
    

Init == buffer = <<>> 
        /\ inactiveSet = {}
        /\empty = BufferCapacity
        /\ full = 0
        /\ mutex = 1
        

ProdProcess(t,item) == empty'= empty-1 
                    /\ IF empty' < 0
                    THEN Wait(t) /\ UNCHANGED buffer /\ UNCHANGED mutex /\ UNCHANGED full
                    ELSE mutex'=mutex-1 /\ IF mutex' < 0
                    THEN Wait(t) /\ UNCHANGED buffer /\ UNCHANGED full /\ UNCHANGED empty
                    ELSE /\ buffer' = Append(buffer, item)
                         /\ mutex'= mutex+1 /\ Signal 
                         /\ IF ( mutex'> 0)
                           THEN /\ full'= full+1  /\ Signal /\ UNCHANGED buffer /\ UNCHANGED empty
                           ELSE UNCHANGED buffer /\ UNCHANGED full /\ UNCHANGED empty /\ UNCHANGED inactiveSet  


ConProcess(t) ==  full'= full-1 
                 /\ IF full' < 0
                    THEN Wait(t) /\ UNCHANGED buffer /\ UNCHANGED mutex /\ UNCHANGED empty 
                    ELSE mutex'= mutex-1 /\ IF mutex' < 0
                    THEN Wait(t) /\ UNCHANGED buffer /\ UNCHANGED full /\ UNCHANGED empty
                    ELSE /\ buffer' = Tail(buffer)
                         /\ mutex'=mutex+1 /\ Signal
                         /\ IF ( mutex'> 0)
                           THEN /\ empty'= empty+1  /\ Signal /\ UNCHANGED buffer /\ UNCHANGED full
                           ELSE UNCHANGED buffer /\ UNCHANGED full /\ UNCHANGED empty /\ UNCHANGED inactiveSet   
                         

Next == \E t \in ActiveThreads : \/ t \in Consumers /\ ConProcess(t)
                                 \/ t \in Producers /\ \E item \in DataItems : ProdProcess(t,item)
                                  
Spec == Init /\ [][Next]_<<buffer, inactiveSet>> 

\* Invariant
NeverDeadlock == [](ActiveThreads # {})

======================================================================




