----------------------------- MODULE 00_Counter ------------------------------
EXTENDS Naturals
CONSTANTS MinValue, MaxValue
ASSUME MinValue < MaxValue
VARIABLE counter

Invariant == counter \in MinValue..MaxValue 

Success == <>[](counter = MaxValue)

Init == counter = MinValue

Next == counter' = IF counter < MaxValue
                   THEN counter + 1
                   ELSE counter
                            
Spec == /\ Init            
        /\ [][Next]_counter
        /\ WF_counter(Next)                           

==============================================================================
