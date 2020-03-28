------------------------------- MODULE 02_PCDemo --------------------------------
EXTENDS Integers

(*--algorithm A

variables 
    a = 0, 
    b = 0;

define 
    Success == <>[](
        (a + b) = 5
    )
end define;

fair process proc1 = 1
begin
    p1_1: a := b + 1;
    p1_2: b := a + 1; 
end process;

fair process proc2 = 2
begin
    p2_1: b := a + 1; 
    p2_2: a := b + 1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES a, b, pc

(* define statement *)
Success == <>[](
    (a + b) = 5
)


vars == << a, b, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ a = 0
        /\ b = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "p1_1"
                                        [] self = 2 -> "p2_1"]

p1_1 == /\ pc[1] = "p1_1"
        /\ a' = b + 1
        /\ pc' = [pc EXCEPT ![1] = "p1_2"]
        /\ b' = b

p1_2 == /\ pc[1] = "p1_2"
        /\ b' = a + 1
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ a' = a

proc1 == p1_1 \/ p1_2

p2_1 == /\ pc[2] = "p2_1"
        /\ b' = a + 1
        /\ pc' = [pc EXCEPT ![2] = "p2_2"]
        /\ a' = a

p2_2 == /\ pc[2] = "p2_2"
        /\ a' = b + 1
        /\ pc' = [pc EXCEPT ![2] = "Done"]
        /\ b' = b

proc2 == p2_1 \/ p2_2

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == proc1 \/ proc2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(proc1)
        /\ WF_vars(proc2)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 03 14:16:55 MSK 2020 by growler
\* Created Mon Mar 02 09:59:39 MSK 2020 by growler
