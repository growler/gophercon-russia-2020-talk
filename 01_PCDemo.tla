---- MODULE 01_PCDemo -----
EXTENDS Naturals

(*--algorithm 01_PCDemo

variables 
  a = 0, 
  b = 0;

define 
  Success == <>[](a+b = 5)
end define;

fair process proc1 = 1
begin p1:
  a := b + 1;
  b := a + 1; 
end process;   

fair process proc2 = 2
begin p2:
  b := a + 1; 
  a := b + 1;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES a, b, pc

(* define statement *)
Success == <>[](a+b = 5)


vars == << a, b, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ a = 0
        /\ b = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "p1"
                                        [] self = 2 -> "p2"]

p1 == /\ pc[1] = "p1"
      /\ a' = b + 1
      /\ b' = a' + 1
      /\ pc' = [pc EXCEPT ![1] = "Done"]

proc1 == p1

p2 == /\ pc[2] = "p2"
      /\ b' = a + 1
      /\ a' = b' + 1
      /\ pc' = [pc EXCEPT ![2] = "Done"]

proc2 == p2

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
===========================
