------------------------------- MODULE 05_ChannelBug ------------------------
EXTENDS Sequences, FiniteSets, Integers, TLC

\* MUST FAIL

CONSTANT NULL, Message

Data == {Message}

LOCAL INSTANCE Channels WITH Data <- Data

(*--fair algorithm go_deadlock_demo
variables ch = MakeChan;

macro send(ch, msg) begin await MaySend(ch); ch := UpdateSend(ch, msg); end macro;
macro wait_sent(ch) begin await Sent(ch); ch := UpdateSent(ch); end macro;
macro recv(var, ch)
begin await MayReceive(ch);
    if ~ch.open then var := NULL;
    else var := ch.val || ch := UpdateReceived(ch); end if;
end macro;
macro close(ch) begin assert MayClose(ch); ch := UpdateClose(ch); end macro;

fair process processor = "processor"
begin 
    Proc_1: send(ch, "result");
    Proc_2: wait_sent(ch);
end process;

fair process receiver = "receiver"
variable rslt = NULL;
begin Rec_1:
    either
        recv(rslt, ch);
    or
        skip;
    end either;
end process;
    
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES ch, pc, rslt

vars == << ch, pc, rslt >>

ProcSet == {"processor"} \cup {"receiver"}

Init == (* Global variables *)
        /\ ch = MakeChan
        (* Process receiver *)
        /\ rslt = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "processor" -> "Proc_1"
                                        [] self = "receiver" -> "Rec_1"]

Proc_1 == /\ pc["processor"] = "Proc_1"
          /\ MaySend(ch)
          /\ ch' = UpdateSend(ch, "result")
          /\ pc' = [pc EXCEPT !["processor"] = "Proc_2"]
          /\ rslt' = rslt

Proc_2 == /\ pc["processor"] = "Proc_2"
          /\ Sent(ch)
          /\ ch' = UpdateSent(ch)
          /\ pc' = [pc EXCEPT !["processor"] = "Done"]
          /\ rslt' = rslt

processor == Proc_1 \/ Proc_2

Rec_1 == /\ pc["receiver"] = "Rec_1"
         /\ \/ /\ MayReceive(ch)
               /\ IF ~ch.open
                     THEN /\ rslt' = NULL
                          /\ ch' = ch
                     ELSE /\ /\ ch' = UpdateReceived(ch)
                             /\ rslt' = ch.val
            \/ /\ TRUE
               /\ UNCHANGED <<ch, rslt>>
         /\ pc' = [pc EXCEPT !["receiver"] = "Done"]

receiver == Rec_1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == processor \/ receiver
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(processor)
        /\ WF_vars(receiver)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 03 14:16:55 MSK 2020 by growler
\* Created Mon Mar 02 09:59:39 MSK 2020 by growler
