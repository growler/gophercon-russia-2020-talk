----- MODULE 03_GoChannel -----
INSTANCE TLC
CONSTANTS NULL, Message

(*--algorithm GoChannel
variables 
    ch = [open |-> TRUE, sent |-> FALSE, rcvd |-> FALSE, val |-> NULL],
    result = NULL;
define
    Success == <>[](result = Message)

    Ordered == pc.sender = "Done" ~> pc.receiver = "Done"
end define;

fair process Sender = "sender"
begin
  Send:
    assert ch.open;
    await ~ch.sent;
    ch.val := Message || ch.sent := TRUE;
  WaitSent:
    await ch.sent /\ ch.rcvd;
    ch.sent := FALSE || ch.rcvd := FALSE;
  Close:
    assert ch.open;
    ch.open := FALSE;
end process;   

fair process Receiver = "receiver"
begin Receive:
  while TRUE do
    either            
      await ch.sent /\ ~ch.rcvd;
      result := ch.val || ch.val := NULL || ch.rcvd := TRUE;
    or
      await ~ch.open;
      goto Done;
    end either;
  end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES ch, result, pc

(* define statement *)
Success == <>[](result = Message)

Ordered == pc.sender = "Done" ~> pc.receiver = "Done"


vars == << ch, result, pc >>

ProcSet == {"sender"} \cup {"receiver"}

Init == (* Global variables *)
        /\ ch = [open |-> TRUE, sent |-> FALSE, rcvd |-> FALSE, val |-> NULL]
        /\ result = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "sender" -> "Send"
                                        [] self = "receiver" -> "Receive"]

Send == /\ pc["sender"] = "Send"
        /\ Assert(ch.open, "Failure of assertion at line 18, column 5.")
        /\ ~ch.sent
        /\ ch' = [ch EXCEPT !.val = Message,
                            !.sent = TRUE]
        /\ pc' = [pc EXCEPT !["sender"] = "WaitSent"]
        /\ UNCHANGED result

WaitSent == /\ pc["sender"] = "WaitSent"
            /\ ch.sent /\ ch.rcvd
            /\ ch' = [ch EXCEPT !.sent = FALSE,
                                !.rcvd = FALSE]
            /\ pc' = [pc EXCEPT !["sender"] = "Close"]
            /\ UNCHANGED result

Close == /\ pc["sender"] = "Close"
         /\ Assert(ch.open, "Failure of assertion at line 25, column 5.")
         /\ ch' = [ch EXCEPT !.open = FALSE]
         /\ pc' = [pc EXCEPT !["sender"] = "Done"]
         /\ UNCHANGED result

Sender == Send \/ WaitSent \/ Close

Receive == /\ pc["receiver"] = "Receive"
           /\ \/ /\ ch.sent /\ ~ch.rcvd
                 /\ /\ ch' = [ch EXCEPT !.val = NULL,
                                        !.rcvd = TRUE]
                    /\ result' = ch.val
                 /\ pc' = [pc EXCEPT !["receiver"] = "Receive"]
              \/ /\ ~ch.open
                 /\ pc' = [pc EXCEPT !["receiver"] = "Done"]
                 /\ UNCHANGED <<ch, result>>

Receiver == Receive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Sender \/ Receiver
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Sender)
        /\ WF_vars(Receiver)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

===============================
