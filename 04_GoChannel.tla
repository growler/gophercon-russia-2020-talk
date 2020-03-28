----- MODULE 04_GoChannel -----
EXTENDS Sequences, Integers, TLC
CONSTANTS MaxMsg, NULL

(*--algorithm GoChannel
variables 
    sent = <<>>, recvd = <<>>;
    ch = [open |-> TRUE, sent |-> FALSE, rcvd |-> FALSE, val |-> NULL],
    nextId = 1,
define
    Success == <>[](sent = recvd)
end define;

macro send(ch, msg) 
begin 
    assert ch.open;
    await ~ch.sent;
    ch.val := msg || ch.sent := TRUE;
end macro;

macro wait_sent(ch)
begin 
    await ch.sent /\ ch.rcvd;
    ch.sent := FALSE || ch.rcvd := FALSE;
end macro;

macro recv(var, ch)
begin 
    await ~ch.open \/ (ch.sent /\ ~ch.rcvd);
    if ~ch.open then var := NULL;
    else 
        var := ch.val || ch.val := NULL || ch.rcvd := TRUE;
    end if;
end macro;

macro close(ch)
begin 
    assert ch.open;
    ch.open := FALSE;
end macro;

fair process Sender = "sender"
variable i = 0;
begin Send:
    while nextId \in 1..MaxMsg do
        i := nextId || sent := Append(sent, nextId) || nextId := nextId + 1;
        Send_1: send(ch, i);
        Send_2: wait_sent(ch);
    end while;
    close(ch);
end process;

fair process Receiver = "receiver"
variable j = 0;
begin Receive:
    while TRUE do
        recv(j, ch);
        if j /= NULL then
            recvd := Append(recvd, j);
        else
            goto Done;
        end if;
    end while;
end process;

end algorithm; *)                             
\* BEGIN TRANSLATION
VARIABLES sent, recvd, ch, nextId, pc

(* define statement *)
Success == <>[](sent = recvd)

VARIABLES i, j

vars == << sent, recvd, ch, nextId, pc, i, j >>

ProcSet == {"sender"} \cup {"receiver"}

Init == (* Global variables *)
        /\ sent = <<>>
        /\ recvd = <<>>
        /\ ch = [open |-> TRUE, sent |-> FALSE, rcvd |-> FALSE, val |-> NULL]
        /\ nextId = 1
        (* Process Sender *)
        /\ i = 0
        (* Process Receiver *)
        /\ j = 0
        /\ pc = [self \in ProcSet |-> CASE self = "sender" -> "Send"
                                        [] self = "receiver" -> "Receive"]

Send == /\ pc["sender"] = "Send"
        /\ IF nextId \in 1..MaxMsg
              THEN /\ /\ i' = nextId
                      /\ nextId' = nextId + 1
                      /\ sent' = Append(sent, nextId)
                   /\ pc' = [pc EXCEPT !["sender"] = "Send_1"]
                   /\ ch' = ch
              ELSE /\ Assert(ch.open, 
                             "Failure of assertion at line 38, column 5 of macro called at line 50, column 5.")
                   /\ ch' = [ch EXCEPT !.open = FALSE]
                   /\ pc' = [pc EXCEPT !["sender"] = "Done"]
                   /\ UNCHANGED << sent, nextId, i >>
        /\ UNCHANGED << recvd, j >>

Send_1 == /\ pc["sender"] = "Send_1"
          /\ Assert(ch.open, 
                    "Failure of assertion at line 16, column 5 of macro called at line 47, column 17.")
          /\ ~ch.sent
          /\ ch' = [ch EXCEPT !.val = i,
                              !.sent = TRUE]
          /\ pc' = [pc EXCEPT !["sender"] = "Send_2"]
          /\ UNCHANGED << sent, recvd, nextId, i, j >>

Send_2 == /\ pc["sender"] = "Send_2"
          /\ ch.sent /\ ch.rcvd
          /\ ch' = [ch EXCEPT !.sent = FALSE,
                              !.rcvd = FALSE]
          /\ pc' = [pc EXCEPT !["sender"] = "Send"]
          /\ UNCHANGED << sent, recvd, nextId, i, j >>

Sender == Send \/ Send_1 \/ Send_2

Receive == /\ pc["receiver"] = "Receive"
           /\ ~ch.open \/ (ch.sent /\ ~ch.rcvd)
           /\ IF ~ch.open
                 THEN /\ j' = NULL
                      /\ ch' = ch
                 ELSE /\ /\ ch' = [ch EXCEPT !.val = NULL,
                                             !.rcvd = TRUE]
                         /\ j' = ch.val
           /\ IF j' /= NULL
                 THEN /\ recvd' = Append(recvd, j')
                      /\ pc' = [pc EXCEPT !["receiver"] = "Receive"]
                 ELSE /\ pc' = [pc EXCEPT !["receiver"] = "Done"]
                      /\ recvd' = recvd
           /\ UNCHANGED << sent, nextId, i >>

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
