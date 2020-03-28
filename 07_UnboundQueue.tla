------------------------------- MODULE 07_UnboundQueue -----------------------
EXTENDS Sequences, Integers, TLC

CONSTANT NULL, MaxMsg

Data == 1..MaxMsg

LOCAL INSTANCE Channels WITH Data <- Data

(*--algorithm UnboundQueue
variables 
    inpCh = MakeChan,
    outCh = MakeChan,
    sent = <<>>,
    recvd = <<>>;

define
    Success == <>[](sent = recvd)
end define;

macro send(ch, msg) begin await MaySend(ch); ch := UpdateSend(ch, msg); end macro;
macro wait_sent(ch) begin await Sent(ch); ch := UpdateSent(ch); end macro;
macro recv(var, ch)
begin await MayReceive(ch);
    if ~ch.open then var := NULL;
    else var := ch.val || ch := UpdateReceived(ch); end if;
end macro;
macro close(ch) begin assert MayClose(ch); ch := UpdateClose(ch); end macro;

fair process Producer = "producer"
variable id = 1, i = NULL;
begin Produce:
    while id \in 1..MaxMsg do
        i := id || sent := Append(sent, id) || id := id + 1;
        Produce_1: send(inpCh, i);
        Produce_2: wait_sent(inpCh);
    end while;
    close(inpCh);
end process;   

fair process Consumer = "consumer"
variable j = NULL;
begin Consume:
    while TRUE do 
        recv(j, outCh);
        Consumer_1: if j /= NULL then
            recvd := Append(recvd, j);
        else    
            goto Done;
        end if;
    end while;
end process;

fair process Buffer = "buffer"
variable k = NULL, buffer = <<>>,
         exit = FALSE;
begin BufferProcess:
  while TRUE do
  either
      when ~exit;
      recv(k, inpCh);
    Buffer_1:
      if k /= NULL then
        buffer := Append(buffer, k);
      else
        exit := TRUE;
      end if;            
    or
      when Len(buffer) > 0;
    Buffer_2:
      send(outCh, Head(buffer));
    Buffer_3:
      wait_sent(outCh);
      buffer := Tail(buffer);
    or
      when Len(buffer) = 0 /\ exit;
      close(outCh);
      goto Done;
    end either;
  end while;
end process;  

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES inpCh, outCh, sent, recvd, pc

(* define statement *)
Success == <>[](sent = recvd)

VARIABLES id, i, j, k, buffer, exit

vars == << inpCh, outCh, sent, recvd, pc, id, i, j, k, buffer, exit >>

ProcSet == {"producer"} \cup {"consumer"} \cup {"buffer"}

Init == (* Global variables *)
        /\ inpCh = MakeChan
        /\ outCh = MakeChan
        /\ sent = <<>>
        /\ recvd = <<>>
        (* Process Producer *)
        /\ id = 1
        /\ i = NULL
        (* Process Consumer *)
        /\ j = NULL
        (* Process Buffer *)
        /\ k = NULL
        /\ buffer = <<>>
        /\ exit = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = "producer" -> "Produce"
                                        [] self = "consumer" -> "Consume"
                                        [] self = "buffer" -> "BufferProcess"]

Produce == /\ pc["producer"] = "Produce"
           /\ IF id \in 1..MaxMsg
                 THEN /\ /\ i' = id
                         /\ id' = id + 1
                         /\ sent' = Append(sent, id)
                      /\ pc' = [pc EXCEPT !["producer"] = "Produce_1"]
                      /\ inpCh' = inpCh
                 ELSE /\ Assert(MayClose(inpCh), 
                                "Failure of assertion at line 28, column 23 of macro called at line 38, column 5.")
                      /\ inpCh' = UpdateClose(inpCh)
                      /\ pc' = [pc EXCEPT !["producer"] = "Done"]
                      /\ UNCHANGED << sent, id, i >>
           /\ UNCHANGED << outCh, recvd, j, k, buffer, exit >>

Produce_1 == /\ pc["producer"] = "Produce_1"
             /\ MaySend(inpCh)
             /\ inpCh' = UpdateSend(inpCh, i)
             /\ pc' = [pc EXCEPT !["producer"] = "Produce_2"]
             /\ UNCHANGED << outCh, sent, recvd, id, i, j, k, buffer, exit >>

Produce_2 == /\ pc["producer"] = "Produce_2"
             /\ Sent(inpCh)
             /\ inpCh' = UpdateSent(inpCh)
             /\ pc' = [pc EXCEPT !["producer"] = "Produce"]
             /\ UNCHANGED << outCh, sent, recvd, id, i, j, k, buffer, exit >>

Producer == Produce \/ Produce_1 \/ Produce_2

Consume == /\ pc["consumer"] = "Consume"
           /\ MayReceive(outCh)
           /\ IF ~outCh.open
                 THEN /\ j' = NULL
                      /\ outCh' = outCh
                 ELSE /\ /\ j' = outCh.val
                         /\ outCh' = UpdateReceived(outCh)
           /\ pc' = [pc EXCEPT !["consumer"] = "Consumer_1"]
           /\ UNCHANGED << inpCh, sent, recvd, id, i, k, buffer, exit >>

Consumer_1 == /\ pc["consumer"] = "Consumer_1"
              /\ IF j /= NULL
                    THEN /\ recvd' = Append(recvd, j)
                         /\ pc' = [pc EXCEPT !["consumer"] = "Consume"]
                    ELSE /\ pc' = [pc EXCEPT !["consumer"] = "Done"]
                         /\ recvd' = recvd
              /\ UNCHANGED << inpCh, outCh, sent, id, i, j, k, buffer, exit >>

Consumer == Consume \/ Consumer_1

BufferProcess == /\ pc["buffer"] = "BufferProcess"
                 /\ \/ /\ ~exit
                       /\ MayReceive(inpCh)
                       /\ IF ~inpCh.open
                             THEN /\ k' = NULL
                                  /\ inpCh' = inpCh
                             ELSE /\ /\ inpCh' = UpdateReceived(inpCh)
                                     /\ k' = inpCh.val
                       /\ pc' = [pc EXCEPT !["buffer"] = "Buffer_1"]
                       /\ outCh' = outCh
                    \/ /\ Len(buffer) > 0
                       /\ pc' = [pc EXCEPT !["buffer"] = "Buffer_2"]
                       /\ UNCHANGED <<inpCh, outCh, k>>
                    \/ /\ Len(buffer) = 0 /\ exit
                       /\ Assert(MayClose(outCh), 
                                 "Failure of assertion at line 28, column 23 of macro called at line 76, column 7.")
                       /\ outCh' = UpdateClose(outCh)
                       /\ pc' = [pc EXCEPT !["buffer"] = "Done"]
                       /\ UNCHANGED <<inpCh, k>>
                 /\ UNCHANGED << sent, recvd, id, i, j, buffer, exit >>

Buffer_1 == /\ pc["buffer"] = "Buffer_1"
            /\ IF k /= NULL
                  THEN /\ buffer' = Append(buffer, k)
                       /\ exit' = exit
                  ELSE /\ exit' = TRUE
                       /\ UNCHANGED buffer
            /\ pc' = [pc EXCEPT !["buffer"] = "BufferProcess"]
            /\ UNCHANGED << inpCh, outCh, sent, recvd, id, i, j, k >>

Buffer_2 == /\ pc["buffer"] = "Buffer_2"
            /\ MaySend(outCh)
            /\ outCh' = UpdateSend(outCh, (Head(buffer)))
            /\ pc' = [pc EXCEPT !["buffer"] = "Buffer_3"]
            /\ UNCHANGED << inpCh, sent, recvd, id, i, j, k, buffer, exit >>

Buffer_3 == /\ pc["buffer"] = "Buffer_3"
            /\ Sent(outCh)
            /\ outCh' = UpdateSent(outCh)
            /\ buffer' = Tail(buffer)
            /\ pc' = [pc EXCEPT !["buffer"] = "BufferProcess"]
            /\ UNCHANGED << inpCh, sent, recvd, id, i, j, k, exit >>

Buffer == BufferProcess \/ Buffer_1 \/ Buffer_2 \/ Buffer_3

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Producer \/ Consumer \/ Buffer
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Producer)
        /\ WF_vars(Consumer)
        /\ WF_vars(Buffer)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Mar 03 14:16:55 MSK 2020 by growler
\* Created Mon Mar 02 09:59:39 MSK 2020 by growler
