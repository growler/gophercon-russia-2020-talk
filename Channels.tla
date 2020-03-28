------------------------------- MODULE Channels ------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
CONSTANT Data
CONSTANT NULL

ChannelTypeInvariant(chan) == chan \in [
    open: BOOLEAN,
    sent: BOOLEAN,
    rcvd: BOOLEAN,
    val:  Data \union {NULL}
]

MakeChan == [
    open |-> TRUE,
    sent |-> FALSE,
    rcvd |-> FALSE,
    val  |-> NULL
]

MaySend(chan) == /\ Assert(chan.open, "send on closed channel")
                 /\ ~chan.sent    
UpdateSend(chan, msg) == [chan EXCEPT !.val = msg, !.sent = TRUE]
    
Sent(chan) == /\ Assert(chan.open, "send on closed channel")
              /\ chan.sent 
              /\ chan.rcvd
UpdateSent(chan) == [chan EXCEPT !.sent = FALSE, !.rcvd = FALSE]

MayReceive(chan) == \/ ~chan.open
                    \/ /\ chan.sent 
                       /\ ~chan.rcvd
UpdateReceived(chan) == [chan EXCEPT !.val = NULL, !.rcvd = TRUE]

MayClose(chan) == Assert(chan.open, "close on closed channel")
UpdateClose(chan) == [chan EXCEPT !.open = FALSE]

(*--algorithm Channels

macro send(ch, var)
begin await MaySend(ch); ch := UpdateSend(ch, msg);
end macro;

macro sent(ch)
begin await Sent(chan); ch := UpdateSent(ch);
end macro;

macro recv(var, ch)
begin await MayReceive(chan);
    if ~ch.open then var := NULL;
    else var := ch.val || ch := UpdateReceived(ch); end if;
end macro;
    
end algorithm;*)

=============================================================================
\* Modification History
\* Last modified Tue Mar 03 14:16:55 MSK 2020 by growler
\* Created Mon Mar 02 09:59:39 MSK 2020 by growler
