include "Message.i.dfy"



datatype Node = Node_c(token:bool, value:nat, seqnum:nat);

static predicate Node_Init(s:Node, hasToken:bool)
{
    s.token==hasToken && (hasToken==>s.value==0)
}

static predicate Node_Increment(s:Node, s':Node)
{
    s.token==true
    && s'.value == s'.value + 1
}

static predicate Node_ReleaseToken(s:Node, s':Node, msg:Message)
{
    s.token==true
    && s'.token==false
    && msg.M_TransferToken?
    && msg.seqnum==s.seqnum + 1
    && msg.value==s.value
    && s'.seqnum==s.seqnum
}

static predicate Node_AcceptToken(s:Node, s':Node, msg:Message)
{
    s.token==false
    && msg.M_TransferToken?
    && s.seqnum < msg.seqnum
    && s'.token==true
    && s'.seqnum==msg.seqnum
    && s'.value==msg.value
}

static predicate Node_Unchanged(s:Node, s':Node)
{
    s == s'
}
