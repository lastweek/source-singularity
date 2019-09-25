include "Message.i.dfy"




datatype Network = Network_c(msgs:set<Message>);

static predicate Network_ReceiveMessage(s:Network, msg:Message)
{
    msg in s.msgs
}

static predicate Network_SendMessage(s:Network, s':Network, msg:Message)
{
    s'.msgs == s.msgs + {msg}
}
