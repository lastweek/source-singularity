include "Message.i.dfy"
include "Node.i.dfy"
include "Network.i.dfy"






datatype System = System_c(nodes:seq<Node>, network:Network);

static predicate System_Init(s:System)
{
    |s.nodes|>0
    && (forall i :: 0<=i<|s.nodes| ==> Node_Init(s.nodes[i], i==|s.nodes|-1))
    && |s.network.msgs| == 0
}

static predicate System_Increment(s:System, s':System)
{
    exists t:nat ::
        |s'.nodes|==|s.nodes|
        && 0<=t<|s.nodes|
        && Node_Increment(s.nodes[t], s'.nodes[t])
        
        && (forall j :: 0<=j<|s.nodes| && j!=t ==> Node_Unchanged(s.nodes[j], s'.nodes[j]))
}

static predicate System_SendToken_i(s:System, s':System, f:nat, msg:Message)
{
    var t := msg.recipient;

    0<=f<|s.nodes|
    && 0<=t<|s.nodes|
    && |s'.nodes|==|s.nodes|
    && msg.M_TransferToken?
    && Node_ReleaseToken(s.nodes[f], s'.nodes[f], msg)
    && Network_SendMessage(s.network, s'.network, msg)
    && (forall j :: 0<=j<|s.nodes| && j!=f ==> Node_Unchanged(s.nodes[j], s'.nodes[j]))
}

static predicate System_SendToken(s:System, s':System)
{
    exists f:nat,msg:Message :: System_SendToken_i(s, s', f, msg)
}

static predicate System_ReceiveToken_i(s:System, s':System, msg:Message)
{
    var t := msg.recipient;

    0<=t<|s.nodes|
    && |s'.nodes|==|s.nodes|
    && msg.M_TransferToken?
    && Node_AcceptToken(s.nodes[t], s'.nodes[t], msg)
    && Network_ReceiveMessage(s.network, msg)
    && /* Network_Unchanged */ s.network == s'.network
    && (forall j :: 0<=j<|s.nodes| && j!=t ==> Node_Unchanged(s.nodes[j], s'.nodes[j]))
}

static predicate System_ReceiveToken(s:System, s':System)
{
    exists msg:Message :: System_ReceiveToken_i(s, s', msg)
}

static predicate System_Next(s:System, s':System)
{
    false
    || System_Increment(s,s')
    || System_SendToken(s,s')
    || System_ReceiveToken(s,s')
}

