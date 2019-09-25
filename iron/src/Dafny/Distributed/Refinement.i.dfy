include "HLIncrementer.s.dfy"
include "System.i.dfy"

static predicate message_sane(s:System, msg:Message)
{
    0 <= msg.recipient < |s.nodes|
}

static predicate network_sane(s:System)
{
    forall msg :: msg in s.network.msgs ==> message_sane(s, msg)
}

static predicate Inv_i_exclusively_holds_token(s:System, i:nat)
    
{
    0<=i<|s.nodes|
    && s.nodes[i].token==true
    && (forall j :: 0<=j<|s.nodes| && j!=i
            ==> s.nodes[j].token==false)
}

static predicate Inv_msg_received(s:System, msg:Message)
    requires msg in s.network.msgs;
    requires network_sane(s);
    requires message_sane(s, msg);
{
    msg.seqnum <= s.nodes[msg.recipient].seqnum
}

static predicate Inv_nobody_holds_token(s:System)
{
    forall j :: 0<=j<|s.nodes| ==> s.nodes[j].token==false
}

static predicate Inv_msg_exclusively_unreceived(s:System, msg:Message)
    requires network_sane(s);
    requires message_sane(s, msg);
{
    msg in s.network.msgs
    && message_sane(s, msg)
    && !Inv_msg_received(s, msg)
    && forall m :: m in s.network.msgs && m!=msg ==> Inv_msg_received(s, m)
}

static predicate Inv_all_messages_received(s:System)
    requires network_sane(s);
{
    forall m :: m in s.network.msgs ==> Inv_msg_received(s, m)
}

static predicate Inv_token_has_max_seqnum(s:System, i:nat)
    requires 0<=i<|s.nodes|;
{
    forall j :: 0<=j<|s.nodes| && j!=i ==>
        s.nodes[i].seqnum > s.nodes[j].seqnum
}

static predicate Inv_token_held_i(s:System, i:nat)
    requires network_sane(s);
{
    Inv_i_exclusively_holds_token(s, i)
    && Inv_all_messages_received(s)
    && Inv_token_has_max_seqnum(s, i)
}

static predicate Inv_token_held(s:System)
    requires network_sane(s);
{
    exists i:nat :: Inv_token_held_i(s, i)
}

static predicate Inv_outstanding_msg_has_max_seqnum(s:System, msg:Message)
{
    forall j :: 0<=j<|s.nodes| ==> msg.seqnum > s.nodes[j].seqnum
}

static predicate Inv_msg_outstanding_msg(s:System, msg:Message)
    requires network_sane(s);
{
    Inv_nobody_holds_token(s)
    && message_sane(s, msg)
    && Inv_msg_exclusively_unreceived(s, msg)
    && Inv_outstanding_msg_has_max_seqnum(s, msg)
}

static predicate Inv_msg_outstanding(s:System)
    requires network_sane(s);
{
    exists msg:Message :: Inv_msg_outstanding_msg(s, msg)
}

static predicate Inv(s:System)
{
    network_sane(s)
    && ( Inv_token_held(s)
        || Inv_msg_outstanding(s) )
}



static function Network_reduce(n:Network, i:nat) : Network
{
    var reduced := set x | x in n.msgs && x.recipient!=i :: x;
    Network_c(reduced)
}

static function System_cdr(s:System) : System
    requires 0<|s.nodes|;
{
    System_c(s.nodes[..|s.nodes|-1], Network_reduce(s.network, |s.nodes|-1))
}

static predicate is_unreceived_message(s:System, msg:Message)
{
    msg in s.network.msgs
    && network_sane(s)
    && message_sane(s, msg)
    && !Inv_msg_received(s, msg)
}

static function select(msgs:set<Message>) : Message
    requires |msgs|>0;
{
    var msg :| msg in msgs; msg
}

lemma lemma_select(msgs:set<Message>, msg:Message)
    requires msgs == {msg};
    ensures select(msgs) == msg;
{
}

static function System_Value_from_message(s:System) : nat
    requires exists msg :: is_unreceived_message(s, msg);
{
    var mset := set x | x in s.network.msgs && is_unreceived_message(s, x) :: x;
    var msg :| is_unreceived_message(s, msg); assert msg in mset;   // OBSERVE set nonempty
    select(mset).value
}

static function System_Value(s:System) : nat
    decreases |s.nodes|;
{
    
    
    if (exists msg :: is_unreceived_message(s, msg))
        then System_Value_from_message(s)
    else if (|s.nodes|==0)
        then 17
    else if (s.nodes[|s.nodes|-1].token)
        then s.nodes[|s.nodes|-1].value
    else
        System_Value(System_cdr(s))
}

static function refinement(s:System) : HLIncrementer.State
{
    HLIncrementer.State_c(System_Value(s))
}

lemma lemma_next_preserves_network_sane(s:System, s':System)
    requires network_sane(s);
    requires System_Next(s,s');
    ensures network_sane(s');
{
    if (System_Increment(s,s'))
    {
        assert network_sane(s');
    }
    else if (System_SendToken(s,s'))
    {
        assert network_sane(s');
    }
    else if (System_ReceiveToken(s,s'))
    {
        assert network_sane(s');
    }
    else
    {
        assert false;
    }
}

lemma lemma_next_preserves_Inv(s:System, s':System)
    requires Inv(s);
    requires System_Next(s, s');
    ensures Inv(s');
{
    lemma_next_preserves_network_sane(s,s');

    if (System_Increment(s,s'))
    {
        assert Inv(s');
    }
    else if (System_SendToken(s,s'))
    {
        var f:nat,msg:Message :| System_SendToken_i(s, s', f, msg);
        assert msg.seqnum >= s'.nodes[msg.recipient].seqnum;
        assert !Inv_msg_received(s', msg);
        assert Inv_msg_exclusively_unreceived(s', msg);

        assert Inv_nobody_holds_token(s');
        assert message_sane(s, msg);
        assert Inv_msg_exclusively_unreceived(s', msg);
        forall (j | 0<=j<|s.nodes|)
            ensures msg.seqnum > s.nodes[j].seqnum;
        {
            if (j==f)
            {
                assert msg.seqnum > s.nodes[j].seqnum;
            }
            else
            {
                assert msg.seqnum > s.nodes[j].seqnum;
            }
        }
        assert Inv_outstanding_msg_has_max_seqnum(s', msg);

        assert Inv_msg_outstanding_msg(s', msg);
        assert Inv_msg_outstanding(s');
        assert Inv(s');
    }
    else if (System_ReceiveToken(s,s'))
    {
        var msg :| System_ReceiveToken_i(s, s', msg);
        var i := msg.recipient;
        assert Inv_i_exclusively_holds_token(s', i);
        assert Inv_all_messages_received(s');
        assert Inv_token_has_max_seqnum(s', i);
        assert Inv_token_held_i(s', i); 
        assert Inv(s');
    }
    else
    {
        assert false;
    }
}

lemma lemma_System_cdr_preserves_network_properties(s:System)
    requires 0<|s.nodes|;
    ensures network_sane(s) && Inv_all_messages_received(s) ==>
        network_sane(System_cdr(s)) && Inv_all_messages_received(System_cdr(s));
{
    var cdr := System_cdr(s);
    assert |cdr.nodes| == |s.nodes|-1;
    if (network_sane(s) && Inv_all_messages_received(s))
    {
        forall (msg | msg in cdr.network.msgs)  
            ensures message_sane(cdr, msg);
        {
        }
    }
}

lemma lemma_value_from_message(s:System, msg:Message)
    requires network_sane(s);
    requires message_sane(s, msg);
    requires Inv_msg_exclusively_unreceived(s, msg);
    ensures System_Value(s) == msg.value;
{
    assert is_unreceived_message(s, msg);
    assert (exists msg :: is_unreceived_message(s, msg));

    var mset2 := set x | x in s.network.msgs && is_unreceived_message(s, x) :: x;
    var msg2 :| is_unreceived_message(s, msg2); assert msg2 in mset2;   // OBSERVE set nonempty


    assert select(mset2).value ==
    (
    var mset := set x | x in s.network.msgs && is_unreceived_message(s, x) :: x;
    var msg :| is_unreceived_message(s, msg); assert msg in mset;   // OBSERVE set nonempty
    select(mset).value
    );


    var yset := set x | x in s.network.msgs && is_unreceived_message(s, x) :: x;
    assert mset2 == yset;
    assert mset2 == {msg};
    lemma_select(mset2, msg);
    calc {
        System_Value(s);
        System_Value_from_message(s);
        select(mset2).value;
        msg.value;
    }
}

lemma lemma_value_from_token(s:System, i:nat)
    requires Inv_i_exclusively_holds_token(s, i);
    requires network_sane(s);
    requires Inv_all_messages_received(s);
    ensures System_Value(s) == s.nodes[i].value;
    decreases |s.nodes|;
{
    if (|s.nodes|==0)
    {
        assert false;
    }
    else if (|s.nodes|==1)
    {
        assert !(exists msg :: is_unreceived_message(s, msg));
        assert System_Value(s) == s.nodes[i].value;
    }
    else if (i==|s.nodes|-1)
    {
        assert System_Value(s) == s.nodes[i].value;
    }
    else
    {
        lemma_System_cdr_preserves_network_properties(s);
        lemma_value_from_token(System_cdr(s), i);
    }
}

lemma lemma_init_refinement(s:System)
    ensures System_Init(s) ==>
        ( HLIncrementer.Init(refinement(s))
          && Inv(s) );
{








}

lemma lemma_next_refinement(s:System,s':System)
    ensures (System_Next(s,s') && Inv(s))
        ==>
        (HLIncrementer.Next(refinement(s), refinement(s'))
        || HLIncrementer.Unchanged(refinement(s), refinement(s')));
{
    if (System_Next(s,s') && Inv(s))
    {
        if (System_Increment(s,s'))
        {
            var i:nat :| Inv_i_exclusively_holds_token(s, i);
            lemma_value_from_token(s, i);
            lemma_next_preserves_Inv(s, s');

            var i':nat :| Inv_i_exclusively_holds_token(s', i');
            lemma_value_from_token(s', i');
        }
        else if (System_SendToken(s,s'))
        {
            var f:nat,msg:Message :| System_SendToken_i(s, s', f, msg);
            lemma_value_from_message(s', msg);
            lemma_value_from_token(s, f);
        }
        else if (System_ReceiveToken(s,s'))
        {
            var msg:Message :| System_ReceiveToken_i(s, s', msg);
            lemma_value_from_message(s, msg);
            lemma_value_from_token(s', msg.recipient);
        }
        else
        {
            assert false;
        }
    }
}

//    
//    










//        


