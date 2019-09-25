include "../../../Trusted/Spec/Apps/TrInc/TrInc_spec.dfy"
include "../../Libraries/BigNum/BigNum.dfy"
include "../../Libraries/Crypto/RSA/RSA.dfy"
include "../../Libraries/Crypto/RSA/KeyGen.dfy"

method {:axiom} DetermineIfPublicKeyIsWellformed (key:RSAPublicKey) returns (success:bool)
    ensures if WellformedPublicKey(key) then success == WellformedRSAPubKeySpec(PubKeyToSpec(key)) else success == false;

function RequirementFreePubKeyToSpec (public_key:RSAPublicKey) : RSAPubKeySpec
{
    if WellformedPublicKey(public_key) then PubKeyToSpec(public_key) else RSAPublicKeySpec_c(0, 0)
}

//////////////////////////////////////////////////////////////////////////
// Implementing TrIncCounter with TrIncCounterImpl
//////////////////////////////////////////////////////////////////////////

datatype TrIncCounterImpl = TrIncCounterImplConstructor(public_key:RSAPublicKey, counter_value:BigNat);

function TrIncCounterImplToSpec (c:TrIncCounterImpl):TrIncCounter
{
    TrIncCounterConstructor(RequirementFreePubKeyToSpec(c.public_key),
                            if WellformedBigNat(c.counter_value) then I(c.counter_value) else 0)
}

function TrIncCounterImplSeqToSpec (s:seq<TrIncCounterImpl>):seq<TrIncCounter>
{
    if |s| == 0 then
        []
    else
        TrIncCounterImplSeqToSpec(s[..|s|-1]) + [TrIncCounterImplToSpec(s[|s|-1])]
}

lemma Lemma_TrIncCounterImplSeqToSpecPreservesLength (s_impl:seq<TrIncCounterImpl>, s_ghost:seq<TrIncCounter>)
    requires s_ghost == TrIncCounterImplSeqToSpec(s_impl);
    ensures |s_ghost| == |s_impl|;
    ensures forall i :: 0 <= i < |s_ghost| ==> s_ghost[i].public_key == RequirementFreePubKeyToSpec(s_impl[i].public_key);
    decreases |s_impl|;
{
    if |s_impl| > 0 {
        assert s_ghost == TrIncCounterImplSeqToSpec(s_impl[..|s_impl|-1]) + [TrIncCounterImplToSpec(s_impl[|s_impl|-1])];
        Lemma_TrIncCounterImplSeqToSpecPreservesLength(s_impl[..|s_impl|-1], s_ghost[..|s_ghost|-1]);
    }
}

//////////////////////////////////////////////////////////////////////////
// Implementing TrIncState with TrIncStateImpl
//////////////////////////////////////////////////////////////////////////

datatype TrIncStateImpl = TrIncStateImplConstructor(TrInc_key_pair:RSAKeyPair, counters:seq<TrIncCounterImpl>);

function TrIncStateImplToSpec (s:TrIncStateImpl):TrIncState
{
    TrIncStateConstructor(if WellformedKeyPair(s.TrInc_key_pair) then
                             KeyPairToSpec(s.TrInc_key_pair)
                         else
                             RSAKeyPairSpec_c(RSAPublicKeySpec_c(0, 0), 0),
                         TrIncCounterImplSeqToSpec(s.counters))
}

predicate TrIncStateImplValid (s:TrIncStateImpl)
{
    TrIncStateValid(TrIncStateImplToSpec(s)) &&
    WellformedKeyPair(s.TrInc_key_pair) &&
    ImplKeyPairSize(s.TrInc_key_pair) >= 286 &&
    (ImplKeyPairSize(s.TrInc_key_pair) % 4 == 0) // TODO -- Remove this once Jon fixes HashedSign not to require this    
}

//////////////////////////////////////////////////////////////////////////
// Exported methods
//////////////////////////////////////////////////////////////////////////

method TrIncInitialize () returns (out_state:TrIncStateImpl)
    ensures TrIncInitializeValid(TrIncStateImplToSpec(out_state));
    ensures TrIncStateImplValid(out_state);
{
    lemma_2toX();
    reveal_power2();
    var TrInc_key_pair := RSAKeyGen(2304);
    assert ImplKeyPairSize(TrInc_key_pair) >= 286;
    assume ImplKeyPairSize(TrInc_key_pair) % 4 == 0; // TODO - After Jon fixes HashedSign to not require this, remove this assumption.

    out_state := TrIncStateImplConstructor(TrInc_key_pair, []);
}

method TrIncCreateCounter (in_state:TrIncStateImpl, public_key:RSAPublicKey)
                          returns (out_state:TrIncStateImpl, error_code:int, counter_index:nat)
    requires TrIncStateImplValid(in_state);
    ensures TrIncCreateCounterValid(TrIncStateImplToSpec(in_state), TrIncStateImplToSpec(out_state), RequirementFreePubKeyToSpec(public_key), 
                                    error_code, counter_index);
    ensures TrIncStateImplValid(out_state);
{
    out_state := in_state;
    counter_index := 0;

    lemma_2toX();
    Lemma_TrIncCounterImplSeqToSpecPreservesLength(in_state.counters, TrIncStateImplToSpec(in_state).counters);
    if |in_state.counters| >= 0xFFFFFFFF {
        error_code := 1;
        return;
    }

    var wellformed := DetermineIfPublicKeyIsWellformed(public_key);
    if !wellformed {
        error_code := 2;
        return;
    }
    assert WellformedPublicKey(public_key);
    assert WellformedRSAPubKeySpec(PubKeyToSpec(public_key));

    error_code := 0;
    var zero := MakeSmallLiteralBigNat(0);
    var new_counter := TrIncCounterImplConstructor(public_key, zero);
    out_state := TrIncStateImplConstructor(in_state.TrInc_key_pair, in_state.counters + [new_counter]);
    counter_index := |out_state.counters| - 1;
    Lemma_TrIncCounterImplSeqToSpecPreservesLength(out_state.counters, TrIncStateImplToSpec(out_state).counters);
}

/*

method TrIncAdvanceCounter (in_state:TrIncStateImpl, counter_index:nat, new_counter_value:BigNat,
                            message:seq<int>, message_attestation:seq<int>)
                           returns (out_state:TrIncStateImpl, error_code:int, TrInc_statement:seq<int>, TrInc_attestation:seq<int>)
    requires TrIncStateImplValid(in_state);
    requires WellformedBigNat(new_counter_value);
    requires ByteSeq(message);
    requires ByteSeq(message_attestation);
    ensures TrIncAdvanceCounterValid(TrIncStateImplToSpec(in_state), TrIncStateImplToSpec(out_state),
                                     counter_index, I(new_counter_value), message, message_attestation,
                                     error_code, TrInc_statement, TrInc_attestation);
    ensures TrIncStateImplValid(in_state);
    ensures Word32(error_code);
    ensures Word32(|TrInc_statement|);
    ensures Word32(|TrInc_attestation|);
{
    out_state := in_state;
    TrInc_statement := [];
    TrInc_attestation := [];

    if counter_index < 0 || counter_index >= |in_state.counters| {
        error_code := 1;
        return;
    }

    var too_small := BigNatLt(new_counter_value, in_state.counters[counter_index].counter_value);
    if too_small {
        error_code := 2;
        return;
    }
    assert I(new_counter_value) >= I(in_state_counters[counter_index].counter_value);

    var modest := IsModestBigNat(new_counter);
    if !modest {
        error_code := 3;
        return;
    }

    var signature_ok := HashedVerify(in_state.counters[counter_index].public_key, message, message_attestation);
    if !signature_ok {
        error_code := 4;
        return;
    }

    var old_counter_encoding := rfc4251_encode_mpint(in_state.counters[counter_index].counter_value);
    var new_counter_encoding := rfc4251_encode_mpint(new_counter);
    TrInc_statement := [34] + old_counter_encoding + new_counter_encoding + message;
    ghost var padded_msg:seq<int>;
    var success:bool;

    if |TrInc_statement| > 0xFFFFFFFF {
        error_code := 5;
        TrInc_statement := [];
        return;
    }

    assert IsByte(34);
    assert ByteSeq(TrInc_statement);
    assert |TrInc_statement| <= 0xFFFFFFFF < power2(61);
    TrInc_attestation := HashedSign(in_state.TrInc_key_pair, TrInc_statement);

    assume Word32(|TrInc_attestation|); // TODO - Remove this once Jon bounds size of signature

    error_code := 0;
    out_state := UpdateStateByModifyingCounterValue(in_state, counter_index, new_counter_value);
    Lemma_UpdatingStateEnsuresProperUpdatesToSpec(in_state, out_state, counter_index, new_counter_value);
    Lemma_TrIncCounterAdvanceStatementValid(TrInc_statement, counter_index,
                                            I(in_state.counters[counter_index].counter_value), I(new_counter_value),
                                            old_counter_encoding, new_counter_encoding, message);
     assert TrIncCounterAdvanceStatementValid(TrInc_statement, TrIncStateImplToSpec(out_state).counter, message);
}

*/

lemma Lemma_TrIncCounterAdvanceStatementValid (statement:seq<int>, counter_index:nat, old_counter_value:nat, new_counter_value:nat,
                                               old_counter_encoding:seq<int>, new_counter_encoding:seq<int>, message:seq<int>)
    requires ByteSeq(message);
    requires rfc4251_mpint_encoding(old_counter_encoding, old_counter_value);
    requires rfc4251_mpint_encoding(new_counter_encoding, new_counter_value);
    requires statement == [34] + old_counter_encoding + new_counter_encoding + message;
    ensures TrIncCounterAdvanceStatementValid(statement, counter_index, old_counter_value, new_counter_value, message);
{
}

method UpdateStateByModifyingCounterValue (in_state:TrIncStateImpl, counter_index:nat, new_counter_value:BigNat)
                                          returns (out_state:TrIncStateImpl)
    requires TrIncStateImplValid(in_state);
    requires 0 <= counter_index < |in_state.counters|;
    ensures out_state.TrInc_key_pair == in_state.TrInc_key_pair;
    ensures |out_state.counters| == |in_state.counters|;
    ensures forall i :: 0 <= i < |in_state.counters| && i != counter_index ==> out_state.counters[i] == in_state.counters[i];
    ensures out_state.counters[counter_index].public_key == in_state.counters[counter_index].public_key;
    ensures out_state.counters[counter_index].counter_value == new_counter_value;
{
    var counters:seq<TrIncCounterImpl> := [];
    var j:int := 0;

    while j < |in_state.counters|
        invariant 0 <= j <= |in_state.counters|;
        invariant |counters| == j;
        invariant forall i :: 0 <= i < j && i != counter_index ==> counters[i] == in_state.counters[i];
        invariant j > counter_index ==> counters[counter_index].public_key == in_state.counters[counter_index].public_key;
        invariant j > counter_index ==> counters[counter_index].counter_value == new_counter_value;
    {
        if j == counter_index {
            counters := counters + [TrIncCounterImplConstructor(in_state.counters[j].public_key, new_counter_value)];
        }
        else {
            counters := counters + [in_state.counters[j]];
        }
        j := j + 1;
    }

    out_state := TrIncStateImplConstructor(in_state.TrInc_key_pair, counters);
    Lemma_TrIncCounterImplSeqToSpecPreservesLength(counters, TrIncCounterImplSeqToSpec(counters));
}

/*

lemma Lemma_UpdatingStateEnsuresProperUpdatesToSpec (in_state:TrIncStateImpl, out_state:TrIncStateImpl,
                                                     counter_index:nat, new_counter_value:BigNat)
    requires TrIncStateImplValid(in_state);
    requires 0 <= counter_index < |in_state.counters|;
    requires out_state.TrInc_key_pair == in_state.TrInc_key_pair;
    requires |out_state.counters| == |in_state.counters|;
    requires forall i :: 0 <= i < |in_state.counters| && i != counter_index ==> out_state.counters[i] == in_state.counters[i];
    requires out_state.counters[counter_index].public_key == in_state.counters[counter_index].public_key;
    requires out_state.counters[counter_index].counter_value == new_counter_value;

    ensures TrIncStateImplToSpec(in_state).TrInc_key_pair == TrIncStateImplToSpec(out_state).TrInc_key_pair;
    ensures forall i :: 0 <= i < |in_state.counters| && i != counter_index ==>
                TrIncStateImplToSpec(out_state).counters[i] == TrIncStateImplToSpec(in_state).counters[i];
    ensures TrIncStateImplToSpec(out_state).counters[counter_index].public_key ==
            TrIncStateImplToSpec(in_state).counters[counter_index].public_key;
    ensures TrIncStateImplToSpec(out_state).counters[counter_index].counter_value == I(new_counter_value);
{
}

*/
