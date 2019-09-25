include "../../../Trusted/Spec/Apps/Notary/Notary_spec.dfy"
include "../../Libraries/BigNum/BigNum.dfy"
include "../../Libraries/BigNum/BigNatBitCount.dfy"
include "../../Libraries/Crypto/RSA/RSA.dfy"
include "../../Libraries/Crypto/RSA/KeyGen.dfy"
include "../../Libraries/Crypto/RSA/rfc4251impl.dfy"

method {:axiom} DetermineIfPublicKeyIsWellformed (key:RSAPublicKey) returns (success:bool)
    ensures if WellformedPublicKey(key) then success == WellformedRSAPubKeySpec(PubKeyToSpec(key)) else success == false;

//////////////////////////////////////////////////////////////////////////
// Implementing NotaryState with NotaryStateImpl
//////////////////////////////////////////////////////////////////////////

datatype NotaryStateImpl = NotaryStateImplConstructor(notary_key_pair:RSAKeyPair, counter:BigNat);

function NotaryStateImplToSpec (s:NotaryStateImpl):NotaryState
{
    NotaryStateConstructor(if WellformedKeyPair(s.notary_key_pair) then
                               KeyPairToSpec(s.notary_key_pair)
                           else
                               RSAKeyPairSpec_c(RSAPublicKeySpec_c(0, 0), 0),
                           if WellformedBigNat(s.counter) then I(s.counter) else 0)
}

predicate NotaryStateImplValid (s:NotaryStateImpl)
{
    WellformedKeyPair(s.notary_key_pair) && WellformedBigNat(s.counter) && ImplKeyPairSize(s.notary_key_pair) >= 286 &&
    (ImplKeyPairSize(s.notary_key_pair) % 4 == 0) // TODO -- Remove this once Jon fixes HashedSign not to require this
}

//////////////////////////////////////////////////////////////////////////
// Exported methods
//////////////////////////////////////////////////////////////////////////

method NotaryInitialize () returns (out_state:NotaryStateImpl)
    ensures NotaryInitializeValid(NotaryStateImplToSpec(out_state));
    ensures NotaryStateImplValid(out_state);
{
    lemma_2toX();
    reveal_power2();
    var notary_key_pair := RSAKeyGen(2304);
    assert ImplKeyPairSize(notary_key_pair) >= 286;
    assume ImplKeyPairSize(notary_key_pair) % 4 == 0; // TODO - After Jon fixes HashedSign to not require this, remove this assumption.
    var zero := MakeSmallLiteralBigNat(0);
    out_state := NotaryStateImplConstructor(notary_key_pair, zero);
}

method {:timeLimit 80} NotaryAdvanceCounter (in_state:NotaryStateImpl, message:seq<int>)
                                            returns (out_state:NotaryStateImpl, error_code:int,
                                                     notary_statement:seq<int>, notary_attestation:seq<int>)
    requires NotaryStateImplValid(in_state);
    requires ByteSeq(message);
    ensures NotaryStateImplValid(out_state);
    ensures NotaryAdvanceCounterValid(NotaryStateImplToSpec(in_state), NotaryStateImplToSpec(out_state),
                                      message, error_code, notary_statement, notary_attestation);
    ensures Word32(error_code);
    ensures Word32(|notary_statement|);
    ensures Word32(|notary_attestation|);
{
    lemma_2toX();
    reveal_power2();

    var one := MakeSmallLiteralBigNat(1);
    var new_counter := BigNatAdd(in_state.counter, one);

    var modest := IsModestBigNat(new_counter);
    if !modest {
        error_code := 1;
        out_state := in_state;
        notary_statement := [];
        notary_attestation := [];
        return;
    }

    var counter_encoding := rfc4251_encode_mpint(new_counter);
    notary_statement := [34] + counter_encoding + message;
    ghost var padded_msg:seq<int>;
    var success:bool;

    if |notary_statement| > 0xFFFFFFFF {
        error_code := 2;
        out_state := in_state;
        notary_statement := [];
        notary_attestation := [];
        return;
    }

    assert IsByte(34);
    assert ByteSeq(notary_statement);
    assert |notary_statement| <= 0xFFFFFFFF < power2(61);
    notary_attestation := HashedSign(in_state.notary_key_pair, notary_statement);

    assume Word32(|notary_attestation|); // TODO - Remove this once Jon bounds size of signature

    error_code := 0;
    out_state := NotaryStateImplConstructor(in_state.notary_key_pair, new_counter);
    Lemma_NotaryCounterAdvanceStatementValid(notary_statement, NotaryStateImplToSpec(out_state).counter, message, counter_encoding);
    assert NotaryCounterAdvanceStatementValid(notary_statement, NotaryStateImplToSpec(out_state).counter, message);
}

lemma Lemma_NotaryCounterAdvanceStatementValid (statement:seq<int>, new_counter_value:nat, message:seq<int>, counter_encoding:seq<int>)
    requires ByteSeq(message);
    requires rfc4251_mpint_encoding(counter_encoding, new_counter_value);
    requires statement == [34] + counter_encoding + message;
    ensures NotaryCounterAdvanceStatementValid(statement, new_counter_value, message);
{
}
