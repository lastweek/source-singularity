include "../../Libraries/Crypto/RSA/RSASpec.dfy"
include "../../Libraries/Util/arrays_and_seqs.dfy"
include "../../Libraries/Crypto/RSA/rfc4251.dfy"

/////////////////////////////////////////////////////
// Structures
/////////////////////////////////////////////////////

datatype NotaryState = NotaryStateConstructor(notary_key_pair:RSAKeyPairSpec, counter:nat);

/////////////////////////////////////////////////////
// Helpers
/////////////////////////////////////////////////////

predicate NotaryCounterAdvanceStatementValid (statement:seq<int>, new_counter_value:nat, message:seq<int>)
{
    exists counter_encoding:seq<int> ::
        rfc4251_mpint_encoding(counter_encoding, new_counter_value) &&
        statement == [34] /* "counter advance" */ + counter_encoding + message
}

/////////////////////////////////////////////////////
// Specifications for correct method operation
/////////////////////////////////////////////////////

// This function is used to ensure that NotaryInitialize operates correctly.
// That method is supposed to initialize the Notary state.  It should generate
// a fresh key pair, then initialize the counter to zero.

predicate NotaryInitializeValid (state:NotaryState)
{
    state.counter == 0
}

// This function is used to ensure that NotaryAdvanceCounter operates
// correctly.  That method is supposed to advance the given counter to the
// next counter value.  It should then return an attestation that the
// counter was advanced.

predicate NotaryAdvanceCounterValid (in_state:NotaryState, out_state:NotaryState, message_in:seq<int>,
                                     error_code_out:int, notary_statement_out:seq<int>, notary_attestation_out:seq<int>)
{
    if error_code_out == 0 then
        out_state.notary_key_pair == in_state.notary_key_pair &&
        out_state.counter == in_state.counter + 1 &&
        WellformedRSAKeyPairSpec(in_state.notary_key_pair) &&
        ByteSeq(message_in) &&
        ByteSeq(notary_statement_out) &&
        ByteSeq(notary_attestation_out) &&
        |ByteSeqToBoolSeq(notary_statement_out)| < power2(64) &&
        NotaryCounterAdvanceStatementValid(notary_statement_out, out_state.counter, message_in) &&
        RSASignatureRelation(in_state.notary_key_pair, notary_statement_out, notary_attestation_out)
    else
        out_state == in_state && |notary_statement_out| == 0 && |notary_attestation_out| == 0
}
