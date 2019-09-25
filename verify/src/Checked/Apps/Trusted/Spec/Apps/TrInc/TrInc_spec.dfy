include "../../Libraries/Crypto/RSA/RSASpec.dfy"
include "../../Libraries/Util/arrays_and_seqs.dfy"
include "../../Libraries/Crypto/RSA/rfc4251.dfy"

/////////////////////////////////////////////////////
// Structures
/////////////////////////////////////////////////////

// Each counter has an RSA public key associated with it; only users
// in possession of the corresponding private key are allowed to
// advance the counter.

datatype TrIncCounter = TrIncCounterConstructor(public_key:RSAPubKeySpec, counter_value:nat);
datatype TrIncState = TrIncStateConstructor(TrInc_key_pair:RSAKeyPairSpec, counters:seq<TrIncCounter>);

/////////////////////////////////////////////////////
// Helpers
/////////////////////////////////////////////////////

predicate TrIncStateValid (state:TrIncState)
{
    Word32(|state.counters|) &&
    (forall i :: 0 <= i < |state.counters| ==> WellformedRSAPubKeySpec(state.counters[i].public_key))
}

predicate TrIncCounterAdvanceStatementValid (statement:seq<int>, counter_index:nat, old_counter_value:nat, new_counter_value:nat,
                                             message:seq<int>)
{
    exists old_encoding:seq<int>, new_encoding:seq<int> ::
        rfc4251_mpint_encoding(old_encoding, old_counter_value) &&
        rfc4251_mpint_encoding(new_encoding, new_counter_value) &&
        statement == [34] /* "counter advance" */ + old_encoding + new_encoding + message
}

/////////////////////////////////////////////////////
// Specifications for correct method operation
/////////////////////////////////////////////////////

// This function is used to ensure that TrIncInitialize operates correctly.
// That method is supposed to initialize the TrInc state.  It should generate
// a fresh key pair, then initialize the counter set to be empty.

predicate TrIncInitializeValid (state:TrIncState)
{
    TrIncStateValid(state) &&
    |state.counters| == 0
}

// This function is used to ensure that TrIncCreateCounter operates correctly.
// That method is supposed to create a new counter with the given public key.
// It returns the index of the new counter.

predicate TrIncCreateCounterValid (in_state:TrIncState, out_state:TrIncState, public_key_in:RSAPubKeySpec,
                                   error_code_out:int, counter_index_out:nat)
{
    TrIncStateValid(out_state) &&
    if error_code_out == 0 then
        out_state.TrInc_key_pair == in_state.TrInc_key_pair &&
        out_state.counters == in_state.counters + [TrIncCounterConstructor(public_key_in, 0)] &&
        counter_index_out == |in_state.counters|
    else
        out_state == in_state && counter_index_out == 0
}

// This function is used to ensure that TrInc_advance_counter operates
// correctly.  That method is supposed to advance the given counter to the
// given new counter value.  It should then return an attestation that the
// counter was advanced.

predicate TrIncAdvanceCounterValid (in_state:TrIncState, out_state:TrIncState,
                                    counter_index_in:nat, new_counter_value_in:nat, message_in:seq<int>, message_attestation_in:seq<int>,
                                    error_code_out:int, TrInc_statement_out:seq<int>, TrInc_attestation_out:seq<int>)
    requires ByteSeq(message_in);
    requires ByteSeq(message_attestation_in);
{
    // Note that, as in the TrInc paper, it is acceptable to advance the counter to
    // the same value that it had before.  This is OK because the attestation will
    // state the old and new counter values, so the recipient of that attestation
    // can't mistake it for a non-zero counter advance.

    TrIncStateValid(out_state) &&
    if error_code_out == 0 then
        // The parameters are valid

        0 <= counter_index_in < |in_state.counters| &&
        in_state.counters[counter_index_in].counter_value <= new_counter_value_in &&
        WellformedRSAPubKeySpec(in_state.counters[counter_index_in].public_key) &&
        RSAVerificationRelation(in_state.counters[counter_index_in].public_key, message_in, message_attestation_in) &&

        // Most of the state stays the same...

        out_state.TrInc_key_pair == in_state.TrInc_key_pair &&
        |out_state.counters| == |in_state.counters| &&
        (forall i :: 0 <= i < |in_state.counters| && i != counter_index_in ==> out_state.counters[i] == in_state.counters[i]) &&
        out_state.counters[counter_index_in].public_key == in_state.counters[counter_index_in].public_key &&

        // ...except for the counter value for the counter with the given index...

        out_state.counters[counter_index_in].counter_value == new_counter_value_in &&

        // ...and an attestation is returned.

        TrIncCounterAdvanceStatementValid(TrInc_statement_out, counter_index_in, in_state.counters[counter_index_in].counter_value,
                                              new_counter_value_in, message_in) &&
        RSAVerificationRelation(in_state.TrInc_key_pair.pub, TrInc_statement_out, TrInc_attestation_out)
    else
        // Otherwise, nothing is done and no attestation is returned
        out_state == in_state && |TrInc_statement_out| == 0 && |TrInc_attestation_out| == 0
}
