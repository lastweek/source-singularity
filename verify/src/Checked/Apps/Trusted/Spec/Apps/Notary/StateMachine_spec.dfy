include "Notary_spec.dfy"
include "../../Libraries/Crypto/RSA/RSASpec.dfy"
include "../../Libraries/Util/arrays_and_seqs.dfy"

datatype Packet = Packet_ctor(data:seq<int>);

/////////////////////////////
// Request parsing
/////////////////////////////

datatype NotaryRequest = InvalidRequest_ctor()
                         | AdvanceCounterRequest_ctor(message:seq<int>)

predicate RequestParsedCorrectly (packet:Packet, request:NotaryRequest)
    requires ByteSeq(packet.data);
{
    if |packet.data| == 0 then
        request.InvalidRequest_ctor?
    else if packet.data[0] == 1 then
        AdvanceCounterRequestParsedCorrectly(packet, request)
    else
        request.InvalidRequest_ctor?
}

predicate AdvanceCounterRequestParsedCorrectly (packet:Packet, request:NotaryRequest)
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 1;
{
    if |packet.data| < 2 then
        request.InvalidRequest_ctor?
    else
        var message_len := packet.data[1];
        if |packet.data| < 2 + message_len then
            request.InvalidRequest_ctor?
        else
            request.AdvanceCounterRequest_ctor? &&
            request.message == packet.data[2..2+message_len]
}

/////////////////////////////
// Response parsing
/////////////////////////////

datatype NotaryResponse = NullResponse_ctor()
                          | AdvanceCounterResponse_ctor(advance_error_code:int, notary_statement:seq<int>, notary_attestation:seq<int>)

function ResponseFormedCorrectly (response:NotaryResponse, packet:Packet) : bool
    requires ByteSeq(packet.data);
{
    match response
        case NullResponse_ctor =>
            |packet.data| >= 1 && packet.data[0] == 0

        case AdvanceCounterResponse_ctor(advance_error_code, notary_statement, notary_attestation) =>
            Word32(advance_error_code) &&
            ByteSeq(notary_statement) &&
            ByteSeq(notary_attestation) &&
            Word32(|notary_statement|) &&
            Word32(|notary_attestation|) &&
            |packet.data| >= 13 + |notary_statement| + |notary_attestation| &&
            packet.data[0] == 1 &&
            packet.data[1..5] == word_to_bytes(advance_error_code) &&
            packet.data[5..9] == word_to_bytes(|notary_statement|) &&
            packet.data[9..13] == word_to_bytes(|notary_attestation|) &&
            packet.data[13..13+|notary_statement|] == notary_statement &&
            packet.data[13+|notary_statement|..13+|notary_statement|+|notary_attestation|] == notary_attestation
}

/////////////////////////////
// State machine
/////////////////////////////

predicate ValidStateMachineTransition (old_state:NotaryState, request:NotaryRequest,
                                       new_state:NotaryState, response:NotaryResponse)
{
    match request
        case InvalidRequest_ctor => new_state == old_state && response.NullResponse_ctor?
        case AdvanceCounterRequest_ctor(message) =>
            response.AdvanceCounterResponse_ctor? &&
            NotaryAdvanceCounterValid(old_state, new_state, message, response.advance_error_code, response.notary_statement,
                                      response.notary_attestation)
}

predicate ValidStateMachineTransitionPackets (old_state:NotaryState, request_packet:Packet,
                                              new_state:NotaryState, response_packet:Packet)
    requires ByteSeq(request_packet.data);
    requires ByteSeq(response_packet.data);
{
    exists request:NotaryRequest, response:NotaryResponse ::
        RequestParsedCorrectly(request_packet, request) &&
        ResponseFormedCorrectly(response, response_packet) &&
        ValidStateMachineTransition(old_state, request, new_state, response)
}

predicate NetworkOutputAcceptable (inputs:seq<Packet>, outputs:seq<Packet>)
{
    exists states:seq<NotaryState> ::
        |outputs| <= |inputs| &&
        |states| == |outputs| + 1 &&
        (forall i :: 0 <= i < |inputs| ==> ByteSeq(inputs[i].data)) &&
        (forall i :: 0 <= i < |outputs| ==> ByteSeq(outputs[i].data)) &&
        (forall i :: 0 <= i < |outputs| ==> ValidStateMachineTransitionPackets(states[i], inputs[i], states[i+1], outputs[i]))
}
