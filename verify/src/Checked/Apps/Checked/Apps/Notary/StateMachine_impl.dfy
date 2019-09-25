include "../../../Trusted/Spec/Apps/Notary/StateMachine_spec.dfy"
include "../../Libraries/Crypto/RSA/RSA.dfy"
include "../../Libraries/Util/arrays_and_seqs.dfy"
include "Notary_impl.dfy"

////////////////////////////
// Placeholders
////////////////////////////

method {:axiom} ConvertByteSeqToWordSeq (bytes:seq<int>) returns (words:seq<int>)
    requires ByteSeq(bytes);
    ensures WordSeq(words);
    ensures words == ByteSeqToWordSeq(bytes);

method {:axiom} GetPacket () returns (packet:Packet)
    ensures ByteSeq(packet.data);

method {:axiom} SendPacket (packet:Packet) returns ()
    requires ByteSeq(packet.data);

////////////////////////////
// Request parsing
////////////////////////////

predicate RequestValid (request:NotaryRequest)
{
    match request
        case InvalidRequest_ctor => true
        case AdvanceCounterRequest_ctor(message) => ByteSeq(message)
}

method ParseRequestPacket (packet:Packet) returns (request:NotaryRequest)
    requires ByteSeq(packet.data);
    ensures RequestParsedCorrectly(packet, request);
    ensures RequestValid(request);
{
    if |packet.data| == 0 {
        request := InvalidRequest_ctor();
        return;
    }
    if packet.data[0] == 1 {
        request := ParseAdvanceCounterRequestPacket(packet);
        return;
    }
    request := InvalidRequest_ctor();
}

method ParseAdvanceCounterRequestPacket (packet:Packet) returns (request:NotaryRequest)
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 1;
    ensures AdvanceCounterRequestParsedCorrectly(packet, request);
    ensures RequestValid(request);
{
    if |packet.data| < 2 {
        request := InvalidRequest_ctor();
        return;
    }
    var message_len := packet.data[1];
    if |packet.data| < 2 + message_len {
        request := InvalidRequest_ctor();
        return;
    }
    request := AdvanceCounterRequest_ctor(packet.data[2..2+message_len]);
}

////////////////////////////
// Response forming
////////////////////////////

predicate WellformedResponse (response:NotaryResponse)
{
    match response
        case NullResponse_ctor => true
        case AdvanceCounterResponse_ctor(e, s, a) => Word32(e) && Word32(|s|) && Word32(|a|) && ByteSeq(s) && ByteSeq(a)
}

method FormResponsePacket (response:NotaryResponse) returns (packet:Packet)
    requires WellformedResponse(response);
    ensures ByteSeq(packet.data);
    ensures ResponseFormedCorrectly(response, packet);
{
    lemma_2toX();
    reveal_power2();

    match response {
        case NullResponse_ctor =>
            packet := Packet_ctor([0]);

        case AdvanceCounterResponse_ctor(advance_error_code, notary_statement, notary_attestation) =>
            var advance_error_code_encoded := word_2_bytes(advance_error_code);
            var notary_statement_len_encoded := word_2_bytes(|notary_statement|);
            var notary_attestation_len_encoded := word_2_bytes(|notary_attestation|);
            packet := Packet_ctor([1] + advance_error_code_encoded + notary_statement_len_encoded + notary_attestation_len_encoded +
                                  notary_statement + notary_attestation);
            assert packet.data[0] == 1;
            assert packet.data[1..5] == word_to_bytes(advance_error_code);
            assert packet.data[5..9] == word_to_bytes(|notary_statement|);
            assert packet.data[9..13] == word_to_bytes(|notary_attestation|);
            assert packet.data[13..13+|notary_statement|] == notary_statement;
            assert packet.data[13+|notary_statement|..13+|notary_statement|+|notary_attestation|] == notary_attestation;
    }
}

////////////////////////////////
// State machine advancement
////////////////////////////////

method AdvanceStateMachine (old_state:NotaryStateImpl, request_packet:Packet)
                           returns (new_state:NotaryStateImpl, response_packet:Packet)
    requires NotaryStateImplValid(old_state);
    requires ByteSeq(request_packet.data);
    ensures ByteSeq(response_packet.data);
    ensures NotaryStateImplValid(new_state);
    ensures ValidStateMachineTransitionPackets(NotaryStateImplToSpec(old_state), request_packet,
                                               NotaryStateImplToSpec(new_state), response_packet);
{
    var request := ParseRequestPacket(request_packet);
    var response:NotaryResponse;
    var error_code:int;

    match request {
        case InvalidRequest_ctor =>
            new_state := old_state;
            response := NullResponse_ctor();

        case AdvanceCounterRequest_ctor(message) =>
            var error_code:int, notary_statement:seq<int>, notary_attestation:seq<int>;
            new_state, error_code, notary_statement, notary_attestation := NotaryAdvanceCounter(old_state, message);
            response := AdvanceCounterResponse_ctor(error_code, notary_statement, notary_attestation);
    }

    assert ValidStateMachineTransition(NotaryStateImplToSpec(old_state), request, NotaryStateImplToSpec(new_state), response);

    response_packet := FormResponsePacket(response);

    assert RequestParsedCorrectly(request_packet, request);
    assert WellformedResponse(response);
    assert ResponseFormedCorrectly(response, response_packet);
    assert ValidStateMachineTransition(NotaryStateImplToSpec(old_state), request, NotaryStateImplToSpec(new_state), response);
    assert ValidStateMachineTransitionPackets(NotaryStateImplToSpec(old_state), request_packet,
                                              NotaryStateImplToSpec(new_state), response_packet);
}

method {:timeLimit 60} EventLoop ()
{
    ghost var inputs:seq<Packet> := [];
    ghost var outputs:seq<Packet> := [];
    ghost var states:seq<NotaryState> := [];

    lemma_2toX(); reveal_power2();

    var current_state := NotaryInitialize();
    states := states + [NotaryStateImplToSpec(current_state)];

    var num_packets := 0;
    while num_packets < 4000000000
       invariant 0 <= num_packets <= 4000000000;
       invariant NotaryStateImplValid(current_state);
       invariant |inputs| == |outputs|;
       invariant |states| == |outputs| + 1;
       invariant states[|states|-1] == NotaryStateImplToSpec(current_state);
       invariant forall i :: 0 <= i < |inputs| ==> ByteSeq(inputs[i].data);
       invariant forall i :: 0 <= i < |outputs| ==> ByteSeq(outputs[i].data);
       invariant forall i :: 0 <= i < |outputs| ==>
                             ValidStateMachineTransitionPackets(states[i], inputs[i], states[i+1], outputs[i]);
       invariant NetworkOutputAcceptable(inputs, outputs);
    {
        ghost var previous_state := current_state;
        var request_packet := GetPacket();
        var next_state, response_packet := AdvanceStateMachine(current_state, request_packet);
        assert ValidStateMachineTransitionPackets(NotaryStateImplToSpec(previous_state), request_packet,
                                                  NotaryStateImplToSpec(next_state), response_packet);
        current_state := next_state;

        inputs := inputs + [request_packet];
        outputs := outputs + [response_packet];
        states := states + [NotaryStateImplToSpec(current_state)];

        SendPacket(response_packet);
        num_packets := num_packets + 1;

        forall i | 0 <= i < |outputs|
            ensures ValidStateMachineTransitionPackets(states[i], inputs[i], states[i+1], outputs[i]);
        {
            if i == |outputs| - 1 {
                assert states[i] == NotaryStateImplToSpec(previous_state);
                assert states[i+1] == NotaryStateImplToSpec(next_state);
                assert inputs[i] == request_packet;
                assert outputs[i] == response_packet;
            }
        }
    }
}
