include "../../../Trusted/Spec/Apps/DiffPriv/StateMachine_spec.dfy"
include "../../Libraries/Crypto/RSA/RSA.dfy"
include "../../Libraries/Util/arrays_and_seqs.dfy"
include "DiffPriv_impl.dfy"

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

predicate RequestIsAllWords (request:DiffPrivRequest)
{
    match request
        case InvalidRequest_ctor => true
        case InitializeRequest_ctor(budget_num, budget_den) => Word32(budget_num) && Word32(budget_den)
        case AddRowRequest_ctor(row, max_budget_num, max_budget_den) => RowValid(row) && Word32(max_budget_num) && Word32(max_budget_den)
        case QueryRequest_ctor(q) => QueryParametersAllWords(q)
}

method ParseRequestPacket (packet:Packet, key_pair:RSAKeyPair) returns (request:DiffPrivRequest)
    requires ByteSeq(packet.data);
    requires WellformedKeyPair(key_pair);
    ensures RequestParsedCorrectly(packet, request, KeyPairToSpec(key_pair));
    ensures RequestIsAllWords(request);
{
    if |packet.data| == 0 {
        request := InvalidRequest_ctor();
        return;
    }
    if packet.data[0] == 1 {
        request := ParseInitializeRequestPacket(packet);
        return;
    }
    if packet.data[0] == 2 {
        request := ParseAddRowRequestPacket(packet, key_pair);
        return;
    }
    if packet.data[0] == 3 {
        request := ParseQueryRequestPacket(packet);
        return;
    }
    request := InvalidRequest_ctor();
}

method ParseInitializeRequestPacket (packet:Packet) returns (request:DiffPrivRequest)
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 1;
    ensures RequestIsAllWords(request);
    ensures InitializeRequestParsedCorrectly(packet, request);
{
    var words := ConvertByteSeqToWordSeq(packet.data[1..]);
    if |words| < 2 {
        request := InvalidRequest_ctor();
        return;
    }
    request := InitializeRequest_ctor(words[0], words[1]);
}

method ParseAddRowRequestPacket (packet:Packet, key_pair:RSAKeyPair) returns (request:DiffPrivRequest)
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 2;
    requires WellformedKeyPair(key_pair);
    ensures RequestIsAllWords(request);
    ensures AddRowRequestParsedCorrectly(packet, request, KeyPairToSpec(key_pair));
{
    var success, plaintext := Decrypt(key_pair, packet.data[1..]);
    if !success {
        request := InvalidRequest_ctor();
        return;
    }
    var words := ConvertByteSeqToWordSeq(plaintext);
    if |words| < 4 {
        request := InvalidRequest_ctor();
        return;
    }
    var row_nonce_size := words[0];
    var row_data_size := words[1];
    if |words| < 4 + row_nonce_size + row_data_size {
        request := InvalidRequest_ctor();
        return;
    }

    var row:Row := Row_ctor(words[4..4+row_nonce_size], words[4+row_nonce_size..4+row_nonce_size+row_data_size]);
    request := AddRowRequest_ctor(row, words[2], words[3]);
}

method ParseQueryRequestPacket (packet:Packet) returns (request:DiffPrivRequest)
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 3;
    ensures RequestIsAllWords(request);
    ensures QueryRequestParsedCorrectly(packet, request);
{
    var words := ConvertByteSeqToWordSeq(packet.data[1..]);
    if |words| < 10 {
        request := InvalidRequest_ctor();
        return;
    }
    var program_size := words[0];
    if |words| < 10 + program_size {
        request := InvalidRequest_ctor();
        return;
    }

    var program_encoding := words[10..10+program_size];
    var q := QueryParameters_ctor(program_encoding, words[1], words[2], words[3], words[4], words[5],
                                  words[6], words[7], words[8], words[9]);
    request := QueryRequest_ctor(q);
}

////////////////////////////
// Response forming
////////////////////////////

predicate WellformedResponse (response:DiffPrivResponse)
{
    match response
        case NullResponse_ctor => true
        case InitializeResponse_ctor(error_code) => Word32(error_code)
        case AddRowResponse_ctor(error_code) => Word32(error_code)
        case QueryResponse_ctor(error_code, response_value) => Word32(error_code) && Word32(response_value)
}

method FormResponsePacket (response:DiffPrivResponse) returns (packet:Packet)
    requires WellformedResponse(response);
    ensures ByteSeq(packet.data);
    ensures ResponseFormedCorrectly(response, packet);
{
    match response {
        case NullResponse_ctor =>
            packet := Packet_ctor([0]);
        case InitializeResponse_ctor(error_code) =>
            var error_code_encoded := word_2_bytes(error_code);
            packet := Packet_ctor([1] + error_code_encoded);
        case AddRowResponse_ctor(error_code) =>
            var error_code_encoded := word_2_bytes(error_code);
            packet := Packet_ctor([2] + error_code_encoded);
        case QueryResponse_ctor(error_code, response_value) =>
            var error_code_encoded := word_2_bytes(error_code);
            var response_value_encoded := word_2_bytes(response_value);
            packet := Packet_ctor([3] + error_code_encoded + response_value_encoded);
    }
}

////////////////////////////////
// State machine advancement
////////////////////////////////

method AdvanceStateMachine (old_state:DiffPrivStateImpl, request_packet:Packet, key_pair:RSAKeyPair)
                           returns (new_state:DiffPrivStateImpl, response_packet:Packet)
    requires GhostDiffPrivStateValid(DiffPrivStateImplToGhost(old_state));
    requires WellformedKeyPair(key_pair);
    requires ByteSeq(request_packet.data);
    ensures ByteSeq(response_packet.data);
    ensures GhostDiffPrivStateValid(DiffPrivStateImplToGhost(new_state));
    ensures ValidStateMachineTransitionPackets(DiffPrivStateImplToGhost(old_state), request_packet,
                                               DiffPrivStateImplToGhost(new_state), response_packet, KeyPairToSpec(key_pair));
{
    var request := ParseRequestPacket(request_packet, key_pair);
    var response:DiffPrivResponse;
    var error_code:int;

    match request {
        case InvalidRequest_ctor =>
            new_state := old_state;
            response := NullResponse_ctor();
            assert ValidStateMachineTransition(DiffPrivStateImplToGhost(old_state), request, DiffPrivStateImplToGhost(new_state), response);

        case InitializeRequest_ctor(budget_num, budget_den) =>
            error_code, new_state := Initialize(old_state, budget_num, budget_den);
            response := InitializeResponse_ctor(error_code);
            assert ValidStateMachineTransition(DiffPrivStateImplToGhost(old_state), request, DiffPrivStateImplToGhost(new_state), response);

        case AddRowRequest_ctor(row, max_budget_num, max_budget_den) =>
            error_code, new_state := AddRow(old_state, row, max_budget_num, max_budget_den);
            response := AddRowResponse_ctor(error_code);
            assert ValidStateMachineTransition(DiffPrivStateImplToGhost(old_state), request, DiffPrivStateImplToGhost(new_state), response);

        case QueryRequest_ctor(q) =>
            var response_value:int;
            error_code, response_value, new_state := PerformQuery(old_state, q);
            response := QueryResponse_ctor(error_code, response_value);
            assert ValidStateMachineTransition(DiffPrivStateImplToGhost(old_state), request, DiffPrivStateImplToGhost(new_state), response);
    }

    response_packet := FormResponsePacket(response);

    assert RequestParsedCorrectly(request_packet, request, KeyPairToSpec(key_pair));
    assert WellformedResponse(response);
    assert ResponseFormedCorrectly(response, response_packet);
    assert ValidStateMachineTransition(DiffPrivStateImplToGhost(old_state), request, DiffPrivStateImplToGhost(new_state), response);
    assert ValidStateMachineTransitionPackets(DiffPrivStateImplToGhost(old_state), request_packet,
                                              DiffPrivStateImplToGhost(new_state), response_packet, KeyPairToSpec(key_pair));
}

method {:timeLimit 60} EventLoop (randoms:seq<int>)
    requires forall i :: 0 <= i < |randoms| ==> Word32(randoms[i]);
{
    ghost var inputs:seq<Packet> := [];
    ghost var outputs:seq<Packet> := [];
    ghost var states:seq<GhostDiffPrivState> := [];

    lemma_2toX(); reveal_power2();
    var key_pair := RSAKeyGen(2048);

    var initial_budget := MakeSmallLiteralBigRat(1);
    assert RV(initial_budget) == real_of(1);
    var current_state := DiffPrivStateImpl_ctor([], initial_budget, randoms);
    assert GhostDiffPrivStateValid(DiffPrivStateImplToGhost(current_state));
    states := states + [DiffPrivStateImplToGhost(current_state)];

    var num_packets := 0;
    while num_packets < 4000000000
       invariant 0 <= num_packets <= 4000000000;
       invariant GhostDiffPrivStateValid(DiffPrivStateImplToGhost(current_state));
       invariant |inputs| == |outputs|;
       invariant |states| == |outputs| + 1;
       invariant states[|states|-1] == DiffPrivStateImplToGhost(current_state);
       invariant forall i :: 0 <= i < |inputs| ==> ByteSeq(inputs[i].data);
       invariant forall i :: 0 <= i < |outputs| ==> ByteSeq(outputs[i].data);
       invariant forall i :: 0 <= i < |states| ==> GhostDiffPrivStateValid(states[i]);
       invariant forall i :: 0 <= i < |outputs| ==>
                             ValidStateMachineTransitionPackets(states[i], inputs[i], states[i+1], outputs[i], KeyPairToSpec(key_pair));
       invariant NetworkOutputAcceptable(inputs, outputs, KeyPairToSpec(key_pair));
    {
        ghost var previous_state := current_state;
        var request_packet := GetPacket();
        var next_state, response_packet := AdvanceStateMachine(current_state, request_packet, key_pair);
        assert ValidStateMachineTransitionPackets(DiffPrivStateImplToGhost(previous_state), request_packet,
                                                  DiffPrivStateImplToGhost(next_state), response_packet, KeyPairToSpec(key_pair));
        current_state := next_state;

        inputs := inputs + [request_packet];
        outputs := outputs + [response_packet];
        states := states + [DiffPrivStateImplToGhost(current_state)];

        SendPacket(response_packet);
        num_packets := num_packets + 1;

        forall i | 0 <= i < |outputs|
            ensures ValidStateMachineTransitionPackets(states[i], inputs[i], states[i+1], outputs[i], KeyPairToSpec(key_pair));
        {
            if i == |outputs| - 1 {
                assert states[i] == DiffPrivStateImplToGhost(previous_state);
                assert states[i+1] == DiffPrivStateImplToGhost(next_state);
                assert inputs[i] == request_packet;
                assert outputs[i] == response_packet;
            }
        }
    }
}
