include "DiffPriv_spec.dfy"
include "../../Libraries/Crypto/RSA/RSASpec.dfy"
include "../../Libraries/Util/arrays_and_seqs.dfy"

datatype Packet = Packet_ctor(data:seq<int>);

/////////////////////////////
// Request parsing
/////////////////////////////

datatype DiffPrivRequest = InvalidRequest_ctor()
                         | InitializeRequest_ctor(budget_num:int, budget_den:int)
                         | AddRowRequest_ctor(row:Row, max_budget_num:int, max_budget_den:int)
                         | QueryRequest_ctor(q:QueryParameters);

function RequestParsedCorrectly (packet:Packet, request:DiffPrivRequest, key_pair:RSAKeyPairSpec) : bool
    requires ByteSeq(packet.data);
{
    if |packet.data| == 0 then
        request.InvalidRequest_ctor?
    else if packet.data[0] == 1 then
        InitializeRequestParsedCorrectly(packet, request)
    else if packet.data[0] == 2 then
        AddRowRequestParsedCorrectly(packet, request, key_pair)
    else if packet.data[0] == 3 then
        QueryRequestParsedCorrectly(packet, request)
    else
        request.InvalidRequest_ctor?
}

function InitializeRequestParsedCorrectly (packet:Packet, request:DiffPrivRequest) : bool
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 1;
{
    var words := ByteSeqToWordSeq(packet.data[1..]);
    if |words| < 2 then
        request.InvalidRequest_ctor?
    else
        request.InitializeRequest_ctor? &&
        request.budget_num == words[0] &&
        request.budget_den == words[1]
}

function AddRowRequestParsedCorrectly (packet:Packet, request:DiffPrivRequest, key_pair:RSAKeyPairSpec) : bool
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 2;
{
    (exists decryption:seq<int> :: RSADecryptionRelation(key_pair, packet.data[1..], decryption) &&
                                   DecryptedAddRowRequestParsedCorrectly(decryption, request)) ||
    request.InvalidRequest_ctor?
// TODO -- Once Jon makes decryption definite, put this back.
//    (request.InvalidRequest_ctor? &&
//     (forall decryption:seq<int> :: !RSADecryptionRelation(key_pair, packet.data[1..], decryption)))
}

function DecryptedAddRowRequestParsedCorrectly (data:seq<int>, request:DiffPrivRequest) : bool
    requires ByteSeq(data);
{
    var words := ByteSeqToWordSeq(data);
    if |words| < 4 then
        request.InvalidRequest_ctor?
    else
        var row_nonce_size := words[0];
        var row_data_size := words[1];
        if |words| < 4 + row_nonce_size + row_data_size then
            request.InvalidRequest_ctor?
        else
            request.AddRowRequest_ctor? &&
            request.max_budget_num == words[2] &&
            request.max_budget_den == words[3] &&
            request.row.nonce == words[4..4+row_nonce_size] &&
            request.row.data == words[4+row_nonce_size..4+row_nonce_size+row_data_size]
}

function QueryRequestParsedCorrectly (packet:Packet, request:DiffPrivRequest) : bool
    requires ByteSeq(packet.data);
    requires |packet.data| > 0;
    requires packet.data[0] == 3;
{
    var words := ByteSeqToWordSeq(packet.data[1..]);
    if |words| < 10 then
        request.InvalidRequest_ctor?
    else
        var program_size := words[0];
        if |words| < 10 + program_size then
            request.InvalidRequest_ctor?
        else
            request.QueryRequest_ctor? &&
            request.q.row_min == words[1] &&
            request.q.row_max == words[2] &&
            request.q.answer_units == words[3] &&
            request.q.answer_min == words[4] &&
            request.q.answer_max == words[5] &&
            request.q.alpha_num == words[6] &&
            request.q.alpha_den == words[7] &&
            request.q.beta_num == words[8] &&
            request.q.beta_den == words[9] &&
            request.q.program_encoding == words[10..10+program_size]
}

/////////////////////////////
// Response parsing
/////////////////////////////

datatype DiffPrivResponse = NullResponse_ctor()
                          | InitializeResponse_ctor(init_error_code:int)
                          | AddRowResponse_ctor(add_row_error_code:int)
                          | QueryResponse_ctor(query_error_code:int, response:int);

function ResponseFormedCorrectly (response:DiffPrivResponse, packet:Packet) : bool
    requires ByteSeq(packet.data);
{
    match response
        case NullResponse_ctor =>
            |packet.data| >= 1 && packet.data[0] == 0
        case InitializeResponse_ctor(error_code) =>
            |packet.data| >= 5 && packet.data[0] == 1 &&
            Word32(error_code) && packet.data[1..5] == word_to_bytes(error_code)
        case AddRowResponse_ctor(error_code) =>
            |packet.data| >= 5 && packet.data[0] == 2 &&
            Word32(error_code) && packet.data[1..5] == word_to_bytes(error_code)
        case QueryResponse_ctor(error_code, response_value) =>
            |packet.data| >= 9 && packet.data[0] == 3 &&
            Word32(error_code) && packet.data[1..5] == word_to_bytes(error_code) &&
            Word32(response_value) && packet.data[5..9] == word_to_bytes(response_value)
}

/////////////////////////////
// State machine
/////////////////////////////

predicate ValidStateMachineTransition (old_state:GhostDiffPrivState, request:DiffPrivRequest,
                                       new_state:GhostDiffPrivState, response:DiffPrivResponse)
    requires GhostDiffPrivStateValid(old_state);
{
    match request
        case InvalidRequest_ctor => new_state == old_state && response.NullResponse_ctor?
        case InitializeRequest_ctor(budget_num, budget_den) =>
            response.InitializeResponse_ctor? &&
            InitializedCorrectly(old_state, new_state, budget_num, budget_den, response.init_error_code)
        case AddRowRequest_ctor(row, max_budget_num, max_budget_den) =>
            response.AddRowResponse_ctor? &&
            RowAddedCorrectly(old_state, new_state, request.row, request.max_budget_num, request.max_budget_den,
                              response.add_row_error_code)
        case QueryRequest_ctor(q) =>
            response.QueryResponse_ctor? &&
            QueryPerformedCorrectly(old_state, new_state, request.q, response.query_error_code, response.response)
}

predicate ValidStateMachineTransitionPackets (old_state:GhostDiffPrivState, request_packet:Packet,
                                              new_state:GhostDiffPrivState, response_packet:Packet,
                                              key_pair:RSAKeyPairSpec)
    requires GhostDiffPrivStateValid(old_state);
    requires ByteSeq(request_packet.data);
    requires ByteSeq(response_packet.data);
{
    exists request:DiffPrivRequest, response:DiffPrivResponse ::
        RequestParsedCorrectly(request_packet, request, key_pair) &&
        ResponseFormedCorrectly(response, response_packet) &&
        ValidStateMachineTransition(old_state, request, new_state, response)
}

predicate NetworkOutputAcceptable (inputs:seq<Packet>, outputs:seq<Packet>, key_pair:RSAKeyPairSpec)
{
    exists states:seq<GhostDiffPrivState> ::
        |outputs| <= |inputs| &&
        |states| == |outputs| + 1 &&
        (forall i :: 0 <= i < |inputs| ==> ByteSeq(inputs[i].data)) &&
        (forall i :: 0 <= i < |outputs| ==> ByteSeq(outputs[i].data)) &&
        (forall i :: 0 <= i < |states| ==> GhostDiffPrivStateValid(states[i])) &&
        (forall i :: 0 <= i < |outputs| ==> ValidStateMachineTransitionPackets(states[i], inputs[i], states[i+1], outputs[i], key_pair))
}
