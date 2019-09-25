//-<NuBuild BasmEnableSymdiff true />
include "StateMachine.s.dfy"
include "DiffPriv.i.dfy"
include "DiffPrivPerformQuery.i.dfy"
include "../../Libraries/Net/Udp.i.dfy"
include "../../Libraries/Util/Halter.i.dfy"
include "../../Libraries/Util/relational.i.dfy"

method HandleGetDiffPrivQuoteRequest(common_state_in:CommonStateImpl, nonce_external:seq<int>)
                                    returns (response:DiffPrivResponse, common_state_out:CommonStateImpl)
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires IsByteSeqOfLen(nonce_external, 20);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_common_state;

    ensures TPM_ready();
    ensures WellformedResponse(response);
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(nonce_external);
    ensures public(response);
{
    var encoded_public_key:seq<int>, pcr_info_bytes:seq<int>, sig_bytes:seq<int>;
    common_state_out, encoded_public_key, pcr_info_bytes, sig_bytes := HandleGetQuoteRequest(common_state_in, nonce_external);
    ghost var declassified_encoded_public_key, declassified_pcr_info_bytes, declassified_sig_bytes :=
        AdvanceCommonStateMachineViaGetQuote(nonce_external, encoded_public_key, pcr_info_bytes, sig_bytes);
    var usable_encoded_public_key := UseDeclassifiedByteSequence(encoded_public_key, declassified_encoded_public_key);
    var usable_pcr_info_bytes := UseDeclassifiedByteSequence(pcr_info_bytes, declassified_pcr_info_bytes);
    var usable_sig_bytes := UseDeclassifiedByteSequence(sig_bytes, declassified_sig_bytes);
    response := GetQuoteResponse_ctor(0, usable_encoded_public_key, usable_pcr_info_bytes, usable_sig_bytes);
}

method HandleInitializeDBRequest(diffpriv_state_in:DiffPrivStateImpl, budget_num:int, budget_den:int)
                                returns (diffpriv_state_out:DiffPrivStateImpl, response:DiffPrivResponse)
    requires current_common_state.initialized;
    requires current_common_state.TPM == TPM;
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires Word32(budget_num);
    requires Word32(budget_den);
    requires budget_den != 0;

    modifies this`current_diffpriv_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures WellformedResponse(response);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(budget_num);
    requires public(budget_den);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response);
{
    var init_error_code:int;
    init_error_code, diffpriv_state_out := DiffPrivInitializeDB(diffpriv_state_in, budget_num, budget_den);
    if init_error_code == 0 {
        AdvanceDiffPrivStateMachineByInitializingDB(real(budget_num) / real(budget_den), DiffPrivStateImplToSpec(diffpriv_state_out));
    }
    response := InitializeDBResponse_ctor(init_error_code);
}

method HandleAddRowRequest(diffpriv_state_in:DiffPrivStateImpl, common_state:CommonStateImpl, request_ciphertext:seq<int>)
                          returns (diffpriv_state_out:DiffPrivStateImpl, response:DiffPrivResponse)
    requires CommonStateImplValid(common_state);
    requires common_state.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires IsByteSeq(request_ciphertext);
    requires |request_ciphertext| > 0;

    modifies this`current_diffpriv_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures WellformedResponse(response);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(request_ciphertext);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response);
{
    diffpriv_state_out := DiffPrivAddRow(diffpriv_state_in, common_state.key_pair, request_ciphertext);
    AdvanceDiffPrivStateMachineByAddingRow(request_ciphertext, DiffPrivStateImplToSpec(diffpriv_state_out));
    response := AddRowResponse_ctor();
}

method HandleQueryRequest(diffpriv_state_in:DiffPrivStateImpl, common_state:CommonStateImpl, q:QueryParametersImpl)
                         returns (diffpriv_state_out:DiffPrivStateImpl, response:DiffPrivResponse)
    requires CommonStateImplValid(common_state);
    requires TPM_ready();
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires QueryParametersImplValid(q);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_diffpriv_state;
    modifies this`current_common_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures TPM_ready();
    ensures WellformedResponse(response);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(q);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response);
{
    var query_error_code:int, answer:int;
    query_error_code, answer, diffpriv_state_out := DiffPrivPerformQuery(diffpriv_state_in, q);
    var usable_answer:int;
    if query_error_code != 0 {
        usable_answer := 0;
    }
    else {
        ghost var declassified_answer :=
            AdvanceDiffPrivStateMachineByAnsweringQuery(QueryParametersImplToSpec(q),
                                                        DiffPrivStateImplToSpec(diffpriv_state_out),
                                                        answer);
        usable_answer := Asm_declassify_result(answer, declassified_answer);
    }
    response := QueryResponse_ctor(query_error_code, usable_answer);
}


method HandleOneRequest (request:DiffPrivRequestImpl, diffpriv_state_in:DiffPrivStateImpl, common_state_in:CommonStateImpl)
                        returns (response:DiffPrivResponse, diffpriv_state_out:DiffPrivStateImpl, common_state_out:CommonStateImpl)
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires WellformedDiffPrivRequest(request);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_diffpriv_state;
    modifies this`current_common_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures TPM_ready();
    ensures WellformedResponse(response);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(request);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response);
{
    match request {
        case InvalidRequestImpl_ctor =>
            response := NullResponse_ctor();
            diffpriv_state_out := diffpriv_state_in;
            common_state_out := common_state_in;

        case GetQuoteRequestImpl_ctor(nonce_external) =>
            diffpriv_state_out := diffpriv_state_in;
            response, common_state_out := HandleGetDiffPrivQuoteRequest(common_state_in, nonce_external);

        case InitializeDBRequestImpl_ctor(budget_num, budget_den) =>
            diffpriv_state_out, response := HandleInitializeDBRequest(diffpriv_state_in, budget_num, budget_den);
            common_state_out := common_state_in;

        case AddRowRequestImpl_ctor(request_ciphertext) =>
            diffpriv_state_out, response := HandleAddRowRequest(diffpriv_state_in, common_state_in, request_ciphertext);
            common_state_out := common_state_in;

        case QueryRequestImpl_ctor(q) =>
            diffpriv_state_out, response := HandleQueryRequest(diffpriv_state_in, common_state_in, q);
            common_state_out := common_state_in;
    }
}

method HandleOneRequestRaw (request_bytes:seq<int>, diffpriv_state_in:DiffPrivStateImpl, common_state_in:CommonStateImpl)
                           returns (response_bytes:seq<int>, diffpriv_state_out:DiffPrivStateImpl, common_state_out:CommonStateImpl)
    requires CommonStateImplValid(common_state_in);
    requires common_state_in.key_pair.pub.size >= 1024 / 8;
    requires TPM_ready();
    requires DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_in));
    requires current_common_state == CommonStateMachine_ctor(true, CommonStateImplToSpec(common_state_in), TPM);
    requires current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_in));
    requires IsByteSeq(request_bytes);

    modifies this`TPM;
    modifies this`IoMemPerm;
    modifies this`current_diffpriv_state;
    modifies this`current_common_state;

    ensures DiffPrivStateValid(DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures TPM_ready();
    ensures IsByteSeq(response_bytes);
    ensures current_diffpriv_state == DiffPrivStateMachine_ctor(true, DiffPrivStateImplToSpec(diffpriv_state_out));
    ensures current_common_state == old(current_common_state)[TPM := TPM];
    ensures CommonStateImplValid(common_state_out);
    ensures CommonStateImplToSpec(common_state_out) == CommonStateImplToSpec(common_state_in);

    requires public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_in)));
    requires public(request_bytes);
    ensures public(PublicPartOfDiffPrivState(DiffPrivStateImplToSpec(diffpriv_state_out)));
    ensures public(response_bytes);
{
    var request := ParseRequestPacket(request_bytes);
    var response:DiffPrivResponse;
    response, diffpriv_state_out, common_state_out := HandleOneRequest(request, diffpriv_state_in, common_state_in);
    response_bytes := FormResponsePacket(response);
}
