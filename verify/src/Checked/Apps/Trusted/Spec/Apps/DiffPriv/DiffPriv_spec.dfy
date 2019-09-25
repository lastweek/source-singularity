include "Mapper_spec.dfy"
include "SumReducer_spec.dfy"
include "Noise_spec.dfy"
include "../../Assembly.dfy"

datatype GhostDiffPrivState = GhostDiffPrivState_ctor(db:seq<Row>, budget:real, randoms:seq<int>);

function GhostDiffPrivStateValid (s:GhostDiffPrivState) : bool
{
    DatabaseValid(s.db) &&
    s.budget >= real_of(1) &&
    (forall i :: 0 <= i < |s.randoms| ==> Word32(s.randoms[i]))
}

datatype PublicDiffPrivState = PublicDiffPrivState_ctor(budget:real, num_randoms:nat)

function PublicPartOfDiffPrivState (s:GhostDiffPrivState) : PublicDiffPrivState
{
    PublicDiffPrivState_ctor(s.budget, |s.randoms|)
}

datatype QueryParameters = QueryParameters_ctor(program_encoding:seq<int>, row_min:int, row_max:int,
                                                answer_units:int, answer_min:int, answer_max:int,
                                                alpha_num:int, alpha_den:int, beta_num:int, beta_den:int);

function QueryParametersValid (q:QueryParameters) : bool
{
    Word32(q.row_min) &&
    Word32(q.row_max) &&
    Word32(q.answer_units) &&
    Word32(q.answer_min) &&
    Word32(q.answer_max) &&
    Word32(q.alpha_num) &&
    Word32(q.alpha_den) &&
    Word32(q.beta_num) &&
    Word32(q.beta_den) &&
    q.row_min <= q.row_max &&
    q.answer_min <= q.answer_max &&
    q.alpha_num > q.alpha_den > 0 &&
    q.beta_num > q.beta_den > 0 &&
    q.answer_units > 0 &&
    (forall i :: 0 <= i < |q.program_encoding| ==> Word32(q.program_encoding[i])) &&
    ProgramValid(MessageToProgram(q.program_encoding))
}

function InitializedCorrectly (old_state:GhostDiffPrivState, new_state:GhostDiffPrivState,
                               budget_num:int, budget_den:int, error_code:int) : bool
{
    GhostDiffPrivStateValid(new_state) &&
    if error_code == 0 then
        budget_den > 0 &&
        new_state.db == [] &&
        new_state.budget == real_of(budget_num) / real_of(budget_den) &&
        new_state.randoms == old_state.randoms
    else
        new_state == old_state
}

function RowAddedCorrectly (old_state:GhostDiffPrivState, new_state:GhostDiffPrivState, row:Row,
                            max_budget_num:int, max_budget_den:int, error_code:int) : bool
{
    GhostDiffPrivStateValid(new_state) &&
    if error_code == 0 then
        max_budget_den > 0 &&
        new_state.budget <= real_of(max_budget_num) / real_of(max_budget_den) &&
        new_state.db == (if DatabaseContainsNonce(old_state.db, row.nonce) then old_state.db else old_state.db + [row]) &&
        new_state.budget == old_state.budget &&
        new_state.randoms == old_state.randoms
    else
        new_state == old_state
}

function QueryResponse (db:seq<Row>, q:QueryParameters, noise:int) : int
    requires DatabaseValid(db);
    requires QueryParametersValid(q);
{
    var program := MessageToProgram(q.program_encoding);
    var sum := MapperSum(db, program, q.row_min, q.row_max);
    var scaled_sum := Scale(sum, q.answer_units);
    var answer := Clip(scaled_sum, q.answer_min, q.answer_max);
    var noised_answer := answer + noise;
    Clip(noised_answer, q.answer_min, q.answer_max)
}

function QueryParametersToDiffPrivParameters (q:QueryParameters) : GhostDiffPrivParameters
    requires QueryParametersValid(q);
{
    GhostDiffPrivParameters_ctor(real_of(q.alpha_num) / real_of(q.alpha_den),
                                 real_of(q.beta_num) / real_of(q.beta_den),
                                 DivideRoundingUp(q.row_max - q.row_min, q.answer_units),
                                 q.answer_max - q.answer_min)
}

function QuerySuccessful (old_state:GhostDiffPrivState, new_state:GhostDiffPrivState, q:QueryParameters, error_code:int, response:int,
                          randoms_used:seq<int>, noise:int) : bool
    requires GhostDiffPrivStateValid(old_state);
    requires QueryParametersValid(q);
{
    var p := QueryParametersToDiffPrivParameters(q);

    DiffPrivParametersValid(p) &&
    old_state.budget >= p.beta &&
    new_state.db == old_state.db &&
    new_state.budget == old_state.budget / p.beta &&
    old_state.randoms == randoms_used + new_state.randoms &&
    NoiseComputedCorrectly(p, randoms_used, noise) &&
    response == QueryResponse(old_state.db, q, noise)
}

function QueryPerformedCorrectly (old_state:GhostDiffPrivState, new_state:GhostDiffPrivState, q:QueryParameters,
                                  error_code:int, response:int) : bool
    requires GhostDiffPrivStateValid(old_state);
{
    GhostDiffPrivStateValid(new_state) &&
    if error_code == 0 then
        QueryParametersValid(q) &&
        exists randoms_used:seq<int>, noise:int :: QuerySuccessful(old_state, new_state, q, error_code, response, randoms_used, noise)
    else
       new_state == old_state &&
       response == 0
}
