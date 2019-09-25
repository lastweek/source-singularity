include "../../../Trusted/Spec/Apps/DiffPriv/DiffPriv_spec.dfy"
include "../../Libraries/BigNum/BigRat.dfy"
include "ErrorCodes.dfy"
include "Noise_impl.dfy"
include "SumReducer_impl.dfy"
include "../../../Trusted/Spec/Libraries/Util/relational.dfy"
include "../../Libraries/Util/arrays_and_seqs.dfy"

//////////////////////////////////////////////
// DiffPrivStateImpl
//////////////////////////////////////////////

datatype DiffPrivStateImpl = DiffPrivStateImpl_ctor(db:seq<Row>, budget:BigRat, randoms:seq<int>);

function DiffPrivStateImplToGhost(s:DiffPrivStateImpl) : GhostDiffPrivState
{
    GhostDiffPrivState_ctor(s.db,
                            if WellformedBigRat(s.budget) then RV(s.budget) else real_of(0),
                            s.randoms)
}

//////////////////////////////////////////////
// Query parameters
//////////////////////////////////////////////

function QueryParametersAllWords (q:QueryParameters) : bool
{
    (forall i :: 0 <= i < |q.program_encoding| ==> Word32(q.program_encoding[i])) &&
    Word32(q.row_min) &&
    Word32(q.row_max) &&
    Word32(q.answer_units) &&
    Word32(q.answer_min) &&
    Word32(q.answer_max) &&
    Word32(q.alpha_num) &&
    Word32(q.alpha_den) &&
    Word32(q.beta_num) &&
    Word32(q.beta_den)
}

method GetDiffPrivParametersFromQueryParameters (q:QueryParameters) returns (p:DiffPrivParametersImpl)
    requires QueryParametersAllWords(q);
    requires QueryParametersValid(q);
    ensures WellformedDiffPrivParameters(p);
    ensures DiffPrivParametersImplToGhost(p) == QueryParametersToDiffPrivParameters(q);
{
    var alpha := BigRat_ctor(MakeSmallLiteralBigNum(q.alpha_num), MakeSmallLiteralBigNat(q.alpha_den));
    var beta := BigRat_ctor(MakeSmallLiteralBigNum(q.beta_num), MakeSmallLiteralBigNat(q.beta_den));
    var delta := DivideRoundingUp(q.row_max - q.row_min, q.answer_units);
    Lemma_DivideRoundingUpPreservesWord32(q.row_max - q.row_min, q.answer_units);
    var B := q.answer_max - q.answer_min;

    p := DiffPrivParametersImpl_ctor(alpha, beta, delta, B);
}

//////////////////////////////////////////////
// Exported methods
//////////////////////////////////////////////

method Initialize (old_state:DiffPrivStateImpl, budget_num:int, budget_den:int) returns (error_code:int, new_state:DiffPrivStateImpl)
    requires GhostDiffPrivStateValid(DiffPrivStateImplToGhost(old_state));
    requires Word32(budget_num);
    requires Word32(budget_den);
    ensures Word32(error_code);
    ensures InitializedCorrectly(DiffPrivStateImplToGhost(old_state), DiffPrivStateImplToGhost(new_state),
                                 budget_num, budget_den, error_code);
    ensures PublicPartOfDiffPrivState(DiffPrivStateImplToGhost(left(old_state))) == PublicPartOfDiffPrivState(DiffPrivStateImplToGhost(right(old_state))) ==> left(error_code) == right(error_code);
{
    lemma_2toX();

    if budget_den == 0 {
        error_code := ErrorBudgetDenominatorZero();
        new_state := old_state;
        return;
    }

    if budget_num < budget_den {
        error_code := ErrorBudgetLessThanOne();
        new_state := old_state;
        return;
    }

    error_code := 0;

    // At this point, the error code is set so we can look at private data.

    var budget := BigRat_ctor(MakeSmallLiteralBigNum(budget_num), MakeSmallLiteralBigNat(budget_den));
    assert RV(budget) == real_of(budget_num) / real_of(budget_den);
    Lemma_DividingBySmallerProducesAtLeastOne(real_of(budget_num), real_of(budget_den));
    new_state := DiffPrivStateImpl_ctor([], budget, old_state.randoms);
}

method AddRow (old_state:DiffPrivStateImpl, row:Row, max_budget_num:int, max_budget_den:int)
              returns (error_code:int, new_state:DiffPrivStateImpl)
    requires GhostDiffPrivStateValid(DiffPrivStateImplToGhost(old_state));
    requires RowValid(row);
    requires Word32(max_budget_num);
    requires Word32(max_budget_den);
    ensures Word32(error_code);
    ensures RowAddedCorrectly(DiffPrivStateImplToGhost(old_state), DiffPrivStateImplToGhost(new_state), row,
                              max_budget_num, max_budget_den, error_code);
    ensures PublicPartOfDiffPrivState(DiffPrivStateImplToGhost(left(old_state))) == PublicPartOfDiffPrivState(DiffPrivStateImplToGhost(right(old_state))) ==> left(error_code) == right(error_code);
{
    lemma_2toX();

    if max_budget_den == 0 {
        error_code := ErrorBudgetDenominatorZero();
        new_state := old_state;
        return;
    }

    var max_budget := BigRat_ctor(MakeSmallLiteralBigNum(max_budget_num), MakeSmallLiteralBigNat(max_budget_den));
    var insufficient := BigRatGt(old_state.budget, max_budget);
    if insufficient {
        error_code := ErrorTooMuchBudgetToAddRow();
        new_state := old_state;
        return;
    }

    error_code := 0;

    // At this point, the error code is set so we can look at private data.

    var already_exists:bool := DoesDatabaseContainNonce(old_state.db, row.nonce);
    if already_exists {
        new_state := old_state;
    }
    else {
        new_state := DiffPrivStateImpl_ctor(old_state.db + [row], old_state.budget, old_state.randoms);
    }
}

method {:timeLimit 40} PerformQuery (old_state:DiffPrivStateImpl, q:QueryParameters)
                                    returns (error_code:int, response:int, new_state:DiffPrivStateImpl)
    requires GhostDiffPrivStateValid(DiffPrivStateImplToGhost(old_state));
    requires QueryParametersAllWords(q);
    ensures Word32(error_code);
    ensures Word32(response);
    ensures QueryPerformedCorrectly(DiffPrivStateImplToGhost(old_state), DiffPrivStateImplToGhost(new_state), q, error_code, response);
    ensures PublicPartOfDiffPrivState(DiffPrivStateImplToGhost(left(old_state))) == PublicPartOfDiffPrivState(DiffPrivStateImplToGhost(right(old_state))) ==> left(error_code) == right(error_code);
{
    var program:seq<Operation>, p:DiffPrivParametersImpl, num_randoms_needed:nat;
    error_code, program, p, num_randoms_needed := GetErrorCodeForPerformQuery(q, old_state.budget, |old_state.randoms|);
    if error_code != 0 {
        response := 0;
        new_state := old_state;
        return;
    }

    //
    // At this point, the error code is set so we can look at private data.
    // (All we looked at before was old_state.budget and |old_state.randoms|.)
    //

    //
    // Generate the noise.
    //

    var negate_noise:bool, absolute_noise:nat, remaining_budget:BigRat, remaining_randoms:seq<int>;
    ghost var noise:int, randoms_used:seq<int>;
    negate_noise, absolute_noise, noise, remaining_budget, remaining_randoms, randoms_used :=
        GenerateNoise(p, old_state.randoms, old_state.budget, num_randoms_needed);

    //
    // Run the reducer.
    //

    var answer:int;
    ghost var sum:int;
    answer, sum := ComputeSum(old_state.db, program, q.row_min, q.row_max, q.answer_units, q.answer_min, q.answer_max);

    //
    // Convert the answer into a response by adding noise and clipping.
    //

    response := AddNoise(old_state.db, sum, answer, q, negate_noise, absolute_noise, noise);

    //
    // Update the state to reduce the privacy budget and remove the random numbers used.
    //

    new_state := DiffPrivStateImpl_ctor(old_state.db, remaining_budget, remaining_randoms);
    assert DatabaseValid(old_state.db);
    assert ProgramValid(program);
    assert q.row_min <= q.row_max;
    assert sum == MapperSum(old_state.db, program, q.row_min, q.row_max);
    assert forall i :: 0 <= i < |randoms_used| ==> Word32(randoms_used[i]);
    Lemma_QueryPerformedCorrectly(DiffPrivStateImplToGhost(old_state), DiffPrivStateImplToGhost(new_state), q,
                                  DiffPrivParametersImplToGhost(p), randoms_used, noise, error_code, response);
}

//////////////////////////////////////////////
// Helpers
//////////////////////////////////////////////

method DoesDatabaseContainNonce (db:seq<Row>, nonce:seq<int>) returns (already_exists:bool)
    requires DatabaseValid(db);
    ensures already_exists == DatabaseContainsNonce(db, nonce);
{
    var i:int := 0;
    while i < |db|
        invariant 0 <= i <= |db|;
        invariant forall j :: 0 <= j < i ==> db[j].nonce != nonce;
    {
        if db[i].nonce == nonce {
            already_exists := true;
            return;
        }
        i := i + 1;
    }

    already_exists := false;
}

method DetermineIfQueryParametersValid (q:QueryParameters) returns (error_code:int, program:seq<Operation>)
    requires QueryParametersAllWords(q);
    ensures Word32(error_code);
    ensures error_code == 0 <==> QueryParametersValid(q);
    ensures error_code == 0 ==> program == MessageToProgram(q.program_encoding);
{
    lemma_2toX();

    //
    // Validate the input values.
    //

    if (q.row_min > q.row_max) {
        error_code := ErrorRowMinGreaterThanRowMax();
        return;
    }
    if (q.answer_min > q.answer_max) {
        error_code := ErrorAnswerMinGreaterThanAnswerMax();
        return;
    }
    if (q.answer_units <= 0) {
        error_code := ErrorAnswerUnitsNotPositive();
        return;
    }
    if (q.alpha_num <= q.alpha_den) {
        error_code := ErrorAlphaNotGreaterThanOne();
        return;
    }
    if (q.alpha_den <= 0) {
        error_code := ErrorAlphaDenominatorZero();
        return;
    }
    if (q.beta_num <= q.beta_den) {
        error_code := ErrorBetaNotGreaterThanOne();
        return;
    }
    if (q.beta_den <= 0) {
        error_code := ErrorBetaDenominatorZero();
        return;
    }

    //
    // Convert the program encoding into a program and validate it.
    //

    program := ConvertMessageToProgram(q.program_encoding);
    var valid:bool := DetermineIfProgramIsValid(program);
    if (!valid) {
        error_code := ErrorProgramInvalid();
        return;
    }

    error_code := 0;
}

method ParseQueryParameters (q:QueryParameters) returns (error_code:int, program:seq<Operation>, p:DiffPrivParametersImpl)
    requires QueryParametersAllWords(q);
    ensures Word32(error_code);
    ensures error_code == 0 ==> QueryParametersValid(q) &&
                                program == MessageToProgram(q.program_encoding) &&
                                ProgramValid(program) &&
                                Word32(q.answer_units * 2) &&
                                WellformedDiffPrivParameters(p) &&
                                DiffPrivParametersImplToGhost(p) == QueryParametersToDiffPrivParameters(q) &&
                                DiffPrivParametersValid(DiffPrivParametersImplToGhost(p));
{
    //
    // Validate the input values.
    //

    error_code, program := DetermineIfQueryParametersValid(q);
    if (error_code != 0) {
        return;
    }

    //
    // Make sure the answer units aren't ridiculously high.
    //

    error_code := TestAnswerUnits(q.answer_units);
    if (error_code != 0) {
        return;
    }

    //
    // Compute noise parameters and validate them.
    //

    p := GetDiffPrivParametersFromQueryParameters(q);
    error_code := DetermineIfDiffPrivParametersValid(p);
}

method GetErrorCodeForPerformQuery (q:QueryParameters, budget:BigRat, num_randoms_available:nat)
                                    returns (error_code:int, program:seq<Operation>, p:DiffPrivParametersImpl, num_randoms_needed:nat)
    requires QueryParametersAllWords(q);
    requires WellformedBigRat(budget);
    ensures Word32(error_code);
    ensures error_code == 0 ==> QueryParametersValid(q) &&
                                program == MessageToProgram(q.program_encoding) &&
                                ProgramValid(program) &&
                                Word32(q.answer_units * 2) &&
                                WellformedDiffPrivParameters(p) &&
                                DiffPrivParametersImplToGhost(p) == QueryParametersToDiffPrivParameters(q) &&
                                DiffPrivParametersValid(DiffPrivParametersImplToGhost(p)) &&
                                RV(budget) >= RV(p.beta) &&
                                Word32((num_randoms_needed-1)*32+1) &&
                                SufficientWordsForNoiseGeneration(DiffPrivParametersImplToGhost(p), num_randoms_needed) &&
                                num_randoms_needed <= num_randoms_available;
{
    lemma_2toX();

    error_code, program, p := ParseQueryParameters(q);
    if error_code != 0 {
        return;
    }

    //
    // See if there's sufficient budget.
    //

    var InsufficientPrivacyBudget:bool := BigRatGt(p.beta, budget);
    if InsufficientPrivacyBudget {
        error_code := ErrorInsufficientPrivacyBudget();
        return;
    }

    //
    // Determine how many random numbers we need.
    //

    error_code, num_randoms_needed := ComputeWordsForNoiseGeneration(p);
    if error_code == 0 && num_randoms_needed > num_randoms_available {
        error_code := ErrorInsufficientRandomness();
    }
}

method GenerateNoise (p:DiffPrivParametersImpl, randoms:seq<int>, budget:BigRat, num_randoms_needed:nat)
                     returns (negate_noise:bool, absolute_noise:nat, ghost noise:int,
                              remaining_budget:BigRat, remaining_randoms:seq<int>, ghost randoms_used:seq<int>)
    requires WellformedDiffPrivParameters(p);
    requires DiffPrivParametersValid(DiffPrivParametersImplToGhost(p));
    requires forall i :: 0 <= i < |randoms| ==> Word32(randoms[i]);
    requires WellformedBigRat(budget);
    requires |randoms| >= num_randoms_needed;
    requires Word32((num_randoms_needed-1)*32+1);
    requires SufficientWordsForNoiseGeneration(DiffPrivParametersImplToGhost(p), num_randoms_needed);
    requires RV(budget) >= RV(p.beta) >= real_of(1);
    ensures Word32(absolute_noise);
    ensures WellformedBigRat(remaining_budget);
    ensures forall i :: 0 <= i < |remaining_randoms| ==> Word32(remaining_randoms[i]);
    ensures forall i :: 0 <= i < |randoms_used| ==> Word32(randoms_used[i]);
    ensures noise == (if negate_noise then -absolute_noise else absolute_noise);
    ensures NoiseComputedCorrectly(DiffPrivParametersImplToGhost(p), randoms_used, noise);
    ensures randoms == randoms_used + remaining_randoms;
    ensures RV(remaining_budget) == RV(budget) / RV(p.beta);
{
    randoms_used := randoms[..num_randoms_needed];
    remaining_randoms := randoms[num_randoms_needed..];
    lemma_seq_split(randoms);
    assert randoms == randoms_used + remaining_randoms;

    // Compute the noise to use.

    negate_noise, absolute_noise, noise := ComputeNoise(p, randoms[..num_randoms_needed]);

    // Reduce the budget by beta.

    Lemma_IfBigRatGeOneItsNotZero(p.beta);
    remaining_budget := BigRatDiv(budget, p.beta);

    // Prove the remaining random numbers are all Word32's.

    forall i:int | 0 <= i < |remaining_randoms|
        ensures Word32(remaining_randoms[i]);
    {
        assert remaining_randoms[i] == randoms[num_randoms_needed + i];
        assert 0 <= num_randoms_needed + i < |randoms|;
        assert Word32(randoms[num_randoms_needed + i]);
    }

    // Prove the randoms used are all Word32's.

    forall i:int | 0 <= i < |randoms_used|
        ensures Word32(randoms_used[i]);
    {
        assert randoms_used[i] == randoms[i];
        assert Word32(randoms[i]);
    }

    assert SufficientWordsForNoiseGeneration(DiffPrivParametersImplToGhost(p), num_randoms_needed);
    assert SufficientWordsForNoiseGeneration(DiffPrivParametersImplToGhost(p), |randoms_used|);
}

method TestAnswerUnits (answer_units:int) returns (error_code:int)
    requires Word32(answer_units);
    ensures Word32(error_code);
    ensures error_code == 0 ==> Word32(answer_units * 2);
{
    lemma_2toX();
    error_code := if answer_units < 0x80000000 then 0 else ErrorAnswerUnitsTooLarge();
}

method AddNoise (ghost db:seq<Row>, ghost sum:int, answer:int, q:QueryParameters,
                 negate_noise:bool, absolute_noise:nat, ghost noise:int)
                returns (response:int)
    requires DatabaseValid(db);
    requires QueryParametersValid(q);
    requires QueryParametersAllWords(q);
    requires sum == MapperSum(db, MessageToProgram(q.program_encoding), q.row_min, q.row_max);
    requires answer == Clip(Scale(sum, q.answer_units), q.answer_min, q.answer_max);
    requires noise == if negate_noise then -absolute_noise else absolute_noise;
    requires Word32(absolute_noise);
    ensures Word32(response);
    ensures sum == MapperSum(db, MessageToProgram(q.program_encoding), q.row_min, q.row_max);
    ensures response == QueryResponse(db, q, noise);
{
    var noised_answer:int;
    if negate_noise {
        if (answer < absolute_noise) {
            noised_answer := 0;
        }
        else {
            noised_answer := answer - absolute_noise;
        }
    }
    else {
        noised_answer := SaturatingAdd(answer, absolute_noise);
    }

    //
    // Clip the noised answer to get the response.
    //

    response := Clip(noised_answer, q.answer_min, q.answer_max);
    Lemma_QueryResponseComputedCorrectly(db, sum, q, negate_noise, absolute_noise, noise, answer, noised_answer, response);    
}

//////////////////////////
// Lemmas
//////////////////////////

lemma {:timeLimit 30} Lemma_QueryPerformedCorrectly (old_state:GhostDiffPrivState, new_state:GhostDiffPrivState, q:QueryParameters,
                                                     p:GhostDiffPrivParameters, randoms_used:seq<int>, ghost noise:int,
                                                     error_code:int, response:int)
    requires GhostDiffPrivStateValid(old_state);
    requires QueryParametersValid(q);
    requires DiffPrivParametersValid(p);
    requires p == QueryParametersToDiffPrivParameters(q);
    requires forall i :: 0 <= i < |randoms_used| ==> Word32(randoms_used[i]);
    requires error_code == 0;
    requires Word32(response);
    requires old_state.budget >= p.beta >= real_of(1);
    requires new_state.db == old_state.db;
    requires new_state.budget == old_state.budget / p.beta;
    requires old_state.randoms == randoms_used + new_state.randoms;
    requires NoiseComputedCorrectly(p, randoms_used, noise);
    requires response == QueryResponse(old_state.db, q, noise);
    ensures QueryPerformedCorrectly(old_state, new_state, q, error_code, response);
{
    var program := MessageToProgram(q.program_encoding);
    Lemma_DividingBySmallerProducesAtLeastOne(old_state.budget, p.beta);

    assert QuerySuccessful(old_state, new_state, q, error_code, response, randoms_used, noise);

    forall i:int | 0 <= i < |new_state.randoms|
        ensures Word32(new_state.randoms[i]);
    {
        calc {
            old_state.randoms[|randoms_used| + i];
            (randoms_used + new_state.randoms)[|randoms_used|+i];
            { Lemma_IndexingIntoSequenceConcatenation(randoms_used, new_state.randoms, |randoms_used|+i); }
            new_state.randoms[|randoms_used|+i-|randoms_used|];
            new_state.randoms[i];
        }
        assert 0 <= |randoms_used| + i < |old_state.randoms|;
        assert Word32(old_state.randoms[|randoms_used|+i]);
    }
}

lemma Lemma_QueryResponseComputedCorrectly (ghost db:seq<Row>, ghost sum:int, q:QueryParameters,
                                            negate_noise:bool, absolute_noise:nat, ghost noise:int,
                                            answer:int, noised_answer:int, response:int)
    requires DatabaseValid(db);
    requires QueryParametersValid(q);
    requires QueryParametersAllWords(q);
    requires Word32(absolute_noise);
    requires Word32(answer);
    requires Word32(noised_answer);
    requires Word32(response);
    requires sum == MapperSum(db, MessageToProgram(q.program_encoding), q.row_min, q.row_max);
    requires answer == Clip(Scale(sum, q.answer_units), q.answer_min, q.answer_max);
    requires noise == if negate_noise then -absolute_noise else absolute_noise;
    requires noised_answer == (if negate_noise then
                                   (if answer < absolute_noise then 0 else answer - absolute_noise)
                               else
                                   SaturatingAdd(answer, absolute_noise));
    requires response == Clip(noised_answer, q.answer_min, q.answer_max);
    ensures response == QueryResponse(db, q, noise);
{
}

lemma Lemma_DividingBySmallerProducesAtLeastOne (x:real, y:real)
    requires x >= y > real_of(0);
    ensures x/y >= real_of(1);
{
}

lemma Lemma_DivideRoundingUpPreservesWord32 (x:int, m:int)
    requires Word32(x);
    requires m > 0;
    ensures Word32(DivideRoundingUp(x, m));
{
    if m == 1 {
        calc {
            DivideRoundingUp(x, m);
            (x / m) + (if x % m == 0 then 0 else 1);
            { Lemma_Mod1IsZero(x); }
            (x / m) + 0;
            x / m;
            { lemma_div_basics(x); }
            x;
        }
    }
    else {
        lemma_2toX();
        calc {
            0;
            <= { lemma_div_pos_is_pos(x, m); }
            x / m;
            <= (x / m) + (if x % m == 0 then 0 else 1);
            DivideRoundingUp(x, m);
       }
       calc {
            DivideRoundingUp(x, m);
            (x / m) + (if x % m == 0 then 0 else 1);
            <= (x / m) + 1;
            <= { lemma_div_is_ordered_by_denominator(x, 2, m); }
            INTERNAL_div(x, 2) + 1;
            { lemma_div_is_div_boogie_at_least_for_2(x); }
            (x / 2) + 1;
            <= power2(32) / 2 + 1;
        }
    }
}

lemma Lemma_Mod1IsZero (x:int)
    requires x >= 0;
    ensures INTERNAL_mod(x, 1) == 0;
{
    reveal_mod_recursive();
    if x >= 1 {
        Lemma_Mod1IsZero(x-1);
    }
}

lemma Lemma_IfBigRatGeOneItsNotZero (Q:BigRat)
    requires WellformedBigRat(Q);
    requires RV(Q) >= real_of(1);
    ensures nonzero(Q.n.value);
{
    if !nonzero(Q.n.value) {
        calc {
            RV(Q);
            real_of(BV(Q.n)) / real_of(I(Q.d));
            real_of(0) / real_of(I(Q.d));
            real_of(0);
        }
        assert false;
    }
}

lemma Lemma_IndexingIntoSequenceConcatenation (seq1:seq<int>, seq2:seq<int>, i:nat)
    requires |seq1| <= i < |seq1| + |seq2|;
    ensures (seq1 + seq2)[i] == seq2[i-|seq1|];
{
}
