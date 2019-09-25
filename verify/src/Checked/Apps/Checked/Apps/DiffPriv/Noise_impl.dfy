include "../../../Trusted/Spec/Apps/DiffPriv/Noise_spec.dfy"
include "../../Libraries/BigNum/BigRat.dfy"
include "../../Libraries/Math/round.dfy"
include "ErrorCodes.dfy"

datatype DiffPrivParametersImpl = DiffPrivParametersImpl_ctor(alpha:BigRat, beta:BigRat, delta:int, B:int);

function WellformedDiffPrivParameters (p:DiffPrivParametersImpl) : bool
{
    WellformedBigRat(p.alpha) && WellformedBigRat(p.beta) && Word32(p.delta) && Word32(p.B)
}

function DiffPrivParametersImplToGhost (p:DiffPrivParametersImpl) : GhostDiffPrivParameters
    requires WellformedDiffPrivParameters(p);
{
    GhostDiffPrivParameters_ctor(RV(p.alpha), RV(p.beta), p.delta, p.B)
}

method BigRatPower(x:BigRat, e:int) returns (r:BigRat)
    requires WellformedBigRat(x);
    requires e >= 0;
    ensures WellformedBigRat(r);
    ensures RV(r) == RealPower(RV(x), e);
{
    r := MakeSmallLiteralBigRat(1);

    var k := 0;
    while k < e
        invariant 0 <= k <= e;
        invariant WellformedBigRat(r);
        invariant RV(r) == RealPower(RV(x), k);
    {
        r := BigRatMul(r, x);
        k := k + 1;
    }
}

method BigRatMin (a:BigRat, b:BigRat) returns (r:BigRat)
    requires WellformedBigRat(a);
    requires WellformedBigRat(b);
    ensures WellformedBigRat(r);
    ensures RV(r) == RealMin(RV(a), RV(b));
{
    var a_less_than_b:bool := BigRatLt(a, b);
    if (a_less_than_b) {
        r := a;
    }
    else {
        r := b;
    }
}

method {:timeLimit 20} FindHigherPowerOfTwo (y:BigRat) returns (success:bool, x:nat)
    requires WellformedBigRat(y);
    ensures Word32(x);
    ensures success ==> real_of(power2(x)) >= RV(y);
{
    lemma_2toX();
    reveal_power2();

    x := 0;
    var two_to_x:BigNat := MakeSmallLiteralBigNat(1);
    var two:BigNat := MakeSmallLiteralBigNat(2);
    var BigRat_two_to_x:BigRat;

    while x < 0xFFFFFFFF
        invariant Word32(x);
        invariant WellformedBigNat(two_to_x);
        invariant I(two_to_x) == power2(x);
    {
        var done:bool := BigRatGe(BigNatToBigRat(two_to_x), y);
        if (done) { 
            success := true;
            return;
        }
        ghost var old_two_to_x := two_to_x;
        two_to_x := BigNatMul(two, two_to_x);
        calc {
            I(two_to_x);
            I(two) * I(old_two_to_x);
            I(two) * power2(x);
            { lemma_mul_is_mul_boogie(I(two), power2(x)); }
            2 * power2(x);
            power2(x+1);
        }
        x := x + 1;
    }

    // At the end of the loop, handle the case of x == 0xFFFFFFFF.

    success := BigRatGe(BigNatToBigRat(two_to_x), y);
}

method DetermineIfDiffPrivParametersValid (p:DiffPrivParametersImpl) returns (error_code:int)
    requires WellformedDiffPrivParameters(p);
    requires p.delta >= 0;
    ensures Word32(error_code);
    ensures error_code == 0 <==> DiffPrivParametersValid(DiffPrivParametersImplToGhost(p));
{
    lemma_2toX();

    if p.B <= 0 {
        error_code := ErrorAnswerRangeNotPositive();
        return;
    }

    var One := MakeSmallLiteralBigRat(1);
    var AlphaLeOne:bool := BigRatLe(p.alpha, One);
    if (AlphaLeOne) {
        error_code := ErrorAlphaNotGreaterThanOne();
        return;
    }

    var AlphaToDelta := BigRatPower(p.alpha, p.delta);
    var BetaLeAlphaToDelta := BigRatLe(p.beta, AlphaToDelta);
    if (BetaLeAlphaToDelta) {
        error_code := ErrorBetaNotGreaterThanAlphaToPowerOfSensitivity();
        return;
    }

    Lemma_RealPowerPreservesGeOne(RV(p.alpha), p.delta);
    error_code := 0;
}

method {:timeLimit 60} ComputeRequiredNoiseEntropyPart1 (p:DiffPrivParametersImpl) returns (entropy:BigRat)
    requires WellformedDiffPrivParameters(p);
    requires DiffPrivParametersValid(DiffPrivParametersImplToGhost(p));
    ensures WellformedBigRat(entropy);
    ensures RV(entropy) == RequiredNoiseEntropyPart1(DiffPrivParametersImplToGhost(p));
{
    lemma_2toX();
    var One := MakeSmallLiteralBigRat(1);
    var Two := MakeSmallLiteralBigRat(2);
    var AlphaPlusOne := BigRatAdd(p.alpha, One);
    var BetaPlusOne := BigRatAdd(p.beta, One);
    var AlphaToDelta := BigRatPower(p.alpha, p.delta);
    var BetaMinusAlphaToDelta := BigRatSub(p.beta, AlphaToDelta);
    var Numerator := BigRatMul(AlphaPlusOne, BetaPlusOne);
    var AlphaMinusOne := BigRatSub(p.alpha, One);
    var MinAlphaMinusOneAndTwo := BigRatMin(AlphaMinusOne, Two);
    var Denominator := BigRatMul(BetaMinusAlphaToDelta, MinAlphaMinusOneAndTwo);
    entropy := BigRatDiv(Numerator, Denominator);

    Lemma_RequiredNoiseEntropyPart1Correct(DiffPrivParametersImplToGhost(p), RV(AlphaPlusOne), RV(BetaPlusOne),
                                           RV(One), RV(Two), RV(AlphaToDelta), RV(BetaMinusAlphaToDelta),
                                           RV(Numerator), RV(AlphaMinusOne), RV(MinAlphaMinusOneAndTwo), RV(Denominator), RV(entropy));
}

method ComputeWordsForNoiseGeneration (p:DiffPrivParametersImpl) returns (error_code:int, words:nat)
    requires WellformedDiffPrivParameters(p);
    requires DiffPrivParametersValid(DiffPrivParametersImplToGhost(p));
    ensures Word32(error_code);
    ensures error_code == 0 ==> Word32((words-1)*32+1) && SufficientWordsForNoiseGeneration(DiffPrivParametersImplToGhost(p), words);
    ensures error_code != 0 ==> words == 0;
{
    lemma_2toX();

    var entropy_part_1 := ComputeRequiredNoiseEntropyPart1(p);
    var success, r1 := FindHigherPowerOfTwo(entropy_part_1);
    if !success || r1 >= 0xFFFFFFE0 {
        error_code := ErrorRequiresTooManyBitsOfRandomness();
        words := 0;
        return;
   }

    var log_alpha:nat;
    success, log_alpha := FindHigherPowerOfTwo(p.alpha);
    if !success || log_alpha > 0xFFFFFFFF / p.B {
        error_code := ErrorRequiresTooManyBitsOfRandomness();
        words := 0;
        return;
    }
    lemma_mul_positive(log_alpha, p.B-1);
    var r2:nat := log_alpha * (p.B-1);
    Lemma_SufficientR2(RV(p.alpha), p.B, log_alpha, r2);

    if r2 >= 0xFFFFFFE0 - r1 {
        error_code := ErrorRequiresTooManyBitsOfRandomness();
        words := 0;
        return;
    }
   
    error_code := 0;
    var min_r := r1 + r2 + 31;      // need 31 extra bits so we can use an entire word for the sign bit
    var r := RoundUpToMultiple(min_r, 32);
    Lemma_Mod32IsMod32(r);
    words := r / 32;
    Lemma_RealPowerPreservesPositivity(RV(p.alpha), p.B-1);
    Lemma_BreakdownOfSufficientWordsForNoiseGeneration(DiffPrivParametersImplToGhost(p), r1, r2, words);
}

method BigNatPower2 (e:nat) returns (r:BigNat)
    requires Word32(e+1);
    ensures WellformedBigNat(r);
    ensures I(r) == power2(e);
{
    lemma_2toX();
    reveal_power2();
    var One := MakeSmallLiteralBigNat(1);
    ghost var rc:nat;
    r, rc := BigNatBitShift_(One, 1, e);
    lemma_mul_is_mul_boogie(power2(e), I(One));
}

method FindHighestPowerLeThreshold (alpha:BigRat, threshold:BigRat, max_power:nat, ghost u:BigRat) returns (e:nat)
    requires WellformedBigRat(alpha);
    requires WellformedBigRat(threshold);
    requires Word32(max_power);
    requires WellformedBigRat(u);
    requires RV(u) > real_of(0);
    requires RV(alpha) > real_of(1);
    requires RV(threshold) >= real_of(1);
    requires RV(threshold) == NoiseThreshold(RV(alpha), RV(u));
    ensures RealPower(RV(alpha), e) <= RV(threshold);
    ensures e == max_power || RealPower(RV(alpha), e+1) > RV(threshold);
    ensures Word32(e);
    ensures RV(threshold) == NoiseThreshold(RV(alpha), RV(u));
{
    var alpha_to_e := MakeSmallLiteralBigRat(1);
    e := 0;

    while e < max_power
        invariant 0 <= e <= max_power;
        invariant WellformedBigRat(alpha_to_e);
        invariant RV(alpha_to_e) == RealPower(RV(alpha), e);
        invariant RV(alpha_to_e) <= RV(threshold);
    {
        alpha_to_e := BigRatMul(alpha, alpha_to_e);
        var done := BigRatGt(alpha_to_e, threshold);
        if (done) {
            assert RealPower(RV(alpha), e+1) == RV(alpha_to_e) > RV(threshold);
            return;
        }
        e := e + 1;
    }
}

method {:timeLimit 60} DeriveRandomValues (randoms:seq<int>) returns (negate_noise:bool, u:BigRat)
    requires |randoms| > 0;
    requires Word32((|randoms|-1) * 32 + 1);
    requires forall i :: 0 <= i < |randoms| ==> Word32(randoms[i]);
    ensures WellformedBigRat(u);
    ensures negate_noise == ShouldNegateNoise(randoms);
    ensures RV(u) == GetUniformBetweenZeroAndOne(randoms);
    ensures real_of(0) < RV(u) <= real_of(1);
{
    negate_noise := (randoms[0] % 2 == 1);

    lemma_2toX();
    var U:BigNat := TruncatingBigNatCtor_impl(randoms[1..]);
    Lemma_VIsIntegerFromSequenceOfWords(randoms[1..]);
    assert I(U) == IntegerFromSequenceOfWords(randoms[1..]);
    var OneHalf:BigRat := BigRat_ctor(MakeSmallLiteralBigNum(1), MakeSmallLiteralBigNat(2));
    var Numerator:BigRat := BigRatAdd(BigNatToBigRat(U), OneHalf);
    var Denominator:BigNat := BigNatPower2((|randoms|-1)*32);
    u := BigRatDiv(Numerator, BigNatToBigRat(Denominator));
    assert WellformedBigRat(u);

    Lemma_RandomDerivationsCorrect(randoms, RV(u), negate_noise, I(U), RV(OneHalf), RV(Numerator), I(Denominator));
}

method ComputeNoiseThreshold (alpha:BigRat, u:BigRat) returns (Threshold:BigRat)
    requires WellformedBigRat(alpha);
    requires WellformedBigRat(u);
    requires RV(alpha) > real_of(1);
    requires real_of(0) < RV(u) <= real_of(1);
    ensures WellformedBigRat(Threshold);
    ensures RV(Threshold) == NoiseThreshold(RV(alpha), RV(u));
    ensures RV(Threshold) >= real_of(1);
{
    lemma_2toX();

    var ThresholdNumerator := BigRatMul(MakeSmallLiteralBigRat(2), alpha);
    var AlphaPlusOne := BigRatAdd(alpha, MakeSmallLiteralBigRat(1));
    var ThresholdDenominator := BigRatMul(u, AlphaPlusOne);

    Threshold := BigRatDiv(ThresholdNumerator, ThresholdDenominator);
    Lemma_ThresholdCorrect(RV(alpha), RV(u), RV(ThresholdNumerator), RV(AlphaPlusOne), RV(ThresholdDenominator), RV(Threshold));
    Lemma_ThresholdGeOne(RV(alpha), RV(u), RV(Threshold));
}

method {:timeLimit 60} ComputeNoise (p:DiffPrivParametersImpl, randoms:seq<int>)
                                    returns (negate_noise:bool, absolute_noise:int, ghost noise:int)
    requires WellformedDiffPrivParameters(p);
    requires forall i :: 0 <= i < |randoms| ==> Word32(randoms[i]);
    requires DiffPrivParametersValid(DiffPrivParametersImplToGhost(p));
    requires Word32((|randoms|-1)*32+1);
    requires SufficientWordsForNoiseGeneration(DiffPrivParametersImplToGhost(p), |randoms|);
    ensures Word32(absolute_noise);
    ensures noise == if negate_noise then -absolute_noise else absolute_noise;
    ensures NoiseComputedCorrectly(DiffPrivParametersImplToGhost(p), randoms, noise);
{
    var u:BigRat;
    negate_noise, u := DeriveRandomValues(randoms);
    assert RV(u) == GetUniformBetweenZeroAndOne(randoms);
    var Threshold := ComputeNoiseThreshold(p.alpha, u);
    absolute_noise := FindHighestPowerLeThreshold(p.alpha, Threshold, p.B, u);
    assert RV(Threshold) == NoiseThreshold(RV(p.alpha), RV(u));
    noise := if negate_noise then -absolute_noise else absolute_noise;

    Lemma_NoiseComputedCorrectlyFromRandomValues(DiffPrivParametersImplToGhost(p), randoms, RV(u), negate_noise, absolute_noise, noise);
}

lemma {:timeLimit 30} Lemma_RequiredNoiseEntropyPart1Correct (p:GhostDiffPrivParameters, AlphaPlusOne:real, BetaPlusOne:real,
                                                              One:real, Two:real, AlphaToDelta:real, BetaMinusAlphaToDelta:real,
                                                              Numerator:real, AlphaMinusOne:real, MinAlphaMinusOneAndTwo:real, Denominator:real,
                                                              entropy:real)
    requires Word32(p.delta);
    requires Word32(p.B);
    requires DiffPrivParametersValid(p);
    requires One == real_of(1);
    requires Two == real_of(2);
    requires AlphaPlusOne == p.alpha + One;
    requires BetaPlusOne == p.beta + One;
    requires AlphaToDelta == RealPower(p.alpha, p.delta);
    requires BetaMinusAlphaToDelta == p.beta - AlphaToDelta;
    requires Numerator == AlphaPlusOne * BetaPlusOne;
    requires AlphaMinusOne == p.alpha - One;
    requires MinAlphaMinusOneAndTwo == RealMin(AlphaMinusOne, Two);
    requires Denominator == BetaMinusAlphaToDelta * MinAlphaMinusOneAndTwo;
    requires Denominator != real_of(0);
    requires entropy == Numerator / Denominator;
    ensures entropy == RequiredNoiseEntropyPart1(p);
{
    calc {
        entropy;
        Numerator / Denominator;
        (AlphaPlusOne * BetaPlusOne) / Denominator;
        ((p.alpha + One) * BetaPlusOne) / Denominator;
        ((p.alpha + One) * (p.beta + One)) / Denominator;
        ((p.alpha + One) * (p.beta + One)) / (BetaMinusAlphaToDelta * MinAlphaMinusOneAndTwo);
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - AlphaToDelta) * MinAlphaMinusOneAndTwo);
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - RealPower(p.alpha, p.delta)) * MinAlphaMinusOneAndTwo);
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(AlphaMinusOne, Two));
        ((p.alpha + One) * (p.beta + One)) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - One, Two));
    }
}

lemma Lemma_SufficientWordsForNoiseGeneration (p:GhostDiffPrivParameters, entropy:real, log_entropy:nat, min_r:nat, r:nat, words:int)
    requires Word32(p.delta);
    requires Word32(p.B);
    requires DiffPrivParametersValid(p);
    requires entropy == RequiredNoiseEntropy(p);
    requires real_of(power2(log_entropy)) >= entropy;
    requires min_r == log_entropy + 31;
    requires Word32(r);
    requires r >= min_r;
    requires r % 32 == 0;
    requires words == r / 32;
    ensures SufficientWordsForNoiseGeneration(p, words);
{
    lemma_power2_increases(min_r - 31, r - 31);
}

lemma Lemma_RealPowerPreservesGeOne (x:real, e:nat)
    requires x >= real_of(1);
    ensures RealPower(x, e) >= real_of(1);
    decreases e;
{
    if e != 0 {
        Lemma_RealPowerPreservesGeOne(x, e-1);
    }
}

lemma Lemma_VIsIntegerFromSequenceOfWords (s:seq<int>)
    ensures V(s) == IntegerFromSequenceOfWords(s);
{
    reveal_V();
    if |s| != 0 {
        Lemma_VIsIntegerFromSequenceOfWords(s[1..]);
    }
}

lemma Lemma_RandomDerivationsCorrect (randoms:seq<int>, u:real, negate_noise:bool, U:nat, OneHalf:real, Numerator:real, Denominator:nat)
    requires |randoms| > 0;
    requires forall i :: 0 <= i < |randoms| ==> Word32(randoms[i]);
    requires negate_noise == (randoms[0] % 2 == 1);
    requires U == IntegerFromSequenceOfWords(randoms[1..]);
    requires OneHalf == real_of(1) / real_of(2);
    requires Numerator == real_of(U) + OneHalf;
    requires Denominator == power2((|randoms|-1)*32);
    requires u == Numerator / real_of(Denominator);
    ensures u == GetUniformBetweenZeroAndOne(randoms);
    ensures real_of(0) < u <= real_of(1);
    decreases U;
{
    calc {
        u;
        Numerator / real_of(Denominator);
        (real_of(U) + OneHalf) / real_of(Denominator);
        <= { Lemma_IntegerFromSequenceOfWordsBounded(randoms[1..]);
          assert U <= power2((|randoms|-1)*32) - 1;
          assert real_of(U) <= real_of(power2((|randoms|-1)*32) - 1); }
        (real_of(power2((|randoms|-1)*32) - 1) + OneHalf) / real_of(Denominator);
        (real_of(power2((|randoms|-1)*32) - 1) + real_of(1) / real_of(2)) / real_of(Denominator);
        (real_of(power2((|randoms|-1)*32) - 1) + real_of(1) / real_of(2)) / real_of(power2((|randoms|-1)*32));
        < real_of(power2((|randoms|-1)*32)) / real_of(power2((|randoms|-1)*32));
        real_of(1);
    }
}

lemma Lemma_ThresholdCorrect (alpha:real, u:real, ThresholdNumerator:real, AlphaPlusOne:real, ThresholdDenominator:real, Threshold:real)
    requires u > real_of(0);
    requires alpha > real_of(1);
    requires ThresholdNumerator == real_of(2) * alpha;
    requires AlphaPlusOne == alpha + real_of(1);
    requires ThresholdDenominator == u * AlphaPlusOne;
    requires Threshold == ThresholdNumerator / ThresholdDenominator;
    ensures Threshold == NoiseThreshold(alpha, u);
{
}

lemma Lemma_NoiseComputedCorrectlyFromRandomValues (p:GhostDiffPrivParameters, randoms:seq<int>,
                                                    u:real, negate_noise:bool, absolute_noise:nat, ghost noise:int)
    requires DiffPrivParametersValid(p);
    requires p.alpha > real_of(1);
    requires u > real_of(0);
    requires SufficientWordsForNoiseGeneration(p, |randoms|);
    requires negate_noise == ShouldNegateNoise(randoms);
    requires u == GetUniformBetweenZeroAndOne(randoms);
    requires RealPower(p.alpha, absolute_noise) <= NoiseThreshold(p.alpha, u);
    requires (absolute_noise == p.B || RealPower(p.alpha, absolute_noise + 1) > NoiseThreshold(p.alpha, u));
    requires noise == if negate_noise then -absolute_noise else absolute_noise;
    ensures NoiseComputedCorrectly(p, randoms, noise);
{
    assert NoiseOK(p, randoms, u, negate_noise, absolute_noise, noise);
}

lemma Lemma_ThresholdGeOne (alpha:real, u:real, threshold:real)
    requires real_of(1) >= u > real_of(0);
    requires alpha > real_of(1);
    requires threshold == NoiseThreshold(alpha, u);
    ensures threshold >= real_of(1);
{
    calc {
        threshold;
        (real_of(2) * alpha) / (u * (alpha + real_of(1)));
        (alpha + alpha) / (u * (alpha + real_of(1)));
        (alpha + alpha) / (u * (alpha + real_of(1)));
        (alpha + alpha) / (alpha + real_of(1)) / u;
        >= real_of(1) / u;
        >= real_of(1);
    }
}

lemma Lemma_IntegerFromSequenceOfWordsBounded (s:seq<int>)
    requires forall i :: 0 <= i < |s| ==> Word32(s[i]);
    ensures IntegerFromSequenceOfWords(s) < power2(|s|*32);
{
    if |s| != 0 {
        calc {
            IntegerFromSequenceOfWords(s);
            power2(32) * IntegerFromSequenceOfWords(s[1..]) + s[0];
            <= { lemma_mul_inequality(IntegerFromSequenceOfWords(s[1..]), power2((|s|-1)*32)-1, power2(32));
                 lemma_mul_commutative(power2(32), IntegerFromSequenceOfWords(s[1..]));
                 lemma_mul_commutative(power2(32), power2((|s|-1)*32)-1); }
            power2(32) * (power2((|s|-1)*32) - 1) + s[0];
            { lemma_mul_is_distributive_sub(power2(32), power2((|s|-1)*32), 1);
              lemma_mul_is_mul_boogie(power2(32), power2((|s|-1)*32) - 1);
              lemma_mul_is_mul_boogie(power2(32), power2((|s|-1)*32)); }
            power2(32) * power2((|s|-1)*32) - power2(32) + s[0];
            { lemma_power2_adds(32, (|s|-1)*32); }
            power2(32 + (|s|-1)*32) - power2(32) + s[0];
            power2(|s|*32) - power2(32) + s[0];
            < power2(|s|*32);
        }
    }
}

lemma Lemma_Mod32IsMod32 (x:nat)
    ensures x % 32 == INTERNAL_mod(x, 32);
{
    reveal_INTERNAL_mod_recursive();

    if x >= 32 {
        Lemma_Mod32IsMod32(x - 32);
    }
}

function RequiredNoiseEntropyPart1 (p:GhostDiffPrivParameters) : real
    requires DiffPrivParametersValid(p);
{
    var One := real_of(1);
    var Two := real_of(2);
    (p.alpha + One) * (p.beta + One) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - One, Two))
}

lemma Lemma_SufficientR2 (alpha:real, B:int, log_alpha:nat, r2:nat)
    requires B > 0;
    requires alpha > real_of(1);
    requires real_of(power2(log_alpha)) >= alpha;
    requires r2 >= log_alpha * (B-1);
    ensures real_of(power2(r2)) >= RealPower(alpha, B-1);
    decreases B;
{
    if B > 1 {
        calc {
            r2 - log_alpha;
            >= log_alpha * (B-1) - log_alpha;
            log_alpha * (B-1) - log_alpha * 1;
            { lemma_mul_is_distributive_sub(log_alpha, B-1, 1); lemma_mul_is_mul_boogie(log_alpha, 1); }
            log_alpha * (B-1 - 1);
            log_alpha * (B-2);
        }
        lemma_mul_positive(log_alpha, B-2);
        assert r2 - log_alpha >= log_alpha * (B-2) >= 0;
        Lemma_SufficientR2(alpha, B-1, log_alpha, r2 - log_alpha);
        assert real_of(power2(r2 - log_alpha)) >= RealPower(alpha, B-2);
        calc {
            real_of(power2(r2));
            { lemma_power2_adds(log_alpha, r2-log_alpha); }
            real_of(power2(log_alpha) * power2(r2-log_alpha));
            { Lemma_RealOfMultiplyIsMultiply(power2(log_alpha), power2(r2-log_alpha)); }
            real_of(power2(log_alpha)) * real_of(power2(r2-log_alpha));
            >= alpha * real_of(power2(r2-log_alpha));
            >= alpha * RealPower(alpha, B-2);
            RealPower(alpha, B-1);
        }
    }
}

lemma Lemma_BreakdownOfSufficientWordsForNoiseGeneration (p:GhostDiffPrivParameters, r1:nat, r2:nat, words:nat)
    requires DiffPrivParametersValid(p);
    requires ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - real_of(1), real_of(2))) != real_of(0);
    requires real_of(power2(r1)) >= RequiredNoiseEntropyPart1(p);
    requires real_of(power2(r2)) >= RealPower(p.alpha, p.B - 1) > real_of(0);
    requires words >= 1;
    requires words * 32 - 31 >= r1 + r2;
    ensures SufficientWordsForNoiseGeneration(p, words);
    decreases r1;
{
    var One := real_of(1);
    var Two := real_of(2);

    calc {
        real_of(power2(words * 32 - 31));
        >= { lemma_power2_increases(r1 + r2, words * 32 - 31); }
        real_of(power2(r1 + r2));
        { lemma_power2_adds(r1, r2); }
        real_of(power2(r1) * power2(r2));
        { Lemma_RealOfMultiplyIsMultiply(power2(r1), power2(r2)); }
        real_of(power2(r1)) * real_of(power2(r2));
        >= RequiredNoiseEntropyPart1(p) * real_of(power2(r2));
        >= RequiredNoiseEntropyPart1(p) * RealPower(p.alpha, p.B - 1);
        (p.alpha + One) * (p.beta + One) * RealPower(p.alpha, p.B - 1) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - One, Two));
        RequiredNoiseEntropy(p);
    }
}

lemma Lemma_RealPowerPreservesPositivity (x:real, e:nat)
    requires x > real_of(0);
    ensures RealPower(x, e) > real_of(0);
    decreases e;
{
    if e > 0 {
        Lemma_RealPowerPreservesPositivity(x, e-1);
    }
}
