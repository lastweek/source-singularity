include "../../../../Checked/Libraries/BigNum/Word32.dfy"

function RealPower(x:real, e:nat) : real
    decreases e;
{
    if e == 0 then real_of(1) else x * RealPower(x, e-1)
}

function RealMin(a:real, b:real) : real
{
    if a < b then a else b
}

datatype GhostDiffPrivParameters = GhostDiffPrivParameters_ctor(alpha:real, beta:real, delta:int, B:int);

function DiffPrivParametersValid (p:GhostDiffPrivParameters) : bool
{
    p.delta >= 0 &&
    p.alpha > real_of(1) &&
    p.beta > RealPower(p.alpha, p.delta) &&
    p.B > 0 &&
    p.beta >= real_of(1)
}

function RequiredNoiseEntropy (p:GhostDiffPrivParameters) : real
    requires DiffPrivParametersValid(p);
{
    var One := real_of(1);
    var Two := real_of(2);
    (p.alpha + One) * (p.beta + One) * RealPower(p.alpha, p.B - 1) / ((p.beta - RealPower(p.alpha, p.delta)) * RealMin(p.alpha - One, Two))
}

function SufficientWordsForNoiseGeneration (p:GhostDiffPrivParameters, words:nat) : bool
    requires DiffPrivParametersValid(p);
{
    words >= 1 && real_of(power2(words * 32 - 31)) >= RequiredNoiseEntropy(p) // We need 31 extra bits because we use an entire word for the sign bit.
}

function NoiseThreshold (alpha:real, u:real) : real
    requires u > real_of(0);
    requires alpha > real_of(1);
{
    (real_of(2) * alpha) / (u * (alpha + real_of(1)))
}

function IntegerFromSequenceOfWords (words:seq<int>) : int
{
    if |words| == 0 then 0 else power2(32) * IntegerFromSequenceOfWords(words[1..]) + words[0]
}

function ShouldNegateNoise (randoms:seq<int>) : bool
    requires |randoms| > 0;
{
    (randoms[0] % 2 == 1)
}

function GetUniformBetweenZeroAndOne (randoms:seq<int>) : real
    requires |randoms| > 0;
{
    (real_of(IntegerFromSequenceOfWords(randoms[1..])) + real_of(1) / real_of(2)) / real_of(power2((|randoms|-1)*32))
}

function NoiseOK (p:GhostDiffPrivParameters, randoms:seq<int>, u:real, negate_noise:bool, absolute_noise:nat, noise:int) : bool
    requires DiffPrivParametersValid(p);
{
    u > real_of(0) &&
    RealPower(p.alpha, absolute_noise) <= NoiseThreshold(p.alpha, u) &&
    (absolute_noise == p.B || RealPower(p.alpha, absolute_noise + 1) > NoiseThreshold(p.alpha, u)) &&
    noise == (if negate_noise then -absolute_noise else absolute_noise)
}

function NoiseComputedCorrectly (p:GhostDiffPrivParameters, randoms:seq<int>, noise:int) : bool
    requires DiffPrivParametersValid(p);
{
    SufficientWordsForNoiseGeneration(p, |randoms|) &&
    exists absolute_noise:nat :: NoiseOK(p, randoms, GetUniformBetweenZeroAndOne(randoms), ShouldNegateNoise(randoms), absolute_noise, noise)
}
