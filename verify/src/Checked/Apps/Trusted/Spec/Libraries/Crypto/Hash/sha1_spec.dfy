include "sha_common.dfy"

/////////////////////////////////////////////////////
// Constants
/////////////////////////////////////////////////////

static function method K(n: int) : int
    requires 0 <= n <= 79;
    ensures Word32(K(n));
{
    reveal_power2();
    if 0 <= n <= 19 then
        0x5a827999
    else if 20 <= n <= 39 then
        0x6ed9eba1
    else if 40 <= n <= 59 then
        0x8f1bbcdc
    else
        0xca62c1d6
}

static function method InitialHValue(index: int) : int
    requires 0 <= index <= 4;
    ensures Word32(InitialHValue(index));
{
    reveal_power2();
    [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0][index]
}

/////////////////////////////////////////////////////
// Intermediate SHA-1 values
/////////////////////////////////////////////////////

//
// Processing message block #i proceeds in 130 steps:
//
// Step 1 initializes a-h.
// Each step 2, 4, 6, 8, ..., 160 computes T from the a-e computed in the previous step.
// Each step 3, 5, 7, 9, ..., 161 computes a-e from the T computed in the previous step.
// Step 162 computes H^(i) from the final values of a-e.
//

static function W(t: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= i <= NumBlocks(m);
    requires 0 <= t <= 79;
    ensures Word32(W(t, i, m));
{
    if t <= 15 then
        PaddedMessageWord(t, i, Pad(m))
    else
        RotateLeftInstruction(BitwiseXorInstruction(BitwiseXorInstruction(BitwiseXorInstruction(W(t-3, i, m),
                                                                                                W(t-8, i, m)),
                                                                          W(t-14, i, m)),
                                                    W(t-16, i, m)),
                              1)
}

static function T(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 2 <= step <= 160;
    requires step % 2 == 0;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(T(step, i, m));
    decreases i, step;
{
    var t := step/2 - 1;
    AddInstruction(AddInstruction(AddInstruction(AddInstruction(RotateLeftInstruction(a(step-1, i, m), 5),
                                                                ft(t, b(step-1, i, m), c(step-1, i, m), d(step-1, i, m))),
                                                 e(step-1, i, m)),
                                  K(t)),
                   W(t, i, m))
}

static function {:hidden} a(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 161;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(a(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(0, i-1, m)
    else
        T(step-1, i, m)
}

static function b(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 161;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(b(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(1, i-1, m)
    else
        a(step-2, i, m)
}

static function c(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 161;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(c(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(2, i-1, m)
    else
        RotateLeftInstruction(b(step-2, i, m), 30)
}

static function d(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 161;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(d(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(3, i-1, m)
    else
        c(step-2, i, m)
}

static function {:hidden} e(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 161;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(e(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(4, i-1, m)
    else
        d(step-2, i, m)
}

static function {:hidden} H(subscript: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 0 <= subscript <= 4;
    requires 0 <= i <= NumBlocks(m); // Note that i can be 0
    ensures Word32(H(subscript, i, m));
    decreases i;
{
    if i == 0 then
        InitialHValue(subscript)
    else if subscript == 0 then
        AddInstruction(a(161, i, m), H(subscript, i-1, m))
    else if subscript == 1 then
        AddInstruction(b(161, i, m), H(subscript, i-1, m))
    else if subscript == 2 then
        AddInstruction(c(161, i, m), H(subscript, i-1, m))
    else if subscript == 3 then
        AddInstruction(d(161, i, m), H(subscript, i-1, m))
    else
        AddInstruction(e(161, i, m), H(subscript, i-1, m))
}

/////////////////////////////////////////////////////
// Final SHA-1 calculation
/////////////////////////////////////////////////////

static function {:hidden} SHA1(m: seq<bool>) : seq<int> // returns a sequence of 32-bit values
    requires |m| < power2(64);
    ensures |SHA1(m)| == 5;
    ensures forall i :: 0 <= i < |SHA1(m)| ==> Word32(SHA1(m)[i]);
{
    SHA1_is_words(m);
    [H(0, NumBlocks(m), m), H(1, NumBlocks(m), m), H(2, NumBlocks(m), m), H(3, NumBlocks(m), m), H(4, NumBlocks(m), m)]
}

static lemma {:timeLimit 60} SHA1_is_words(m: seq<bool>)
    requires |m| < power2(64);
    ensures var hash := [H(0, NumBlocks(m), m), H(1, NumBlocks(m), m), H(2, NumBlocks(m), m), H(3, NumBlocks(m), m), H(4, NumBlocks(m), m)];
            forall i :: 0 <= i < |hash| ==> Word32(hash[i]);
{
    ghost var hash := [H(0, NumBlocks(m), m), H(1, NumBlocks(m), m), H(2, NumBlocks(m), m), H(3, NumBlocks(m), m), H(4, NumBlocks(m), m)];
    assert forall subscript :: 0 <= subscript <= 4 ==> Word32(H(subscript, NumBlocks(m), m));
    forall i | 0 <= i < |hash| {
        calc ==> {
            true;
            hash[i] == H(i, NumBlocks(m), m);
            Word32(hash[i]);
        }
    }
}

/////////////////////////////////////////////////////////////////////////////////
// HMAC specification based on:
// http://csrc.nist.gov/publications/fips/fips198-1/FIPS-198-1_final.pdf
/////////////////////////////////////////////////////////////////////////////////

static function HMAC(k: seq<bool>, m: seq<bool>) : seq<int>
    requires |k| == 512;
    requires |m| < power2(64) - 8*64;
{
    reveal_power2();
    SHA1( SeqXor(k, Opad(|k|)) + WordSeqToBits(SHA1(SeqXor(k, Ipad(|k|)) + m)) )
}
