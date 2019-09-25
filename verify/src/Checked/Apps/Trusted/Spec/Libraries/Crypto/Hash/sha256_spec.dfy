include "sha_common.dfy"

/////////////////////////////////////////////////////
// Constants
/////////////////////////////////////////////////////

static function method K(n: int) : int
    requires 0 <= n <= 63;
    ensures Word32(K(n));
{
    reveal_power2();
    [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2][n]
}

static function method InitialHValue(index: int) : int
    requires 0 <= index <= 7;
    ensures Word32(InitialHValue(index));
{
    reveal_power2();
    [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19][index]
}

/////////////////////////////////////////////////////
// Intermediate SHA-256 values
/////////////////////////////////////////////////////

//
// Processing message block #i proceeds in 130 steps:
//
// Step 1 initializes a-h.
// Each step 2, 4, 6, 8, ..., 128 computes T1 and T2 from the a-h computed in the previous step.
// Each step 3, 5, 7, 9, ..., 129 computes a-h from the T1 and T2 computed in the previous step.
// Step 130 computes H^(i) from the final values of a-h.
//

static function W(t: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= i <= NumBlocks(m);
    requires 0 <= t <= 63;
    ensures Word32(W(t, i, m));
{
    if t <= 15 then
        PaddedMessageWord(t, i, Pad(m))
    else
        AddInstruction(AddInstruction(AddInstruction(SSIG1(W(t-2, i, m)), W(t-7, i, m)), SSIG0(W(t-15, i, m))), W(t-16, i, m))
}

static function T1(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 2 <= step <= 128;
    requires step % 2 == 0;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(T1(step, i, m));
    decreases i, step;
{
    AddInstruction(AddInstruction(AddInstruction(AddInstruction(h(step-1, i, m), BSIG1(e(step-1, i, m))),
                                                 Ch(e(step-1, i, m), f(step-1, i, m), g(step-1, i, m))),
                                  K(step/2-1)),
                   W(step/2-1, i, m))
}

static function T2(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 2 <= step <= 128;
    requires step % 2 == 0;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(T2(step, i, m));
    decreases i, step;
{
    AddInstruction(BSIG0(a(step-1, i, m)),
                   Maj(a(step-1, i, m), b(step-1, i, m), c(step-1, i, m)))
}

static function {:hidden} a(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 129;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(a(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(0, i-1, m)
    else
        AddInstruction(T1(step-1, i, m), T2(step-1, i, m))
}

static function b(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 129;
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
    requires 1 <= step <= 129;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(c(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(2, i-1, m)
    else
        b(step-2, i, m)
}

static function d(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 129;
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
    requires 1 <= step <= 129;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(e(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(4, i-1, m)
    else
        AddInstruction(d(step-2, i, m), T1(step-1, i, m))
}

static function f(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 129;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(f(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(5, i-1, m)
    else
        e(step-2, i, m)
}

static function g(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 129;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(g(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(6, i-1, m)
    else
        f(step-2, i, m)
}

static function h(step: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 1 <= step <= 129;
    requires step % 2 == 1;
    requires 1 <= i <= NumBlocks(m);
    ensures Word32(h(step, i, m));
    decreases i, step;
{
    if step == 1 then
        H(7, i-1, m)
    else
        g(step-2, i, m)
}

static function {:hidden} H(subscript: int, i: int, m: seq<bool>) : int
    requires |m| < power2(64);
    requires 0 <= subscript <= 7;
    requires 0 <= i <= NumBlocks(m); // Note that i can be 0
    ensures Word32(H(subscript, i, m));
    decreases i;
{
    if i == 0 then
        InitialHValue(subscript)
    else if subscript == 0 then
        AddInstruction(a(129, i, m), H(subscript, i-1, m))
    else if subscript == 1 then
        AddInstruction(b(129, i, m), H(subscript, i-1, m))
    else if subscript == 2 then
        AddInstruction(c(129, i, m), H(subscript, i-1, m))
    else if subscript == 3 then
        AddInstruction(d(129, i, m), H(subscript, i-1, m))
    else if subscript == 4 then
        AddInstruction(e(129, i, m), H(subscript, i-1, m))
    else if subscript == 5 then
        AddInstruction(f(129, i, m), H(subscript, i-1, m))
    else if subscript == 6 then
        AddInstruction(g(129, i, m), H(subscript, i-1, m))
    else
        AddInstruction(h(129, i, m), H(subscript, i-1, m))
}

/////////////////////////////////////////////////////
// Final SHA-256 calculation
/////////////////////////////////////////////////////

static function {:hidden} SHA256(m: seq<bool>) : seq<int> // returns a sequence of 32-bit values
    requires |m| < power2(64);
    ensures |SHA256(m)| == 8;
    ensures forall i :: 0 <= i < |SHA256(m)| ==> Word32(SHA256(m)[i]);
{
    SHA256_is_words(m);
    [H(0, NumBlocks(m), m), H(1, NumBlocks(m), m), H(2, NumBlocks(m), m), H(3, NumBlocks(m), m),
     H(4, NumBlocks(m), m), H(5, NumBlocks(m), m), H(6, NumBlocks(m), m), H(7, NumBlocks(m), m)]
}

static lemma {:timeLimit 60} SHA256_is_words(m: seq<bool>)
    requires |m| < power2(64);
    ensures var hash := [H(0, NumBlocks(m), m), H(1, NumBlocks(m), m), H(2, NumBlocks(m), m), H(3, NumBlocks(m), m),
                        H(4, NumBlocks(m), m), H(5, NumBlocks(m), m), H(6, NumBlocks(m), m), H(7, NumBlocks(m), m)];
            forall i :: 0 <= i < |hash| ==> Word32(hash[i]);
{
    ghost var hash := [H(0, NumBlocks(m), m), H(1, NumBlocks(m), m), H(2, NumBlocks(m), m), H(3, NumBlocks(m), m),
                       H(4, NumBlocks(m), m), H(5, NumBlocks(m), m), H(6, NumBlocks(m), m), H(7, NumBlocks(m), m)];
    assert forall subscript :: 0 <= subscript <= 7 ==> Word32(H(subscript, NumBlocks(m), m));
    forall i | 0 <= i < |hash| {
        calc ==> {
            true;
            hash[i] == H(i, NumBlocks(m), m);
            Word32(hash[i]);
        }
    }
}

static function HMAC(k: seq<bool>, m: seq<bool>) : seq<int>
    requires |k| == 512;
    requires |m| < power2(64) - 8*64;
{
    reveal_power2();    
    SHA256( SeqXor(k, Opad(|k|)) + WordSeqToBits(SHA256(SeqXor(k, Ipad(|k|)) + m)) ) 
}
