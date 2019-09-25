include "../../../Assembly.dfy"
include "../../Util/arrays_and_seqs.dfy"

/////////////////////////////////////////////////////
// Ch, Maj, BSIG0, BSIG1, SSIG0, SSIG1
/////////////////////////////////////////////////////

static function method Ch(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Ch(x, y, z));
{
    BitwiseXorInstruction(BitwiseAndInstruction(x, y), BitwiseAndInstruction(BitwiseNotInstruction(x), z))
}

static function method Maj(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Maj(x, y, z));
{
    BitwiseXorInstruction(BitwiseXorInstruction(BitwiseAndInstruction(x, y), BitwiseAndInstruction(x, z)), BitwiseAndInstruction(y, z))
}

static function method Parity(x: int, y: int, z: int) : int
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(Parity(x, y, z));
{
    BitwiseXorInstruction(BitwiseXorInstruction(x, y), z)
}

static function method ft(t: int, x: int, y: int, z: int) : int
    requires 0 <= t <= 79;
    requires Word32(x);
    requires Word32(y);
    requires Word32(z);
    ensures Word32(ft(t, x, y, z));
{
    if 0 <= t <= 19 then
        Ch(x, y, z)
    else if 40 <= t <= 59 then
        Maj(x, y, z)
    else
        Parity(x, y, z)
}

static function method BSIG0(x: int) : int
    requires Word32(x);
    ensures Word32(BSIG0(x));
{
    BitwiseXorInstruction(BitwiseXorInstruction(RotateRightInstruction(x, 2), RotateRightInstruction(x, 13)), RotateRightInstruction(x, 22))
}

static function method BSIG1(x: int) : int
    requires Word32(x);
    ensures Word32(BSIG1(x));
{
    BitwiseXorInstruction(BitwiseXorInstruction(RotateRightInstruction(x, 6), RotateRightInstruction(x, 11)), RotateRightInstruction(x, 25))
}

static function method SSIG0(x: int) : int
    requires Word32(x);
    ensures Word32(SSIG0(x));
{
    BitwiseXorInstruction(BitwiseXorInstruction(RotateRightInstruction(x, 7), RotateRightInstruction(x, 18)), RightShiftInstruction(x, 3))
}

static function method SSIG1(x: int) : int
    requires Word32(x);
    ensures Word32(SSIG1(x));
{
    BitwiseXorInstruction(BitwiseXorInstruction(RotateRightInstruction(x, 17), RotateRightInstruction(x, 19)), RightShiftInstruction(x, 10))
}

/////////////////////////////////////////////////////
// Padding
/////////////////////////////////////////////////////

static function method {:timeLimit 20} {:hidden} NumPaddingZeroes(message_len: int) : int
    // According to the spec, this is the smallest non-negative k such that message_len + 1 + k = 448 (mod 512)
//    ensures (message_len + 1 + NumPaddingZeroes(message_len)) % 512 == 448;
    // no good triggers: ensures forall k :: 0 <= k < NumPaddingZeroes(message_len) ==> (message_len + 1 + k) % 512 != 448;
//    ensures NumPaddingZeroes(message_len) <= (448 - message_len - 1) % 512;
    ensures 0 <= NumPaddingZeroes(message_len) < 512;
//    ensures (message_len + NumPaddingZeroes(message_len) + 1) % 32 == 0;
{
    (959 - (message_len % 512)) % 512
}

static function method {:hidden} PaddedLength(message_len: int) : int
    ensures message_len + 1 + 64 <= PaddedLength(message_len) < message_len + 1 + 64 + 512;
//    ensures PaddedLength(message_len) % 512 == 0;
{
    message_len + 1 + NumPaddingZeroes(message_len) + 64
}

static function Pad(m: seq<bool>) : seq<bool>
    requires |m| < power2(64);
//    ensures |Pad(m)| % 512 == 0;
    ensures |Pad(m)| == PaddedLength(|m|) == |m| + NumPaddingZeroes(|m|) + 65;
    ensures forall i {:trigger Pad(m)[i]} :: 0 <= i < |m| ==> Pad(m)[i] == m[i];
    ensures Pad(m)[|m|] == true;
    ensures forall i {:trigger Pad(m)[i]} :: |m| + 1 <= i <= |m| + NumPaddingZeroes(|m|) ==> Pad(m)[i] == false;
    ensures Pad(m)[|m|+NumPaddingZeroes(|m|)+1..|m|+NumPaddingZeroes(|m|)+65] == IntToSeq(|m|, 64);
{
    calc
    {
        true;
        { reveal_NumPaddingZeroes(); }
        { reveal_PaddedLength(); }
        PaddedLength(|m|) == |m| + 1 + NumPaddingZeroes(|m|) + 64;
    }
    m + [true] + SequenceOfFalses(NumPaddingZeroes(|m|)) + IntToSeq(|m|, 64)
}

/////////////////////////////////////////////////////
// Dividing messages into blocks and words
/////////////////////////////////////////////////////

static function NumBlocks(m: seq<bool>) : int
    ensures NumBlocks(m) * 512 == PaddedLength(|m|);
{
    reveal_NumPaddingZeroes();
    reveal_PaddedLength();
    PaddedLength(|m|) / 512
}

static function PaddedMessageWord(word_index: int, block_index: int, m: seq<bool>) : int
    requires 1 <= block_index <= |m|/512;
    requires 0 <= word_index <= 15;
    ensures Word32(PaddedMessageWord(word_index, block_index, m));
{
    SeqToInt(m[(block_index-1) * 512 + word_index * 32 .. (block_index-1) * 512 + (word_index+1) * 32])
}

/////////////////////////////////////////////////////////////////////////////////
// HMAC specification based on:
// http://csrc.nist.gov/publications/fips/fips198-1/FIPS-198-1_final.pdf
/////////////////////////////////////////////////////////////////////////////////

static function {:hidden} SeqXor(a: seq<bool>, b: seq<bool>) : seq<bool>
    requires |a| == |b|;
    ensures |SeqXor(a, b)| == |a|;
    ensures forall i {:trigger a[i]}{:trigger b[i]}{:trigger SeqXor(a, b)[i]} :: 0 <= i < |a| ==> SeqXor(a, b)[i] == (a[i] != b[i]);
{
    if |a| == 0 then
        []
    else
        [a[0] != b[0]] + SeqXor(a[1..], b[1..])
}

static function Opad(len:int) : seq<bool>
    requires len % 32 == 0;
    ensures len >= 0 ==> |Opad(len)| == len;
{
    lemma_power2_32();
    ConstPad(len, 0x5c5c5c5c)
}


static function Ipad(len:int) : seq<bool>
    requires len % 32 == 0;
    ensures len >= 0 ==> |Ipad(len)| == len;
{
    lemma_power2_32();
    ConstPad(len, 0x36363636)
}

static function {:hidden} ConstPad(len:int, const:int) : seq<bool>
    requires len % 32 == 0;
    requires Word32(const);
    ensures len >= 0 ==> |ConstPad(len, const)| == len;
{
    if len <= 0 then
        []
    else
        WordToSeq(const) + ConstPad(len - 32, const)
}
