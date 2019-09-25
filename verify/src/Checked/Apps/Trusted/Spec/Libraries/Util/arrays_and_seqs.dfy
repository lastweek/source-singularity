include "..\Math\power2.dfy"
include "bytes_and_words.dfy"

//////////////////////////////////////////////////////////////////////////////
// Sequence types
//////////////////////////////////////////////////////////////////////////////

static predicate IsBitSeq(bs:seq<int>)
{
	forall i {:trigger bs[i]} :: 0<=i<|bs| ==> IsBit(bs[i])
}

static predicate IsByteSeq(os:seq<int>)
{
	forall i {:trigger os[i]} :: 0<=i<|os| ==> IsByte(os[i])
}

static predicate IsWordSeq(ws:seq<int>)
{
	forall i {:trigger ws[i]} :: 0<=i<|ws| ==> IsWord(ws[i])
}

//////////////////////////////////////////////////////////////////////////////
// Relationships among sequences of different digit sizes
// (bit, byte, word, and ghost int)
//////////////////////////////////////////////////////////////////////////////

// BE/LE refers to the endianness of the transformation. There's no
// inherent endianness in a sequence until it's interpreted.
// I'll add LE variants if we actually need them in spec-land.

static predicate IsDigitSeq(place_value:int, digits:seq<int>)
{
	forall i {:trigger digits[i]} :: 0<=i<|digits| ==> 0 <= digits[i] < place_value
}

static function {:hidden} BEDigitSeq_IntValue(place_value:int, digits:seq<int>) : int
	decreases |digits|;
{
	if (digits==[]) then
		0
	else
		BEDigitSeq_IntValue(place_value, digits[0..|digits|-1])*place_value + digits[|digits|-1]
}

static predicate BEDigitSeqEqInt(place_value:int, digits:seq<int>, v:int)
{
	IsDigitSeq(place_value, digits)
	&& BEDigitSeq_IntValue(place_value, digits)==v
}

static predicate BEBitSeqEqInt(bitseq:seq<int>, v:int)
{
	BEDigitSeqEqInt(2, bitseq, v)
}

static predicate BEBitSeqEqByte(bitseq:seq<int>, byte:int)
{
	IsByte(byte) && BEBitSeqEqInt(bitseq, byte)
}

static predicate BEBitSeqEqWord(bitseq:seq<int>, word:int)
{
	IsWord(word) && BEBitSeqEqInt(bitseq, word)
}

static predicate BEByteSeqEqInt(byteseq:seq<int>, v:int)
{
	BEDigitSeqEqInt(256, byteseq, v)
}

static predicate BEByteSeqEqWord(byteseq:seq<int>, word:int)
{
	IsWord(word) && BEByteSeqEqInt(byteseq, word)
}

static predicate BEWordSeqEqInt(byteseq:seq<int>, v:int)
{
	BEDigitSeqEqInt(power2(32), byteseq, v)
}

static predicate BEBitSeqEqByteSeq(bitseq:seq<int>, byteseq:seq<int>)
{
	exists v:int ::
		BEBitSeqEqInt(bitseq, v) && BEByteSeqEqInt(byteseq, v)
}

static predicate BEBitSeqEqWordSeq(bitseq:seq<int>, wordseq:seq<int>)
{
	exists v:int ::
		BEBitSeqEqInt(bitseq, v) && BEWordSeqEqInt(wordseq, v)
}

//////////////////////////////////////////////////////////////////////////////
// Transformation to sequences of bools, which SHA256 uses
//////////////////////////////////////////////////////////////////////////////

static predicate BoolSeqEqBitSeq(boolseq:seq<bool>, bitseq:seq<int>)
{
	|boolseq| == |bitseq|
	&& IsDigitSeq(2, bitseq)
	&& forall i {:trigger boolseq[i]}{:trigger bitseq[i]} :: 0<=i<|boolseq| ==> boolseq[i] == (bitseq[i]==1)
}

//////////////////////////////////////////////////////////////////////////////
//
// TODO deprecate and delete old terminology
//

// Shims here to make old functions work

static predicate ByteSeq(os:seq<int>) { IsByteSeq(os) }
static predicate WordSeq(ws:seq<int>) { IsWordSeq(ws) }

// stuff that used to be in Assembly.dfy

/////////////////////////////////////////////////////
// Conversion between integers and bit sequences
/////////////////////////////////////////////////////

static function {:hidden} SeqToInt(s: seq<bool>) : int
    ensures 0 <= SeqToInt(s) < power2(|s|);
{
    reveal_power2();
    if (|s| == 0) then
        0
    else
        SeqToInt(s[..|s|-1]) * 2 + if s[|s|-1] then 1 else 0
}

static function {:hidden} IntToSeq(x: int, b: int) : seq<bool>
    decreases b;
    requires 0 <= b;
    requires 0 <= x < power2(b);
    ensures SeqToInt(IntToSeq(x, b)) == x;
    ensures |IntToSeq(x, b)| == b;
{
    reveal_power2();
    reveal_SeqToInt();
    if b == 0 then
        []
    else
        IntToSeq(x / 2, b-1) + [x % 2 != 0]
}

static function WordToSeq(x: int) : seq<bool>
    requires Word32(x);
    ensures |WordToSeq(x)| == 32;
    ensures SeqToInt(WordToSeq(x)) == x;
{
    IntToSeq(x, 32)
}


static function word(x:int) : bool
{
        0 <= x < power2(32)
}

static function byte(x : int) : bool
{
    0 <= x < 256
}

static function byte_seq(a:seq<int>, len:int) : bool
{
	word(len) && len == |a| && forall i {:trigger a[i]} :: 0 <= i < |a| ==> byte(a[i])
}

static function is_byte_seq(s:seq<int>) : bool
{
	byte_seq(s, |s|)
}

static function word_seq(s:seq<int>, len:int) : bool
{
	word(len) && |s| == len && forall i {:trigger s[i]} :: 0 <= i < |s| ==> word(s[i])
}

static function is_word_seq(s:seq<int>) : bool
{
	word_seq(s, |s|)
}

static lemma{:axiom} axiom_word_to_bytes_assume(i:int)
	requires word(i);
	ensures ByteSeq([ i / power2(24), (i / power2(16)) % 256, (i / power2(8)) % 256, i % 256 ]);

// NB output sequence is big endian
static function word_to_bytes(i:int) : seq<int>
	requires word(i);
	ensures |word_to_bytes(i)| == 4;
	ensures ByteSeq(word_to_bytes(i));
	/*
	ensures  var r := int_to_bytes(i); 
			 |r| == 4 &&
			 (forall x :: 0 <= x < |r| ==> byte(r[x])) &&
			 r[0] * power2(24) + r[1] * power2(16) + r[2] * power2(8) + r[3] == i;
	*/
{
	// TODO This assume should go away once we understand how to handle
	// ensures obligations in spec.
  axiom_word_to_bytes_assume(i);
	[ i / power2(24), (i / power2(16)) % 256, (i / power2(8)) % 256, i % 256 ]
//	lemma_2toX();
//	assert i / 16777216 < 256;
//	[ i / 16777216, (i / 65536) % 256, (i / 256) % 256, i % 256 ]
}

// NB words are interpreted as big-endian.
static function {:hidden} WordSeqToByteSeq(ws:seq<int>) : seq<int>
	decreases |ws|;
	requires WordSeq(ws);
	ensures ByteSeq(WordSeqToByteSeq(ws));
	ensures |WordSeqToByteSeq(ws)| == 4*|ws|;
{
	if (ws==[]) then
		[]
	else
		word_to_bytes(ws[0]) + WordSeqToByteSeq(ws[1..])
}

static function ByteSeqToWordSeq(bs:seq<int>) : seq<int>
	requires ByteSeq(bs);
	ensures WordSeq(ByteSeqToWordSeq(bs));
	ensures WordSeqToByteSeq(ByteSeqToWordSeq(bs)) == bs;

static function {:hidden} WordSeqToBits(ints:seq<int>) : seq<bool>
    requires forall i {:trigger ints[i]} :: 0 <= i < |ints| ==> word(ints[i]);
    ensures |WordSeqToBits(ints)| == 32 * |ints|;
{
    if |ints| == 0 then
        []
    else
        WordToSeq(ints[0]) + WordSeqToBits(ints[1..])
}

static function IsWordBitSet(x: int, b: int) : bool
    // Indicates whether bit b of 32-bit word x is set, counting from the LEFT side.
    requires word(x);
    requires 0 <= b < 32;
{
    WordToSeq(x)[b]
}

static function {:hidden} IsArrayBitSet(a: array<int>, b:int) : bool
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> word(a[i]);
    requires 0 <= b < a.Length * 32;
    reads a;
{
    IsWordBitSet(a[b / 32], b % 32)
}

static function {:hidden} ArrayToBitSequence(a: array<int>, b: int) : seq<bool>
    // This static function produces a sequence consisting of the first b bits of the array of words a.
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> word(a[i]);
    requires 0 <= b <= a.Length * 32;
    ensures |ArrayToBitSequence(a, b)| == b;
    ensures forall i {:trigger ArrayToBitSequence(a, b)[i]}{:trigger IsArrayBitSet(a, i)} :: 0 <= i < b ==> ArrayToBitSequence(a, b)[i] == IsArrayBitSet(a, i);
    decreases b;
    reads a;
{
    if b == 0 then
        []
    else
        ArrayToBitSequence(a, b-1) + [IsArrayBitSet(a, b-1)]
}

static function {:hidden} SequenceOfFalses(count: int) : seq<bool>
    requires 0 <= count;
    ensures |SequenceOfFalses(count)| == count;
    ensures forall i {:trigger SequenceOfFalses(count)[i]} :: 0 <= i < count ==> SequenceOfFalses(count)[i] == false;
{
    if count == 0 then [] else SequenceOfFalses(count-1) + [false]
}

static function {:hidden} ByteToBoolSeqInner(bits:nat, os:int) : seq<bool>
	decreases bits;
	requires IsByte(os);
	ensures |ByteToBoolSeqInner(bits,os)|==bits;
{
	if (bits==0) then
		[]
	else
		ByteToBoolSeqInner(bits-1,os/2) + [if os%2==1 then true else false]
}

static function ByteToBoolSeq(os:int) : seq<bool>
	requires IsByte(os);
	ensures |ByteToBoolSeq(os)|==8;
{
	ByteToBoolSeqInner(8,os)
}

static function {:hidden} ByteSeqToBoolSeq(os:seq<int>) : seq<bool>
	requires ByteSeq(os);
	ensures |ByteSeqToBoolSeq(os)| == 8*|os|;
{
	if (os==[]) then
		[]
	else
		ByteToBoolSeq(os[0]) + ByteSeqToBoolSeq(os[1..])
}

static function BoolSeqToByteSeq(bs:seq<bool>) : seq<int>
	ensures ByteSeq(BoolSeqToByteSeq(bs));
	ensures ByteSeqToBoolSeq(BoolSeqToByteSeq(bs)) == bs;

