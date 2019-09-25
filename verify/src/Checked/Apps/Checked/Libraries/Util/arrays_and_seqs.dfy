include "..\..\..\Trusted\Spec\Libraries\Util\arrays_and_seqs.dfy"
//include "..\..\Libraries\Math\mul.dfy"
include "..\..\Libraries\Math\div.dfy"
include "..\..\Libraries\Math\power2.dfy"
include "..\..\..\Trusted\Spec\Assembly.dfy"

//////////////////////////////////////////////////////////////////////////////
// Sequence types
//////////////////////////////////////////////////////////////////////////////



//////////////////////////////////////////////////////////////////////////////

// prior methods


////////////////////////////
// Conversion Routines   //
//////////////////////////

static method copy_seq_to_array(s:seq<int>, a:array<int>, a_offset:int) 
	requires a != null;
	requires 0 <= a_offset < a.Length;
	requires 0 <= a_offset + |s| <= a.Length;
	requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> word(a[i]);
	requires is_word_seq(s);
	modifies a;
	ensures forall i {:trigger a[i]} :: 0 <= i < a.Length ==> word(a[i]);
	//ensures forall i :: 0 <= i < |s| ==> word(a[a_offset + i]);
	//ensures forall j :: 0 <= j < a_offset || a_offset + |s| <= j < a.Length ==> a[j] == old(a[j]);
{
	var i := 0;
	while (i < |s|) 
		invariant 0 <= i <= |s|;
		invariant 0 <= a_offset + i <= a.Length;
		//invariant forall j :: 0 <= j < i ==> word(a[a_offset + j]);
		//invariant forall j :: 0 <= j < a_offset || a_offset + |s| <= j < a.Length ==> a[j] == old(a[j]);
		invariant forall j {:trigger a[j]} :: 0 <= j < a.Length ==> word(a[j]);
	{
		a[a_offset + i] := s[i];
		i := i + 1;
	}
}

// TODO: We're being inconsistent with endianness!  
// This takes a little-endian byte sequence, but word_seq_to_byte_seq creates a big-endian byte sequence!
static method byte_seq_to_word_seq(bs:seq<int>) returns (is:seq<int>)
	requires is_byte_seq(bs);
	ensures forall i {:trigger is[i]} :: 0 <= i < |is| ==> word(is[i]);
	ensures if |bs| % 4 == 0 then |is| == |bs| / 4 else |is| == |bs| / 4 + 1;
{
	is := [];
	var padded_bs := bs;

	if (|bs| % 4 == 1) {
		padded_bs := bs + [ 0, 0, 0 ];
		assert |padded_bs| % 4 == 0;
	} else if (|bs| % 4 == 2) {
		padded_bs := bs + [ 0, 0 ];
		assert |padded_bs| % 4 == 0;
	} else if (|bs| % 4 == 3) {
		padded_bs := bs + [ 0 ];
		assert |padded_bs| % 4 == 0;
	}
	assert |padded_bs| % 4 == 0;

	var i := 0;
	while (i < |padded_bs|) 
		invariant i % 4 == 0;
		invariant 0 <= i <= |padded_bs|;
		invariant i < |padded_bs| ==> i + 3 <= |padded_bs|;
		invariant forall j {:trigger is[j]} :: 0 <= j < |is| ==> word(is[j]);
		invariant |is| == i / 4;
	{
		lemma_2toX();
		is := is + [ padded_bs[i+3] * 16777216 + padded_bs[i+2] * 65536 + padded_bs[i+1] *256 + padded_bs[i+0] ];
		i := i + 4;
	}

	assert |is| == |padded_bs| / 4;
}

static method word_seq_to_byte_seq(is:seq<int>) returns (bs:seq<int>)
	requires word(|is| * 4);
	requires is_word_seq(is);
	ensures |bs| == 4*|is|;
	ensures is_byte_seq(bs);
{
	bs := [];

	var i := 0;
	while (i < |is|) 
		invariant 0 <= i <= |is|;
		invariant |bs| == 4 * i;
		invariant forall j {:trigger is[j]} :: 0 <= j < |is| ==> word(is[j]);
		invariant is_byte_seq(bs);
	{	
		var bytes := word_2_bytes(is[i]);
		bs := bs + bytes;
		i := i + 1;
	}
}

static method word_2_bytes(x:int) returns (bytes:seq<int>)
	requires word(x);
	ensures is_byte_seq(bytes);
	ensures bytes == word_to_bytes(x);
{
	bytes := [ x / 16777216, (x / 65536) % 256, (x / 256) % 256, x % 256 ];
	lemma_div_power2toX();
	lemma_word_to_bytes_is_bytes_generic();
}

// TODO: Fix me! 
/* 
static method bytes_2_word(bytes:seq<int>) returns (x:int)
	requires is_byte_seq(bytes);
	requires 0 <= |bytes| <= 4;
	ensures word_to_bytes(x) == bytes;	// Not quite right, if we're allowing short (<4) byte sequences
{
}
*/

///////////////////////////////////////////////////////////
// Properties of Conversion Routines Defined Elsewhere  //
/////////////////////////////////////////////////////////

static lemma lemma_word_to_bytes_is_bytes_generic()
	ensures forall w :: word(w) ==> is_byte_seq(word_to_bytes(w));
{
  assert unroll(1) && unroll(2) && unroll(3) && unroll(4) && unroll(5) && unroll(6) && unroll(7) && unroll(8) && unroll(9);
	forall w | word(w)
		ensures is_byte_seq(word_to_bytes(w));
	 {
		calc {
			word_to_bytes(w)[0];
			w / power2(24);
			< { lemma_power2_adds(8, 24); lemma_div_by_multiple_is_strongly_ordered(w, power2(32), power2(8), power2(24)); }
			power2(32) / power2(24);
			{ lemma_power2_div_is_sub(24, 32); }
			power2(8);
			{ reveal_power2(); }
			256;
		}
		assert word_to_bytes(w)[0] < 256;
		lemma_div_pos_is_pos(w, power2(24));
		lemma_2toX();		
	}	
}

lemma {:timeLimit 33} lemma_word_to_bytes_unique_specific(a:int, b:int)
	requires word(a) && word(b);
	requires word_to_bytes(a) == word_to_bytes(b);
	ensures a == b;
{
    assert IsByte(word_to_bytes(a)[0]);
    assert IsByte(word_to_bytes(a)[1]);
    assert IsByte(word_to_bytes(a)[2]);
    assert IsByte(word_to_bytes(a)[3]);
    assert IsByte(word_to_bytes(b)[0]);
    assert IsByte(word_to_bytes(b)[1]);
    assert IsByte(word_to_bytes(b)[2]);
    assert IsByte(word_to_bytes(b)[3]);
    lemma_word_to_bytes_unique_specific_power2(a, b);
/*
	assert word_to_bytes(a) == [ a / 16777216, (a/65536) % 256, (a / 256) % 256, a % 256 ];
	assert word_to_bytes(b) == [ b / 16777216, (b/65536) % 256, (b / 256) % 256, b % 256 ];

	calc {
		a;
		(a / 256) * 256 + (a % 256);
		{ assert word_to_bytes(a)[3] == word_to_bytes(b)[3]; }
		(a / 256) * 256 + (b % 256);
		calc {
			a / 256;
			(a / 65536) * 256 + (a/256) % 256;
			{ assert word_to_bytes(a)[2] == word_to_bytes(b)[2]; }
			(a / 65536) * 256 + (b/256) % 256;
		}
		((a / 65536) * 256 + (b/256) % 256) * 256 + (b % 256);
		calc {
			a / 65536;
			(a / 16777216) * 256 + (a / 65536) % 256;
			{ assert word_to_bytes(a)[1] == word_to_bytes(b)[1]; }
			(a / 16777216) * 256 + (b / 65536) % 256;
			{ assert word_to_bytes(a)[0] == word_to_bytes(b)[0]; }
			(b / 16777216) * 256 + (b / 65536) % 256;
		}
		(((b / 16777216) * 256 + (b / 65536) % 256) * 256 + (b/256) % 256) * 256 + (b % 256);
		calc {
			(b / 16777216) * 256 + (b / 65536) % 256;			
			b / 65536;
		}
		((b / 65536) * 256 + (b/256) % 256) * 256 + (b % 256);
        calc {
            (b / 65536) * 256 + (b/256) % 256;
            b / 256;
        }
		(b / 256) * 256 + (b % 256);
		b;
	}
*/
}

static lemma lemma_array_seq_equality(a:array<int>, b:array<int>, a_start:int, a_end:int, b_start:int, b_end:int) 
    requires b_end - b_start == a_end - a_start;
    requires a != null && b != null;
    requires 0 <= a_start < a_end <= a.Length;
    requires 0 <= b_start < b_end <= b.Length;
    requires forall i :: 0 <= i < a_end - a_start ==> a[a_start + i] == b[b_start + i];
    ensures a[a_start..a_end] == b[b_start..b_end];
{
    ghost var A := a[a_start..a_end];
    ghost var B := b[b_start..b_end];

    assert |A| == |B|;
    forall i | 0 <= i < |A| 
        ensures 0 <= i < |A| ==> A[i] == B[i];
    {
        calc {
            A[i];
            a[a_start..a_end][i];
            a[a_start + i];
            { assert forall j :: 0 <= j < a_end - a_start ==> a[a_start + j] == b[b_start + j]; }
            //{ assert 0 <= i < a_end - a_start; }
            b[b_start + i];
            b[b_start..b_end][i];
            B[i];
        }
        assert A[i] == B[i];
        //assert a[a_start..a_end][i] == b[b_start..b_end][i];
    }
    assert A == B;
    assert a[a_start..a_end] == b[b_start..b_end];
}

static lemma Lemma_ZeroToSeqIsFalses(b: int)
    requires 0 <= b;
    ensures IntToSeq(0, b) == SequenceOfFalses(b);
{
    reveal_IntToSeq();
    reveal_SequenceOfFalses();
    if (b > 0)
    {
        Lemma_ZeroToSeqIsFalses(b - 1);
    }
}

static lemma Lemma_OneToSeqIsFalsesAndTrue(b: int)
    requires 0 < b;
    ensures 0 <= 1 < power2(b);
    ensures IntToSeq(1, b) == SequenceOfFalses(b-1) + [true];
{    
    reveal_power2();
    calc {
        IntToSeq(1, b);
        { reveal_IntToSeq(); }
        IntToSeq(0, b - 1) + [true];
        == { Lemma_ZeroToSeqIsFalses(b-1); }
        SequenceOfFalses(b-1) + [true];
    }
}

static lemma lemma_IntSeq_ConvertMessage(a: array<int>, b: int)
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires 0 <= b <= a.Length * 32;
    ensures forall i {:trigger WordSeqToBits(a[..])[i]}{:trigger ArrayToBitSequence(a, b)[i]} :: 0 <= i < b ==> WordSeqToBits(a[..])[i] == ArrayToBitSequence(a, b)[i];
    decreases b;
{
    if b == 0 {
    } else {
        lemma_IntSeq_ConvertMessage(a, b-1);
        assert forall i :: 0 <= i < b-1 ==> WordSeqToBits(a[..])[i] == ArrayToBitSequence(a, b)[i];
        
        calc {
            ArrayToBitSequence(a, b)[b-1];
            IsArrayBitSet(a, b-1);
            { reveal_IsArrayBitSet(); }
            IsWordBitSet(a[(b-1) / 32], (b - 1) % 32);
            WordToSeq(a[(b-1) / 32])[(b - 1) % 32];
            { lemma_IntSeq_Indexing(a[..], b-1); }
            WordSeqToBits(a[..])[b-1];
        }
    }
}

////////////////////////////////////////////
// Properties of Sequence Manipulations  //
//////////////////////////////////////////

static lemma {:timeLimit 20} Lemma_IntToSeqExpansion(x: int, b1: int, b2: int)
    requires 0 <= b1 <= b2;
    requires 0 <= x < power2(b1);
    ensures power2(b1) <= power2(b2);
    ensures IntToSeq(x, b2) == SequenceOfFalses(b2-b1) + IntToSeq(x, b1);
    decreases b2;
{
    reveal_SequenceOfFalses();
    if (b2 <= b1) {
        reveal_IntToSeq();
        reveal_power2();
        lemma_power2_increases(b1, b2);
    } else if (b2 == 0) {
    } else if (b1 == 0) {
        reveal_IntToSeq();
        reveal_power2();
        assert x == 0;
        Lemma_ZeroToSeqIsFalses(b2);
    } else if (b2 == b1 + 1) {
        lemma_power2_increases(b1, b2);
        calc {
            IntToSeq(x, b2);
            IntToSeq(x, b1+1);
            { reveal_IntToSeq(); reveal_power2(); }
            IntToSeq(x / 2, b1) + [x % 2 != 0];
            { reveal_power2(); Lemma_IntToSeqExpansion(x / 2, b1-1, b1); }
            SequenceOfFalses(1) + IntToSeq(x / 2, b1-1) + [x % 2 != 0];
            { reveal_IntToSeq(); reveal_power2(); }
            SequenceOfFalses(b2-b1) + IntToSeq(x, b1);
        }
    } else {
        lemma_power2_increases(b1, b2);
        calc {
            IntToSeq(x, b2);
            { reveal_IntToSeq(); reveal_power2(); }
            IntToSeq(x / 2, b2-1) + [x % 2 != 0];
            { Lemma_IntToSeqExpansion(x / 2, b1, b2 - 1); }
            SequenceOfFalses(b2-b1-1) + IntToSeq(x/2, b1) + [x % 2 != 0];
            { reveal_IntToSeq(); lemma_power2_increases(b1, b1+1); }
            SequenceOfFalses(b2-b1-1) + IntToSeq(x, b1+1);
            { Lemma_IntToSeqExpansion(x, b1, b1+1); lemma_power2_increases(b1, b1+1); }
            SequenceOfFalses(b2-b1-1) + SequenceOfFalses(1) + IntToSeq(x, b1);
        }
    }
}

static lemma {:timeLimit 30} lemma_IntSeq_Split(a: seq<int>, b: seq<int>)    
    requires forall w {:trigger a[w]} :: 0 <= w < |a| ==> Word32(a[w]);
    requires forall w {:trigger b[w]} :: 0 <= w < |b| ==> Word32(b[w]);
    ensures WordSeqToBits(a + b) == WordSeqToBits(a) + WordSeqToBits(b);
{
    if a == [] {
        assert a + b == b;
    } else {
        ghost var tmp := [a[0]] + a[1..] + b;
        calc {            
            WordSeqToBits(a + b);
            { assert a + b == [a[0]] + a[1..] + b; }
            WordSeqToBits([a[0]] + a[1..] + b);
            WordSeqToBits(tmp);
            { reveal_WordSeqToBits(); }
            WordToSeq(tmp[0]) + WordSeqToBits(tmp[1..]);
            { assert tmp[0] == a[0]; assert tmp[1..] == a[1..] + b; }
            WordToSeq(a[0]) + WordSeqToBits(a[1..] + b);
            { lemma_IntSeq_Split(a[1..], b); assert WordSeqToBits(a[1..] + b) == WordSeqToBits(a[1..]) + WordSeqToBits(b); }
            WordToSeq(a[0]) + (WordSeqToBits(a[1..]) + WordSeqToBits(b));
            { reveal_WordSeqToBits(); }
            WordSeqToBits(a) + WordSeqToBits(b);
        }
    }
}

static lemma lemma_IntSeq_Indexing(s: seq<int>, b: int)
    requires forall i {:trigger s[i]} :: 0 <= i < |s| ==> Word32(s[i]);
    requires 0 <= b < |s| * 32;
    ensures WordSeqToBits(s)[b] == WordToSeq(s[b / 32])[b % 32];
{
    if s == [] {
    } else {
        if b < 32 {
            assert b / 32 == 0;
            assert b % 32 == b;
            reveal_WordSeqToBits();
        } else {
            calc {
                WordSeqToBits(s)[b];
                { reveal_WordSeqToBits(); }
                WordSeqToBits(s[1..])[b-32];
                { lemma_IntSeq_Indexing(s[1..], b-32); }
                WordToSeq(s[1..][(b - 32) / 32])[(b - 32) % 32];
                { lemma_mod32(b); }
                WordToSeq(s[1..][b/32 - 1])[b % 32];
                WordToSeq(s[b/32])[b % 32];
            }
        }
    }
}

static lemma lemma_seq_equality(a:seq<bool>, b:seq<bool>, len:int) 
    requires |a| == |b| == len;
    requires forall i {:trigger a[i]}{:trigger b[i]} :: 0 <= i < len ==> a[i] == b[i];
    ensures a == b;
{
    assert forall i :: 0 <= i < len ==> a[i] == b[i];
}

static lemma Lemma_SubsequenceConcatenation (s: seq<bool>, left: int, middle: int, right: int)
    requires 0 <= left <= middle <= right <= |s|;
    ensures s[left..right] == s[left..middle] + s[middle..right];
{
}

static lemma lemma_seq_split(s:seq<int>)
    ensures forall i :: 0 <= i < |s| ==> s == s[..i] + s[i..];
{}

lemma lemma_byte_seq_sub_seq(bytes:seq<int>, subseq:seq<int>, a:int, b:int) 
	requires is_byte_seq(bytes);
	requires 0 <= a < b <= |bytes|;
	requires subseq == bytes[a..b];
	ensures  is_byte_seq(subseq);
{
}


///////////////////////
// Updating arrays  //
/////////////////////

static method UpdateBitOfWord(x: int, pos: int, value: bool) returns (y: int)
    requires Word32(x);
    requires 0 <= pos < 32;
    ensures Word32(y);
    ensures IsWordBitSet(y, pos) == value;
    ensures forall i {:trigger IsWordBitSet(x, i)}{:trigger IsWordBitSet(y, i)} :: 0 <= i < 32 && i != pos ==> IsWordBitSet(y, i) == IsWordBitSet(x, i);
{
    Lemma_ComputePower2Properties(31 - pos);

    if value
    {
        assert forall i :: 0 <= i < 32 ==> IsWordBitSet(BitwiseOrInstruction(x, ComputePower2(31-pos)), i) ==
                                           (IsWordBitSet(x, i) || IsWordBitSet(ComputePower2(31-pos), i));
        return BitwiseOrInstruction(x, ComputePower2(31-pos));
    }
    else
    {
        assert forall i :: 0 <= i < 32 ==> IsWordBitSet(BitwiseAndInstruction(x, BitwiseNotInstruction(ComputePower2(31-pos))), i) ==
                                           (IsWordBitSet(x, i) && !IsWordBitSet(ComputePower2(31-pos), i));
        return BitwiseAndInstruction(x, BitwiseNotInstruction(ComputePower2(31-pos)));
    }
}

static method UpdateBitOfArray(a: array<int>, pos: int, value: bool)
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires 0 <= pos < a.Length * 32;
    ensures forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    ensures IsArrayBitSet(a, pos) == value;
    ensures forall i {:trigger IsArrayBitSet(a, i)}{:trigger old(IsArrayBitSet(a, i))} :: 0 <= i < a.Length * 32 && i != pos ==> IsArrayBitSet(a, i) == old(IsArrayBitSet(a, i));
    modifies a;
{
    reveal_IsArrayBitSet();
// TODO:    a[pos / 32] := UpdateBitOfWord(a[pos / 32], pos % 32, value);
    var tmp := UpdateBitOfWord(a[pos / 32], pos % 32, value);
    a[pos / 32] := tmp;
    reveal_IsArrayBitSet();
}

static method AppendBitToMessageArray(a: array<int>, b: int, value: bool)
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires 0 <= b;
    requires b + 1 <= a.Length * 32;
    ensures forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    ensures forall i {:trigger IsArrayBitSet(a, i)}{:trigger old(IsArrayBitSet(a, i))} :: 0 <= i < b ==> IsArrayBitSet(a, i) == old(IsArrayBitSet(a, i));
    ensures IsArrayBitSet(a, b) == value;
    modifies a;
{
    UpdateBitOfArray(a, b, value);
}

static method AppendBitsToMessageArray(a: array<int>, b: int, value: bool, num_values: int)
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires 0 <= b;
    requires 0 <= num_values;
    requires b + num_values <= a.Length * 32;
    ensures forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    ensures forall i {:trigger IsArrayBitSet(a, i)}{:trigger old(IsArrayBitSet(a, i))} :: 0 <= i < b ==> IsArrayBitSet(a, i) == old(IsArrayBitSet(a, i));
    ensures forall i {:trigger IsArrayBitSet(a, i)} :: b <= i < b + num_values ==> IsArrayBitSet(a, i) == value;
    modifies a;
{
    var j := 0;
    while (j < num_values)
        invariant 0 <= b <= b + j <= b + num_values <= a.Length * 32;
        invariant forall i :: 0 <= i < a.Length ==> Word32(a[i]);
        invariant forall i :: 0 <= i < b ==> IsArrayBitSet(a, i) == old(IsArrayBitSet(a, i));
        invariant forall i :: b <= i < b + j ==> IsArrayBitSet(a, i) == value;
    {
        if (!value && (b + j) % 32 == 0 && j + 32 <= num_values) {
            Lemma_ZeroToSeqIsFalses(32);
            lemma_2toX();
            AppendWordToMessageArray(a, b + j, 0);
            j := j + 32;
        }
        else {
            AppendBitToMessageArray(a, b + j, value);
            j := j + 1;
        }
        reveal_IsArrayBitSet();
    }
}

static method AppendWordToMessageArray(a: array<int>, b: int, value: int)
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires 0 <= b;
    requires b % 32 == 0;
    requires b + 32 <= a.Length * 32;
    requires Word32(value);
    ensures forall i {:trigger a[i]}:: 0 <= i < a.Length ==> Word32(a[i]);
    ensures forall i {:trigger IsArrayBitSet(a, i)}{:trigger old(IsArrayBitSet(a, i))} :: 0 <= i < b ==> IsArrayBitSet(a, i) == old(IsArrayBitSet(a, i));
    ensures forall i {:trigger a[i]}:: 0 <= i * 32 < b ==> a[i] == old(a[i]);
    ensures a[b / 32] == value;
    modifies a;
{
    reveal_IsArrayBitSet();
    a[b / 32] := value;
    reveal_IsArrayBitSet();
}

/////////////////////////////////////////////////////
// Properties of Power2 Relevant to Sequences     //
///////////////////////////////////////////////////

static function method ComputePower2(e: int) : int
    requires 0 <= e < 32;
    ensures Word32(ComputePower2(e));
{
    lemma_2toX();
    LeftShiftInstruction(1, e)
}

static method Lemma_ComputePower2Properties(e: int)
    requires 0 <= e < 32;
    ensures IsWordBitSet(ComputePower2(e), 31 - e);
    ensures forall i {:trigger IsWordBitSet(ComputePower2(e), i)} :: 0 <= i < 32 && i != 31 - e ==> !IsWordBitSet(ComputePower2(e), i);
{
    Lemma_OneToSeqIsFalsesAndTrue(32);
    lemma_2toX();
    assert WordToSeq(1) == SequenceOfFalses(31) + [true];
    assert forall i :: 0 <= i < 32 - e ==> WordToSeq(ComputePower2(e))[i] == WordToSeq(1)[i+e];
    assert forall i :: 32 - e <= i < 32 ==> WordToSeq(ComputePower2(e))[i] == false;
    assert forall i :: 32 - e <= i < 32 ==> !IsWordBitSet(ComputePower2(e), i);
}

