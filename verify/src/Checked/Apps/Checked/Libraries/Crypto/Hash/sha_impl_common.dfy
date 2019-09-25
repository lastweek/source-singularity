include "..\..\..\..\Trusted\Spec\Libraries\Crypto\Hash\sha_common.dfy"
include "..\..\Util\arrays_and_seqs.dfy"


/////////////////////////////////////////////////////
// Padding message
/////////////////////////////////////////////////////

static function {:hidden} Mod32(i:int):int { i % 32 }

static lemma Lemma_ArrayIsPaddedMessageHelper1(n1:int, n2:int, a:array<int>, b:int, s:seq<bool>)
    requires Mod32(n1) == 0;
    requires n1 + 32 == n2;
    requires 0 <= n1 < n2 <= |s|;
    requires a != null;
    requires n2 <= a.Length * 32;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires forall i :: n1 <= i < n2 ==> s[i] == IsArrayBitSet(a, i);
    requires a[n1 / 32] == b;
    ensures forall i :: n1 <= i < n2 ==> s[i] == WordToSeq(b)[i - n1];
    ensures |s[n1..n2]| == 32;
{
    reveal_Mod32();
    reveal_IsArrayBitSet();
}

static lemma Lemma_ArrayIsPaddedMessageHelper2(m:seq<bool>)
    ensures |m| + NumPaddingZeroes(|m|) + 65 <= PaddedLength(|m|);
    ensures Mod32(|m| + NumPaddingZeroes(|m|) + 1) == 0;
    ensures Mod32(|m| + NumPaddingZeroes(|m|) + 33) == 0;
{
    reveal_Mod32();
    reveal_NumPaddingZeroes();
    reveal_PaddedLength();
}

ghost static method  {:timeLimit 60} Lemma_ArrayIsPaddedMessage(a: array<int>, b: int, m: seq<bool>)
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires |m| == b;
    requires Word32(b);
    requires 0 <= b < power2(64);
    requires 0 <= b <= PaddedLength(b) <= a.Length * 32;
    requires forall i {:trigger IsArrayBitSet(a, i)}{:trigger m[i]} :: 0 <= i < b ==> IsArrayBitSet(a, i) == m[i];
    requires IsArrayBitSet(a, b);
    requires a.Length > (b + NumPaddingZeroes(b) + 33) / 32;
    requires forall i {:trigger IsArrayBitSet(a, i)} :: b + 1 <= i <= b + NumPaddingZeroes(b) ==> !IsArrayBitSet(a, i);
    requires a[(b + NumPaddingZeroes(b) + 1) / 32] == 0;
    requires a[(b + NumPaddingZeroes(b) + 33) / 32] == b;
    ensures ArrayToBitSequence(a, PaddedLength(b)) == Pad(m);
{
    ghost var s := ArrayToBitSequence(a, PaddedLength(b));

    calc {
        s;
        ==
        { reveal_NumPaddingZeroes(); }
        { reveal_PaddedLength(); }
        { Lemma_ArrayIsPaddedMessageHelper2(m); }
        { assert |s| == |m|+NumPaddingZeroes(|m|)+65; }
        s[0..|m|+NumPaddingZeroes(|m|)+65];
        ==
        { Lemma_ArrayIsPaddedMessageHelper2(m); }
        { Lemma_SubsequenceConcatenation(s, 0, |m|+NumPaddingZeroes(|m|)+33, |m|+NumPaddingZeroes(|m|)+65); }
        s[0..|m|+NumPaddingZeroes(|m|)+33] + s[|m|+NumPaddingZeroes(|m|)+33..|m|+NumPaddingZeroes(|m|)+65];
        ==
        { Lemma_ArrayIsPaddedMessageHelper2(m); }
        { Lemma_ArrayIsPaddedMessageHelper1(b+NumPaddingZeroes(b)+33, b+NumPaddingZeroes(b)+65, a, b, s); }
        s[0..|m|+NumPaddingZeroes(|m|)+33] + WordToSeq(b);
        == { Lemma_SubsequenceConcatenation(s, 0, |m|+NumPaddingZeroes(|m|)+1, |m|+NumPaddingZeroes(|m|)+33); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + s[|m|+NumPaddingZeroes(|m|)+1..|m|+NumPaddingZeroes(|m|)+33] + WordToSeq(b);
        ==
        { Lemma_ArrayIsPaddedMessageHelper2(m); }
        { Lemma_ArrayIsPaddedMessageHelper1(b+NumPaddingZeroes(b)+1, b+NumPaddingZeroes(b)+33, a, 0, s); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + WordToSeq(0) + WordToSeq(b);
        == { lemma_2toX(); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + IntToSeq(0, 32) + IntToSeq(b, 32);
        == { Lemma_ZeroToSeqIsFalses(32); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + SequenceOfFalses(32) + IntToSeq(b, 32);
        == { Lemma_IntToSeqExpansion(b, 32, 64); }
        s[0..|m|+NumPaddingZeroes(|m|)+1] + IntToSeq(b, 64);
        == { Lemma_SubsequenceConcatenation(s, 0, |m|+1, |m|+NumPaddingZeroes(|m|)+1); }
        s[0..|m|+1] + s[|m|+1..|m|+NumPaddingZeroes(|m|)+1] + IntToSeq(b, 64);
        ==
        { assert forall i :: |m| + 1 <= i <= |m| + NumPaddingZeroes(b) ==> s[i] == SequenceOfFalses(NumPaddingZeroes(|m|))[i - (|m| + 1)]; }
        s[0..|m|+1] + SequenceOfFalses(NumPaddingZeroes(|m|)) + IntToSeq(b, 64);
        == { Lemma_SubsequenceConcatenation(s, 0, |m|, |m|+1); }
        s[0..|m|] + s[|m|..|m|+1] + SequenceOfFalses(NumPaddingZeroes(|m|)) + IntToSeq(b, 64);
        == { assert s[|m|] == true; assert s[|m|..|m|+1] == [true]; }
        s[0..|m|] + [true] + SequenceOfFalses(NumPaddingZeroes(|m|)) + IntToSeq(b, 64);
        == { assert forall i {:trigger IsArrayBitSet(a, i)}{:trigger m[i]} :: 0 <= i < b ==> IsArrayBitSet(a, i) == m[i]; }
        { lemma_seq_equality(s[0..|m|], m, b); }
        m + [true] + SequenceOfFalses(NumPaddingZeroes(|m|)) + IntToSeq(b, 64);
        == { assert |m| == b; }
        Pad(m);
     }
}

static method {:timeLimit 30} PadMessageArray(a: array<int>, b: int)
    requires a != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires Word32(b);
    requires 0 <= b < power2(64);
    requires 0 <= b <= PaddedLength(b) <= a.Length * 32;
    ensures forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    ensures ArrayToBitSequence(a, PaddedLength(b)) == Pad(old(ArrayToBitSequence(a, b)));
    modifies a;
{
    lemma_2toX();
    reveal_NumPaddingZeroes();
    reveal_PaddedLength();
    reveal_IsArrayBitSet();
    var numPad := NumPaddingZeroes(b);

    AppendBitToMessageArray(a, b, true);
    AppendBitsToMessageArray(a, b + 1, false, numPad);
    AppendWordToMessageArray(a, b + numPad + 1, 0);
    AppendWordToMessageArray(a, b + numPad + 33, b);

    ghost var m := old(ArrayToBitSequence(a, b));

    assert forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    assert forall i {:trigger m[i]}{:trigger IsArrayBitSet(a, i)} :: 0 <= i < b ==> IsArrayBitSet(a, i) == m[i];
    assert IsArrayBitSet(a, b);
    assert forall i {:trigger IsArrayBitSet(a, i)} :: b + 1 <= i <= b + numPad ==> !IsArrayBitSet(a, i);
    assert a[(b + numPad + 1) / 32] == 0;
    assert a[(b + numPad + 33) / 32] == b;

    Lemma_ArrayIsPaddedMessage(a, b, m);
    assert ArrayToBitSequence(a, PaddedLength(b)) == Pad(m);
}

/////////////////////////////////////////////////////
// Copying messages
/////////////////////////////////////////////////////

static method copy_message_words(data:array<int>, len:int, ghost padded_seq:seq<bool>, block_index:int, wlen:int) returns (W : array<int>)
    requires Word32(len);
    requires len <= power2(32) - 1;
    requires data != null;
    requires 0 < len <= PaddedLength(len) <= data.Length * 32;        // Make padding easier
    requires forall i {:trigger data[i]} :: 0 <= i < data.Length ==> Word32(data[i]);
    requires padded_seq == ArrayToBitSequence(data, PaddedLength(len));
    requires 1 <= block_index <= |padded_seq|/512;
    requires wlen >= 16;
    ensures fresh(W);
    ensures W != null && W.Length == wlen;
    ensures forall i {:trigger data[i]} :: 0 <= i < data.Length ==> data[i] == old(data[i]);
    ensures forall i {:trigger W[i]} :: 0 <= i < 16 ==> Word32(W[i]);
    ensures forall i {:trigger W[i]} :: 0 <= i < 16 ==> W[i] == PaddedMessageWord(i, block_index, padded_seq);
{
    W := new int[wlen];
    var w_index := 0;
    while (w_index < 16) 
        invariant forall i {:trigger data[i]} :: 0 <= i < data.Length ==> Word32(data[i]);
        invariant forall i {:trigger data[i]} :: 0 <= i < data.Length ==> data[i] == old(data[i]);
        invariant 0 <= w_index <= 16;
        invariant forall i {:trigger W[i]} :: 0 <= i < w_index ==> Word32(W[i]);        
//        invariant forall i {:trigger W[i]} :: 0 <= i < w_index ==> W[i] == data[(block_index-1)*16 + i];
        invariant forall i {:trigger W[i]} :: 0 <= i < w_index ==> W[i] == PaddedMessageWord(i, block_index, padded_seq);
    {            
        W[w_index] := data[(block_index-1)*16 + w_index];            
        reveal_IsArrayBitSet();
        lemma_PaddedMessageWordIndexing(data, len, padded_seq, w_index, block_index);
        assert W[w_index] == PaddedMessageWord(w_index, block_index, padded_seq);
        w_index := w_index + 1;        
    }

/*
    assert forall i :: 0 <= i < 16 ==> W[i] == data[(block_index-1)*16 + i];    
    forall i | 0 <= i < 16 
        ensures W[i] == PaddedMessageWord(i, block_index, padded_seq);
    {
        lemma_PaddedMessageWordIndexing(data, len, padded_seq, i, block_index);
        assert W[i] == PaddedMessageWord(i, block_index, padded_seq);
    }
*/
}

static lemma lemma_PaddedMessageWordIndexing(data:array<int>, len:int, padded_seq:seq<bool>, word_index:int, block_index:int)
    requires Word32(len);
    requires len <= power2(32) - 1;
    requires data != null;
    requires 0 < len <= PaddedLength(len) <= data.Length * 32;        // Make padding easier
    requires forall i {:trigger data[i]} :: 0 <= i < data.Length ==> Word32(data[i]);
    requires padded_seq == ArrayToBitSequence(data, PaddedLength(len));
    requires 1 <= block_index <= |padded_seq|/512;
    requires 0 <= word_index <= 15;
    ensures PaddedMessageWord(word_index, block_index, padded_seq) == data[(block_index-1)*16 + word_index];
{
    var bit_start := (block_index-1) * 512 + word_index * 32;
    var bit_end := (block_index-1) * 512 + (word_index+1) * 32;
    var word_start := (block_index-1)*16 + word_index;
    calc {
        PaddedMessageWord(word_index, block_index, padded_seq);
        SeqToInt(padded_seq[bit_start .. bit_end]);
        { 
            forall i | bit_start <= i < bit_end
                //ensures forall i :: 0 <= i < 32 ==> padded_seq[i] == WordToSeq(data[0])[i];
                ensures padded_seq[i] == WordToSeq(data[word_start])[i - bit_start];
            {
                calc ==> {
                    true;
                    ArrayToBitSequence(data, PaddedLength(len))[i] == IsArrayBitSet(data, i);
                    padded_seq[i] == IsArrayBitSet(data, i);
                    { reveal_IsArrayBitSet(); }
                    padded_seq[i] == IsWordBitSet(data[i / 32], i % 32);
                    padded_seq[i] == IsWordBitSet(data[(block_index-1) * 16 + word_index], i % 32);
                    padded_seq[i] == IsWordBitSet(data[word_start], i - bit_start);
                    padded_seq[i] == WordToSeq(data[word_start])[i - bit_start];
                }
            }
            assert forall i {:trigger padded_seq[i]} :: bit_start <= i < bit_end ==> padded_seq[i] == WordToSeq(data[word_start])[i - bit_start];
            calc {
                padded_seq[bit_start..bit_end];
                { lemma_seq_equality(padded_seq[bit_start..bit_end], WordToSeq(data[word_start]), 32); }
                WordToSeq(data[word_start]);
            }
        }    
        SeqToInt(WordToSeq(data[word_start]));
        data[word_start];
    }
}

/////////////////////////////////////////////////////
// HMAC
/////////////////////////////////////////////////////

static method xor_pad(key:array<int>, const:int) returns (pad:array<int>)
    requires key != null && key.Length == 16;
    requires forall i {:trigger key[i]} :: 0 <= i < key.Length ==> Word32(key[i]);
    requires Word32(const);
    ensures fresh(pad);
    ensures forall i {:trigger pad[i]} :: 0 <= i < pad.Length ==> Word32(pad[i]);
    ensures pad.Length == 16;
    ensures WordSeqToBits(pad[..]) == SeqXor(WordSeqToBits(key[..]), ConstPad(512, const));
    //ensures ArrayToBitSequence(pad, 512) == SeqXor(ArrayToBitSequence(key, 512), Opad(512));
{
    pad := new int[16];
    /*
    assert ArrayToBitSequence(pad, 0) == [] && ArrayToBitSequence(key, 0) == [] && Opad(0) == [] && SeqXor([], []) == [];
    var i := 0;
    while (i < 16) 
        invariant 0 <= i <= 16;
        invariant forall j :: 0 <= j < i ==> Word32(pad[j]);
    {
        pad[i] := 0;
        i := i + 1;
    }
    */

    var i := 0;
    while (i < 16) 
        invariant 0 <= i <= 16;
        invariant forall j {:trigger pad[j]} :: 0 <= j < i ==> Word32(pad[j]);    
        invariant forall j {:trigger pad[j]}{:trigger key[j]} :: 0 <= j < i ==> pad[j] == BitwiseXorInstruction(key[j], const);
    {
        pad[i] := BitwiseXorInstruction(key[i], const);
        i := i + 1;
    }    
    lemma_SeqXor_WordSeqToBits(16, pad[..], key[..], const);
    //assert WordSeqToBits(pad[..]) == SeqXor(WordSeqToBits(key[..]), Opad(512));
    //assert ArrayToBitSequence(pad, 512) == SeqXor(ArrayToBitSequence(key, 512), Opad(512));
    // invariant ArrayToBitSequence(pad, i*32) == SeqXor(ArrayToBitSequence(key, i*32), Opad(i*32));
}

static method consolidate_arrays(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a != null && b != null;
    requires forall i {:trigger a[i]} :: 0 <= i < a.Length ==> Word32(a[i]);
    requires forall i {:trigger b[i]} :: 0 <= i < b.Length ==> Word32(b[i]);
    ensures fresh(c);
    ensures forall i {:trigger c[i]} :: 0 <= i < c.Length ==> Word32(c[i]);
    ensures c.Length * 32 == PaddedLength(32*(a.Length+b.Length));
    ensures c[..a.Length+b.Length] == a[..] + b[..]; 
    ensures a[..] == old(a[..]);
    ensures b[..] == old(b[..]);
{
    c := new int[PaddedLength(32*(a.Length+b.Length))/ 32];
    assert c.Length >= a.Length + b.Length;

    var i := 0;
    while (i < a.Length) 
        invariant 0 <= i <= a.Length;
        invariant forall j {:trigger a[j]} :: 0 <= j < a.Length ==> Word32(a[j]);
        invariant forall j {:trigger a[j]}{:trigger c[j]} :: 0 <= j < i ==> c[j] == a[j] && Word32(c[j]);    
    {
        c[i] := a[i];
        i := i+1;
    }
    
    var k := 0;
    while (k < b.Length)         
        invariant 0 <= k <= b.Length;
        invariant i == k + a.Length;
        invariant a.Length <= i <= a.Length + b.Length;
        invariant forall j {:trigger a[j]}{:trigger c[j]} :: 0 <= j < a.Length ==> c[j] == a[j] && Word32(c[j]);
        invariant forall j {:trigger c[j]} :: a.Length <= j < a.Length + k ==> c[j] == b[j-a.Length]; 
        invariant forall j {:trigger c[j]} :: a.Length <= j < a.Length + k ==> Word32(c[j]);
    {
        c[i] := b[k];
        i := i + 1;
        k := k + 1;
    }

    while (i < c.Length)
        invariant a.Length + b.Length <= i <= c.Length;
        invariant forall j {:trigger a[j]}{:trigger c[j]} :: 0 <= j < a.Length ==> c[j] == a[j] && Word32(c[j]);
        invariant forall j {:trigger c[j]} :: a.Length <= j < a.Length + b.Length ==> c[j] == b[j-a.Length] && Word32(c[j]);
        invariant forall j {:trigger c[j]} :: a.Length + b.Length <= j < i ==> Word32(c[j]);
    {
        lemma_2toX();
        c[i] := 0;
        i := i + 1;
    }

    reveal_NumPaddingZeroes();
    reveal_PaddedLength();
}

static method HMAC_outer_input(key: array<int>, inner_hash: array<int>) returns (input: array<int>) 
    requires key != null && key.Length == 16;
    requires forall i {:trigger key[i]} :: 0 <= i < key.Length ==> Word32(key[i]);
    requires inner_hash != null;
    requires forall i {:trigger inner_hash[i]} :: 0 <= i < inner_hash.Length ==> Word32(inner_hash[i]);
    ensures fresh(input);
    ensures forall i {:trigger input[i]} :: 0 <= i < input.Length ==> Word32(input[i]);
//    ensures input.Length == 32;
    ensures input.Length * 32 == PaddedLength(32*(16+inner_hash.Length));
    ensures WordSeqToBits(input[..]) == SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]) + WordSeqToBits(input[16+inner_hash.Length..]);
{
    ghost var old_key := key[..];
    lemma_2toX();
    var opad := xor_pad(key, 0x5c5c5c5c);
    assert old_key == key[..];

    ghost var old_opad := opad[..];

    input := consolidate_arrays(opad, inner_hash);
    assert key[..] == old_key;
    assert opad[..] == old_opad;

    ghost var sum := opad.Length + inner_hash.Length;
    calc {
        WordSeqToBits(input[..]);
//        { lemma_seq_split(input[..]); }
        { assert input[..] == input[..sum] + input[sum..]; }
        WordSeqToBits(input[..sum] + input[sum..]);
        { lemma_IntSeq_Split(input[..sum], input[sum..]); }
        WordSeqToBits(input[..sum]) + WordSeqToBits(input[sum..]);
        WordSeqToBits(opad[..] + inner_hash[..]) + WordSeqToBits(input[sum..]);
        { lemma_IntSeq_Split(opad[..], inner_hash[..]); }
        WordSeqToBits(opad[..]) + WordSeqToBits(inner_hash[..]) + WordSeqToBits(input[sum..]);
        SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]) + WordSeqToBits(input[sum..]);
    }
}

static lemma lemma_HMAC_inner_input(len:int, dataLength32:int, inputLength32:int)
    requires inputLength32 == PaddedLength(512 + dataLength32);
    requires 0 < len <= dataLength32;
    ensures len + 512 <= PaddedLength(len + 512) <= inputLength32;
{
    reveal_PaddedLength();
    reveal_NumPaddingZeroes();
}

static method {:timeLimit 20} HMAC_inner_input(key: array<int>, data: array<int>, len: int) returns (input: array<int>) 
    requires Word32(len);
    requires key != null && key.Length == 16;
    requires forall i {:trigger key[i]} :: 0 <= i < key.Length ==> Word32(key[i]);
    requires data != null;
    requires 0 < len <= data.Length * 32;        
    requires forall i {:trigger data[i]} :: 0 <= i < data.Length ==> Word32(data[i]);
    ensures fresh(input);
    ensures forall i {:trigger input[i]} :: 0 <= i < input.Length ==> Word32(input[i]);
    ensures len + 512 <= PaddedLength(len + 512) <= input.Length * 32;
    ensures input.Length >= 16 + data.Length;
    ensures WordSeqToBits(input[..]) == SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32)) + WordSeqToBits(data[..]) + WordSeqToBits(input[16+data.Length..]);
{    
    ghost var old_key := key[..];
    lemma_2toX();
    var ipad := xor_pad(key, 0x36363636);
    assert old_key == key[..];

    ghost var old_ipad := ipad[..];

    input := consolidate_arrays(ipad, data);
    assert key[..] == old_key;
    assert ipad[..] == old_ipad;
    
    ghost var sum := ipad.Length + data.Length;
    calc {
        WordSeqToBits(input[..]);
//        { lemma_seq_split(input[..]); }
        { assert input[..] == input[..sum] + input[sum..]; }
        WordSeqToBits(input[..sum] + input[sum..]);
        { lemma_IntSeq_Split(input[..sum], input[sum..]); }
        WordSeqToBits(input[..sum]) + WordSeqToBits(input[sum..]);
        WordSeqToBits(ipad[..] + data[..]) + WordSeqToBits(input[sum..]);
        { lemma_IntSeq_Split(ipad[..], data[..]); }
        WordSeqToBits(ipad[..]) + WordSeqToBits(data[..]) + WordSeqToBits(input[sum..]);
        { assert WordSeqToBits(ipad[..])  == SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32)); }
        SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32)) + WordSeqToBits(data[..]) + WordSeqToBits(input[sum..]);
    }
    lemma_HMAC_inner_input(len, data.Length * 32, input.Length * 32);
}

/////////////////////////////////////////////////////
// Other useful lemmas
/////////////////////////////////////////////////////

static lemma lemma_SeqXor_Split(a: seq<bool>, A: seq<bool>, b: seq<bool>, B: seq<bool>)
    requires |a| == |b| && |A| == |B|;
    ensures SeqXor(a + A, b + B) == SeqXor(a, b) + SeqXor(A, B);
{
    reveal_SeqXor();
    if a == [] {
        assert a + A == A;
        assert b + B == B;
    } else {                
        calc {
            SeqXor(a + A, b + B);
            { assert a + A == [a[0]] + (a[1..] + A); assert b + B == [b[0]] + (b[1..] + B); }
            [a[0] != b[0]] + SeqXor(a[1..] + A, b[1..]+B);
            { lemma_SeqXor_Split(a[1..], A, b[1..], B); }
            [a[0] != b[0]] + SeqXor(a[1..], b[1..]) + SeqXor(A, B);
            SeqXor(a, b) + SeqXor(A, B);
        }        
    }
}    

static lemma lemma_SeqXor_Unrolled(a: seq<bool>, b: seq<bool>) 
    requires |a| == |b|;
    ensures forall j {:trigger a[j]}{:trigger b[j]}{:trigger SeqXor(a, b)[j]} :: 0 <= j < |a| ==> SeqXor(a, b)[j] == (a[j] != b[j]);
{}

static lemma lemma_SeqXor_WordSeqToBits(i:int, pad:seq<int>, key:seq<int>, const:int)
    requires |pad| == |key| == i;
    requires Word32(const);
    requires forall j {:trigger pad[j]}{:trigger key[j]} :: 0 <= j < |pad| ==> Word32(pad[j]) && Word32(key[j]);    
    requires forall j {:trigger pad[j]}{:trigger key[j]} :: 0 <= j < |pad| ==> pad[j] == BitwiseXorInstruction(key[j], const);
    ensures WordSeqToBits(pad) == SeqXor(WordSeqToBits(key), ConstPad(i*32, const));
{
    if i == 0 {
        assert WordSeqToBits(pad) == SeqXor(WordSeqToBits(key), ConstPad(i*32, const));
    } else {
        var len0 := i * 32;
        var len1 := (i - 1) * 32;
        ghost var x := SeqXor(WordToSeq(key[0]), WordToSeq(const));
        calc {
            SeqXor(WordSeqToBits(key), ConstPad(len0, const));
            { reveal_WordSeqToBits(); }
            SeqXor(WordToSeq(key[0]) + WordSeqToBits(key[1..]), ConstPad(len0, const));
            { reveal_ConstPad(); assert ConstPad_FULL(len0, const) == WordToSeq(const) + ConstPad(len1, const); assert ConstPad_FULL(len0, const) == ConstPad(len0, const); }  // Needed to deal with Z3 bug
            SeqXor(WordToSeq(key[0]) + WordSeqToBits(key[1..]), WordToSeq(const) + ConstPad(len1, const));
            { assert len1 % 32 == 0; }
            { assert |ConstPad(len1, const)| == len1; }
            { lemma_SeqXor_Split(WordToSeq(key[0]), WordSeqToBits(key[1..]), WordToSeq(const), ConstPad(len1, const)); }
            SeqXor(WordToSeq(key[0]), WordToSeq(const)) + SeqXor(WordSeqToBits(key[1..]), ConstPad(len1, const));
            x + SeqXor(WordSeqToBits(key[1..]), ConstPad(len1, const));
            { assert |pad[1..]| == |key[1..]| == i - 1; lemma_SeqXor_WordSeqToBits(i - 1, pad[1..], key[1..], const); assert WordSeqToBits(pad[1..]) == SeqXor(WordSeqToBits(key[1..]), ConstPad(len1, const)); }
            x + WordSeqToBits(pad[1..]);
            SeqXor(WordToSeq(key[0]), WordToSeq(const)) + WordSeqToBits(pad[1..]);
            { lemma_SeqXor_Unrolled(WordToSeq(key[0]), WordToSeq(const)); } 
            { assert forall j :: 0 <= j < |WordToSeq(key[0])| ==>
              SeqXor(WordToSeq(key[0]), WordToSeq(const))[j] == WordToSeq(BitwiseXorInstruction(key[0], const))[j]; }
            WordToSeq(BitwiseXorInstruction(key[0], const)) + WordSeqToBits(pad[1..]);
            { reveal_WordSeqToBits(); }
            WordSeqToBits([pad[0]]) + WordSeqToBits(pad[1..]);
            { lemma_IntSeq_Split([pad[0]], pad[1..]); assert pad == [pad[0]] + pad[1..]; }
            WordSeqToBits(pad);
        }        
    }
}
