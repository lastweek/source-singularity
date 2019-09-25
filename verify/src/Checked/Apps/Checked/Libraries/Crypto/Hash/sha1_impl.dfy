include "..\..\..\..\Trusted\Spec\Libraries\Crypto\Hash\sha1_spec.dfy"
include "sha_impl_common.dfy"

/////////////////////////////////////////////////////
// Initialization of data structures
/////////////////////////////////////////////////////

static method InitH() returns (hash: array<int>)
    ensures fresh(hash);
    ensures hash != null && hash.Length == 5;
    ensures forall i :: 0 <= i < hash.Length ==> Word32(hash[i]);
    ensures forall i :: 0 <= i < hash.Length ==> hash[i] == InitialHValue(i);
    ensures forall i, m :: 0 <= i < hash.Length && |m| < power2(64) ==> hash[i] == H(i, 0, m);
{
    hash := new int[5];
    hash[0] := 0x67452301;
    hash[1] := 0xefcdab89;
    hash[2] := 0x98badcfe;
    hash[3] := 0x10325476;
    hash[4] := 0xc3d2e1f0;

    lemma_2toX();
    reveal_H();
}

static method InitK() returns (Karr: array<int>)
    ensures fresh(Karr);
    ensures Karr != null && Karr.Length == 80;
    ensures forall i :: 0 <= i < Karr.Length ==> Word32(Karr[i]);
    ensures forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i);
{
    Karr := new int[80];

    var i := 0;
    while (i < 20)
        invariant 0 <= i <= 20;
        invariant forall j :: 0 <= j < i ==> Karr[j] == K(j);
    {
        Karr[i] := 0x5a827999;
        i := i + 1;
    }
    while (i < 40)
        invariant 20 <= i <= 40;
        invariant forall j :: 0 <= j < i ==> Karr[j] == K(j);
    {
        Karr[i] := 0x6ed9eba1;
        i := i + 1;
    }
    while (i < 60)
        invariant 40 <= i <= 60;
        invariant forall j :: 0 <= j < i ==> Karr[j] == K(j);
    {
        Karr[i] := 0x8f1bbcdc;
        i := i + 1;
    }
    while (i < 80)
        invariant 60 <= i <= 80;
        invariant forall j :: 0 <= j < i ==> Karr[j] == K(j);
    {
        Karr[i] := 0xca62c1d6;
        i := i + 1;
    }
}

/////////////////////////////////////////////////////
// Stepping through the algorithm
/////////////////////////////////////////////////////

datatype compress_state = build(a:int, b:int, c:int, d:int, e:int);

static function {:hidden} valid_compress_state(state:compress_state, step:int, block_index:int, m:seq<bool>) : bool
{
    |m| < power2(64) &&
    1 <= step <= 161 &&
    step % 2 == 1 &&
    1 <= block_index <= NumBlocks(m) &&
    Word32(state.a) && Word32(state.b) && Word32(state.c) && Word32(state.d) && Word32(state.e) &&
    state.a == a(step, block_index, m) &&
    state.b == b(step, block_index, m) &&
    state.c == c(step, block_index, m) &&
    state.d == d(step, block_index, m) &&
    state.e == e(step, block_index, m)
}

static method compress_init(hash:array<int>, block_index:int, ghost m:seq<bool>) returns (state:compress_state)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);
    requires hash != null;
    requires hash.Length == 5;
    requires forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index - 1, m) && Word32(hash[i]);
    ensures valid_compress_state(state, 1, block_index, m);
{
    reveal_valid_compress_state();
    reveal_a(); reveal_e();
    state := build(hash[0], hash[1], hash[2], hash[3], hash[4]);
}

static method compress_step(old_state:compress_state, ghost step:int, round:int, Karr:array<int>, Warr:array<int>, block_index:int, ghost m:seq<bool>) returns (new_state:compress_state)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);
    requires 0 <= round < 80;
    requires step == round * 2 + 1;
    requires 1 <= step <= 159 && step % 2 == 1;
    requires Karr != null && Warr != null;
    requires Karr.Length == 80 && Warr.Length == 80;
    requires forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i) && Word32(Karr[i]);
    requires forall i :: 0 <= i < Warr.Length ==> Warr[i] == W(i, block_index, m) && Word32(Warr[i]);
    requires valid_compress_state(old_state, step, block_index, m);
    ensures valid_compress_state(new_state, step+2, block_index, m);
{
    reveal_valid_compress_state();

    var T_local := AddInstruction(AddInstruction(AddInstruction(AddInstruction(RotateLeftInstruction(old_state.a, 5),
                                                                               ft(round, old_state.b, old_state.c, old_state.d)),
                                                                old_state.e),
                                                 Karr[round]),
                                  Warr[round]);

    ghost var step_orig := step;
    ghost var step_new  := step + 1;
    assert step % 2 == 1;
    lemma_mod2_plus(step);
    assert step_new % 2 == 0;

    calc {
        T_local;
        AddInstruction(AddInstruction(AddInstruction(AddInstruction(RotateLeftInstruction(old_state.a, 5),
                                                                    ft(round, old_state.b, old_state.c, old_state.d)),
                                                     old_state.e),
                                      Karr[round]),
                       Warr[round]);
        AddInstruction(AddInstruction(AddInstruction(AddInstruction(RotateLeftInstruction(a(step_new-1, block_index, m), 5),
                                                                    ft(round, b(step_new-1, block_index, m), c(step_new-1, block_index, m), d(step_new-1, block_index, m))),
                                                     e(step_new-1, block_index, m)),
                                      Karr[round]),
                       Warr[round]);
        AddInstruction(AddInstruction(AddInstruction(AddInstruction(RotateLeftInstruction(a(step_new-1, block_index, m), 5),
                                                                    ft(round, b(step_new-1, block_index, m), c(step_new-1, block_index, m), d(step_new-1, block_index, m))),
                                                     e(step_new-1, block_index, m)),
                                      K(round)),
                       W(round, block_index, m));
        T(step_new, block_index, m);
    }

    new_state := build(T_local, old_state.a, RotateLeftInstruction(old_state.b, 30), old_state.c, old_state.d);
    reveal_a(); reveal_e(); lemma_mod2_plus2(step);
    assert (step+2) % 2 == 1;
    assert 1 <= block_index <= NumBlocks(m);

    assert valid_compress_state(new_state, step+2, block_index, m);
}

static method {:timeLimit 61} compress(hash:array<int>, Karr:array<int>, Warr:array<int>, block_index:int, ghost m:seq<bool>) returns (state:compress_state)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);
    requires hash != null && Karr != null && Warr != null;
    requires hash.Length == 5 && Karr.Length == 80 && Warr.Length == 80;
    requires forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index - 1, m) && Word32(hash[i]);
    requires forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i) && Word32(Karr[i]);
    requires forall i :: 0 <= i < Warr.Length ==> Warr[i] == W(i, block_index, m) && Word32(Warr[i]);
    ensures valid_compress_state(state, 161, block_index, m);
{
    state := compress_init(hash, block_index, m);

    var round := 0;
    ghost var step := 1;
    assert step % 2 == 1;

    while (round < 80)
        invariant 0 <= round <= 80;
        invariant step == round * 2 + 1;
        invariant 1 <= step <= 161;
        invariant step % 2 == 1;
        invariant 1 <= block_index <= NumBlocks(m);
        invariant valid_compress_state(state, step, block_index, m);
    {
        state := compress_step(state, step, round, Karr, Warr, block_index, m);
        lemma_mod2_plus2(step);
        step := step + 2;
        round := round + 1;
    }
    assert valid_compress_state(state, 161, block_index, m);
}

static method extend_message(block_index:int, W_arr:array<int>, ghost m:seq<bool>)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);
    requires W_arr != null && W_arr.Length == 80;
    requires forall i :: 0 <= i < 16 ==> W_arr[i] == PaddedMessageWord(i, block_index, Pad(m));
    modifies W_arr;
    ensures forall i :: 0 <= i < 16 ==> W_arr[i] == old(W_arr[i]);
    ensures forall i :: 0 <= i < 80 ==> W_arr[i] == W(i, block_index, m);
{

    assert forall i :: 0 <= i < 16 ==> W_arr[i] == W(i, block_index, m);

    var w_index := 16;
    while (w_index < 80)
        invariant 16 <= w_index <= 80;
        invariant forall i :: 0 <= i < w_index ==> Word32(W_arr[i]);
        invariant forall i :: 0 <= i < w_index ==> W_arr[i] == W(i, block_index, m);
    {
        W_arr[w_index] := RotateLeftInstruction(BitwiseXorInstruction(BitwiseXorInstruction(BitwiseXorInstruction(W_arr[w_index-3],
                                                                                                                  W_arr[w_index-8]),
                                                                                            W_arr[w_index-14]),
                                                                      W_arr[w_index-16]),
                                                1);
        assert W_arr[w_index] == W(w_index, block_index, m);
        assert forall i :: 0 <= i <= w_index ==> W_arr[i] == W(i, block_index, m);
        w_index := w_index + 1;
    }

}

static method compress_final(state:compress_state, hash:array<int>, hash_old:seq<int>, block_index:int, ghost m:seq<bool>)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);
    requires hash != null;
    requires hash.Length == 5;
    requires forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index - 1, m) && Word32(hash[i]);
    requires valid_compress_state(state, 161, block_index, m);
    requires hash_old == hash[..];
    modifies hash;
    ensures forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index, m) && Word32(hash[i]);
{
    reveal_valid_compress_state();
    reveal_H();
    hash[0] := AddInstruction(state.a, hash[0]);
    hash[1] := AddInstruction(state.b, hash[1]);
    hash[2] := AddInstruction(state.c, hash[2]);
    hash[3] := AddInstruction(state.d, hash[3]);
    hash[4] := AddInstruction(state.e, hash[4]);
}

/////////////////////////////////////////////////////
// Overall calculation
/////////////////////////////////////////////////////

static method {:timeLimit 30} SHA1impl(data: array<int>, len: int) returns (hash: array<int>)
    requires Word32(len);
    requires len <= power2(32) - 1;
    requires data != null;
    requires 0 < len <= PaddedLength(len) <= data.Length * 32;        // Make padding easier
    requires forall i :: 0 <= i < data.Length ==> Word32(data[i]);
    modifies data;
    ensures fresh(hash);
    ensures hash != null && hash.Length == 5 && forall i :: 0 <= i < hash.Length ==> Word32(hash[i]);
    ensures len < power2(64) && hash[..] == SHA1(old(ArrayToBitSequence(data, len)));
{
    var Karr := InitK();
    hash := InitH();

    lemma_2toX();
    PadMessageArray(data, len);
    ghost var original_msg := old(ArrayToBitSequence(data, len));
    ghost var padded_seq := ArrayToBitSequence(data, PaddedLength(len));


    var block_index := 0;
    var num_blocks := PaddedLength(len) / 512;
    //reveal_NumBlocks();

    while (block_index < num_blocks)
        invariant 0 <= block_index <= num_blocks == NumBlocks(original_msg);
        invariant hash != null && hash.Length == 5 && forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index, original_msg) && Word32(hash[i]);
        invariant forall i :: 0 <= i < data.Length ==> Word32(data[i]);
        invariant padded_seq == ArrayToBitSequence(data, PaddedLength(len));
        invariant forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i) && Word32(Karr[i]);
        modifies  hash;
    {
        assert block_index+1 <= num_blocks;
        ghost var old_hash := hash[..];
        ghost var old_Karr := Karr[..];
        var W_arr := copy_message_words(data, len, padded_seq, block_index+1, 80);
        assert hash[..] == old_hash;
        assert Karr[..] == old_Karr;
        extend_message(block_index+1, W_arr, original_msg);
        assert hash[..] == old_hash;
        assert Karr[..] == old_Karr;

        var state := compress(hash, Karr, W_arr, block_index+1, original_msg);
        compress_final(state, hash, hash[..], block_index+1, original_msg);

        block_index := block_index + 1;
    }

    lemma_connect_SHA1(hash[..], original_msg);
    assert hash[..] == SHA1(original_msg);
}

static lemma lemma_connect_SHA1(hash:seq<int>, original_msg:seq<bool>)
    requires |original_msg| < power2(64);
    requires |hash| == 5;
    requires forall i :: 0 <= i < 5 ==> hash[i] == H(i, NumBlocks(original_msg), original_msg) && Word32(hash[i]);
    ensures hash == SHA1(original_msg);
{
    reveal_SHA1();
}

static method HMAC_inner_hash(key: array<int>, data: array<int>, len: int) returns (hash: array<int>)
    requires Word32(len);
    requires key != null && key.Length == 16;
    requires forall i :: 0 <= i < key.Length ==> Word32(key[i]);
    requires len <= power2(32) - 1 - 512;
    requires data != null;
    requires 0 < data.Length;
    requires 0 < len <= data.Length * 32;
    requires forall i :: 0 <= i < data.Length ==> Word32(data[i]);
    ensures fresh(hash);
    ensures forall i :: 0 <= i < hash.Length ==> Word32(hash[i]);
    //ensures 18446744073709551616 == power2(64);
    ensures var input := SeqXor(ArrayToBitSequence(key, key.Length*32), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len);
        |input| < power2(64) && hash[..] == SHA1(input);
{
    var input := HMAC_inner_input(key, data, len);
    lemma_2toX();
    ghost var old_input := ArrayToBitSequence(input, len+512);

    calc {
        old_input;
        ArrayToBitSequence(input, len+512);
        { lemma_IntSeq_ConvertMessage(input, len+512);
          assert forall i :: 0 <= i < len + 512 ==> ArrayToBitSequence(input, len+512)[i] == WordSeqToBits(input[..])[i];
          assert WordSeqToBits(input[..])[..len+512] == ArrayToBitSequence(input, len+512);
        }
        WordSeqToBits(input[..])[..len+512];
        (SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32)) + WordSeqToBits(data[..]) + WordSeqToBits(input[16+data.Length..]))[..len+512];
        { assert |SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32))| == 512;  assert |WordSeqToBits(data[..])| >= len; } // == |data[..]|*32; }
        SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32)) + WordSeqToBits(data[..])[..len];
        { lemma_IntSeq_ConvertMessage(data, len); }
        SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len);
        { lemma_IntSeq_ConvertMessage(key, key.Length * 32);
          assert ArrayToBitSequence(key, key.Length*32) == WordSeqToBits(key[..]); }
        SeqXor(ArrayToBitSequence(key, key.Length*32), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len);
    }

    hash := SHA1impl(input, len+512);
    lemma_2toX();
    assert hash[..] == SHA1(old_input);
}

static method HMAC_impl(key: array<int>, data: array<int>, len: int) returns (hash: array<int>)
    requires Word32(len);
    requires key != null && key.Length == 16;
    requires forall i :: 0 <= i < key.Length ==> Word32(key[i]);
    requires len <= power2(32) - 1 - 512;
    requires data != null;
    requires 0 < data.Length;
    requires 0 < len <= data.Length * 32;
    requires forall i :: 0 <= i < data.Length ==> Word32(data[i]);
    ensures fresh(hash);
    ensures forall i :: 0 <= i < hash.Length ==> Word32(hash[i]);
    ensures var k := ArrayToBitSequence(old(key), 32*key.Length);
            var m := ArrayToBitSequence(old(data), len);
            |m| < power2(64) - 8*64 &&
            hash[..] == HMAC(k, m);
{
    var inner_hash := HMAC_inner_hash(key, data, len);
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);
    lemma_2toX();
    assert inner_hash[..] == SHA1(SeqXor(ArrayToBitSequence(key, key.Length*32), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len));
    ghost var old_inner_hash := inner_hash[..];

    var input := HMAC_outer_input(key, inner_hash);
    assert WordSeqToBits(input[..]) == SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]) + WordSeqToBits(input[16+5..]);
    assert old_inner_hash == inner_hash[..];
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);
    var original_input := input[..];

    assert old_inner_hash == inner_hash[..];
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);
    assert Word32(len) ==> (0 <= len < power2(32));
    var bit_len := 32*(key.Length + inner_hash.Length);
    ghost var old_input := ArrayToBitSequence(input, bit_len);
    assert old_inner_hash == inner_hash[..];

    calc {
        old_input;
        ArrayToBitSequence(input, bit_len);
        { lemma_IntSeq_ConvertMessage(input, bit_len);
          assert forall i :: 0 <= i < bit_len ==> ArrayToBitSequence(input, bit_len)[i] == WordSeqToBits(input[..])[i]; }
        WordSeqToBits(input[..])[..bit_len];
        (SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]) + WordSeqToBits(input[16+5..]))[..bit_len];
        (SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]))[..bit_len];
        SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]);
        SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(SHA1(SeqXor(ArrayToBitSequence(key, key.Length*32), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len)));
    }

    hash := SHA1impl(input, bit_len);
    assert hash[..] == SHA1(old_input);
    assert old_inner_hash == inner_hash[..];
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);

    ghost var key_bits := key.Length*32;
    ghost var k := ArrayToBitSequence(key, key_bits);
    ghost var m := ArrayToBitSequence(data, len);
    calc {
        hash[..];
        SHA1(old_input);
        SHA1(SeqXor(WordSeqToBits(key[..]),
                    Opad(|key[..]|*32))
             + WordSeqToBits(SHA1(SeqXor(ArrayToBitSequence(key, key.Length*32),
                                        Ipad(|key[..]|*32))
                                 + ArrayToBitSequence(data, len))));
        { lemma_IntSeq_ConvertMessage(key, key_bits);
          assert ArrayToBitSequence(key, key_bits) == WordSeqToBits(key[..]);
        }
        SHA1(SeqXor(k,
                    Opad(|k|))
             + WordSeqToBits(SHA1(SeqXor(k,
                                        Ipad(|k|))
                                 + m)));
        HMAC(k, m);
    }
}


// FIPS says:
// SHA1("abc") = A9993E36 4706816A BA3E2571 7850C26C 9CD0D89D
// http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA1.pdf
method Test1() {
    var data := new int[16];
    data[0] := 0x61626300;

    lemma_2toX();
    assert Word32(data[0]);
    var i := 1;
    while (i < data.Length)
        invariant 1 <= i <= data.Length;
        invariant forall j :: 0 <= j < i ==> Word32(data[j]);
    {
        data[i] := 0;
        i := i + 1;
    }

    //lemma_short_PaddedLength();
    var hash := SHA1impl(data, 24);

    i := 0;
    while (i < hash.Length)
    {
        print hash[i];
        i := i + 1;
    }
}

// FIPS says:
// SHA1("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
// 84983E44 1C3BD26E BAAE4AA1 F95129E5 E54670F1
// http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA1.pdf
method Test2() {
    var data := new int[32];
    data[0]  := 0x61626364;
    data[1]  := 0x62636465;
    data[2]  := 0x63646566;
    data[3]  := 0x64656667;
    data[4]  := 0x65666768;
    data[5]  := 0x66676869;
    data[6]  := 0x6768696A;
    data[7]  := 0x68696A6B;
    data[8]  := 0x696A6B6C;
    data[9]  := 0x6A6B6C6D;
    data[10] := 0x6B6C6D6E;
    data[11] := 0x6C6D6E6F;
    data[12] := 0x6D6E6F70;
    data[13] := 0x6E6F7071;
    data[14] := 0;
    data[15] := 0;

    lemma_2toX();

    assert forall j :: 0 <= j < 16 ==> Word32(data[j]);

    var i := 16;
    while (i < data.Length)
        invariant 16 <= i <= data.Length;
        invariant forall j :: 0 <= j < i ==> Word32(data[j]);
    {
        data[i] := 0;
        i := i + 1;
    }

    //lemma_medium_PaddedLength();
    var hash := SHA1impl(data, 448);

    i := 0;
    while (i < hash.Length)
    {
        print hash[i];
        i := i + 1;
    }
}


method Main() {
    Test1();
    Test2();
}
