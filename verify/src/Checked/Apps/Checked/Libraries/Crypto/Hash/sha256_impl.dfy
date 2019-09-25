include "..\..\..\..\Trusted\Spec\Libraries\Crypto\Hash\sha256_spec.dfy"
include "sha_impl_common.dfy"

/////////////////////////////////////////////////////
// Initialization of data structures
/////////////////////////////////////////////////////

static method InitH() returns (hash: array<int>) 
    ensures fresh(hash);
    ensures hash != null && hash.Length ==  8;    
    ensures forall i :: 0 <= i < hash.Length ==> Word32(hash[i]);    
    ensures forall i :: 0 <= i < hash.Length ==> hash[i] == InitialHValue(i);
    ensures forall i, m :: 0 <= i < hash.Length && |m| < power2(64) ==> hash[i] == H(i, 0, m);
{
    hash := new int[8];
    hash[0] := 1779033703; 
    hash[1] := 3144134277; 
    hash[2] := 1013904242; 
    hash[3] := 2773480762; 
    hash[4] := 1359893119; 
    hash[5] := 2600822924; 
    hash[6] :=  528734635; 
    hash[7] := 1541459225; 
    
    lemma_2toX();
    reveal_H();
}

static method InitK() returns (Karr: array<int>) 
    ensures fresh(Karr);
    ensures Karr != null && Karr.Length ==  64;    
    ensures forall i :: 0 <= i < Karr.Length ==> Word32(Karr[i]);    
    ensures forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i);
{
    Karr := new int[64];
    InitK_0_to_10(Karr);
    InitK_11_to_20(Karr);
    InitK_21_to_30(Karr);
    InitK_31_to_40(Karr);
    InitK_41_to_50(Karr);
    InitK_51_to_60(Karr);
    InitK_61_to_63(Karr);
}

static method InitK_0_to_10(Karr: array<int>) 
    requires Karr != null && Karr.Length == 64;
    modifies Karr;
    ensures forall i :: 0 <= i <= 10 ==> Word32(Karr[i]);
    ensures forall i :: 0 <= i <= 10 ==> Karr[i] == K(i);
    ensures forall i :: 10 < i < Karr.Length ==> Karr[i] == old(Karr[i]);
{
    Karr [0] := 1116352408;
    Karr [1] := 1899447441;
    Karr [2] := 3049323471;
    Karr [3] := 3921009573;
    Karr [4] := 961987163;
    Karr [5] := 1508970993;
    Karr [6] := 2453635748;
    Karr [7] := 2870763221;
    Karr [8] := 3624381080;
    Karr [9] := 310598401;
    Karr[10] := 607225278;    
    lemma_2toX();
}

static method InitK_11_to_20(Karr: array<int>) 
    requires Karr != null && Karr.Length == 64;
    modifies Karr;
    ensures forall i :: 11 <= i <= 20 ==> Word32(Karr[i]);
    ensures forall i :: 11 <= i <= 20 ==> Karr[i] == K(i);
    ensures forall i :: 0 <= i < 11 || 20 < i < Karr.Length ==> Karr[i] == old(Karr[i]);
{
    Karr[11] := 1426881987;
    Karr[12] := 1925078388;
    Karr[13] := 2162078206;
    Karr[14] := 2614888103;
    Karr[15] := 3248222580;
    Karr[16] := 3835390401;
    Karr[17] := 4022224774;
    Karr[18] := 264347078;
    Karr[19] := 604807628;
    Karr[20] := 770255983;
    lemma_2toX();
}

static method InitK_21_to_30(Karr: array<int>)
    requires Karr != null && Karr.Length == 64;
    modifies Karr;
    ensures forall i :: 21 <= i <= 30 ==> Word32(Karr[i]);
    ensures forall i :: 21 <= i <= 30 ==> Karr[i] == K(i);
    ensures forall i :: 0 <= i < 21 || 30 < i < Karr.Length ==> Karr[i] == old(Karr[i]);
{
    Karr[21] := 1249150122;
    Karr[22] := 1555081692;
    Karr[23] := 1996064986;
    Karr[24] := 2554220882;
    Karr[25] := 2821834349;
    Karr[26] := 2952996808;
    Karr[27] := 3210313671;
    Karr[28] := 3336571891;
    Karr[29] := 3584528711;
    Karr[30] := 113926993;
    lemma_2toX();
}

static method InitK_31_to_40(Karr: array<int>) 
    requires Karr != null && Karr.Length == 64;
    modifies Karr;
    ensures forall i :: 31 <= i <= 40 ==> Word32(Karr[i]);
    ensures forall i :: 31 <= i <= 40 ==> Karr[i] == K(i);
    ensures forall i :: 0 <= i < 31 || 40 < i < Karr.Length ==> Karr[i] == old(Karr[i]);
{
    Karr[31] := 338241895;
    Karr[32] := 666307205;
    Karr[33] := 773529912;    
    Karr[34] := 1294757372;
    Karr[35] := 1396182291;
    Karr[36] := 1695183700;
    Karr[37] := 1986661051;
    Karr[38] := 2177026350;
    Karr[39] := 2456956037;
    Karr[40] := 2730485921;

    lemma_2toX();
}

static method InitK_41_to_50(Karr: array<int>) 
    requires Karr != null && Karr.Length == 64;
    modifies Karr;
    ensures forall i :: 41 <= i <= 50 ==> Word32(Karr[i]);
    ensures forall i :: 41 <= i <= 50 ==> Karr[i] == K(i);
    ensures forall i :: 0 <= i < 41 || 50 < i < Karr.Length ==> Karr[i] == old(Karr[i]);
{
    Karr[41] := 2820302411;
    Karr[42] := 3259730800;
    Karr[43] := 3345764771;
    Karr[44] := 3516065817;
    Karr[45] := 3600352804;
    Karr[46] := 4094571909;
    Karr[47] := 275423344;
    Karr[48] := 430227734;
    Karr[49] := 506948616;
    Karr[50] := 659060556;

    lemma_2toX();
}

static method InitK_51_to_60(Karr: array<int>) 
    requires Karr != null && Karr.Length == 64;
    modifies Karr;
    ensures forall i :: 51 <= i <= 60 ==> Word32(Karr[i]);
    ensures forall i :: 51 <= i <= 60 ==> Karr[i] == K(i);
    ensures forall i :: 0 <= i < 51 || 60 < i < Karr.Length ==> Karr[i] == old(Karr[i]);
{
    Karr[51] := 883997877;
    Karr[52] := 958139571;
    Karr[53] := 1322822218;
    Karr[54] := 1537002063;
    Karr[55] := 1747873779;
    Karr[56] := 1955562222;
    Karr[57] := 2024104815;
    Karr[58] := 2227730452;
    Karr[59] := 2361852424;
    Karr[60] := 2428436474;

    lemma_2toX();
}

static method InitK_61_to_63(Karr: array<int>) 
    requires Karr != null && Karr.Length == 64;
    modifies Karr;
    ensures forall i :: 61 <= i <= 63 ==> Word32(Karr[i]);
    ensures forall i :: 61 <= i <= 63 ==> Karr[i] == K(i);
    ensures forall i :: 0 <= i < 61 ==> Karr[i] == old(Karr[i]);
{
    Karr[61] := 2756734187;
    Karr[62] := 3204031479;
    Karr[63] := 3329325298;    

    lemma_2toX();
}

/////////////////////////////////////////////////////
// Stepping through the algorithm
/////////////////////////////////////////////////////

datatype compress_state = build(a:int, b:int, c:int, d:int, e:int, f:int, g:int, h:int);

static function {:hidden} valid_compress_state(state:compress_state, step:int, block_index:int, m:seq<bool>) : bool
{
    |m| < power2(64) &&
    1 <= step <= 129 &&
    step % 2 == 1 &&
    1 <= block_index <= NumBlocks(m) &&
    Word32(state.a) && Word32(state.b) && Word32(state.c) && Word32(state.d) && Word32(state.e) && Word32(state.f) && Word32(state.g) && Word32(state.h)
    &&
    state.a == a(step, block_index, m) &&
    state.b == b(step, block_index, m) &&
    state.c == c(step, block_index, m) &&
    state.d == d(step, block_index, m) &&
    state.e == e(step, block_index, m) &&
    state.f == f(step, block_index, m) &&
    state.g == g(step, block_index, m) &&
    state.h == h(step, block_index, m)
}

static method compress_init(hash:array<int>, Karr:array<int>, Warr:array<int>, block_index:int, ghost m:seq<bool>) returns (state:compress_state)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);    
    requires hash != null && Karr != null && Warr != null;
    requires hash.Length == 8 && Karr.Length == 64 && Warr.Length == 64;
    requires forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index - 1, m) && Word32(hash[i]);
    requires forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i) && Word32(Karr[i]);
    requires forall i :: 0 <= i < Warr.Length ==> Warr[i] == W(i, block_index, m) && Word32(Warr[i]);
    ensures valid_compress_state(state, 1, block_index, m);
{
    reveal_valid_compress_state();
    reveal_a(); reveal_e();
    state := build(hash[0], hash[1], hash[2], hash[3], hash[4], hash[5], hash[6], hash[7]);
}

static method compress_step(old_state:compress_state, ghost step:int, round:int, Karr:array<int>, Warr:array<int>, block_index:int, ghost m:seq<bool>) returns (new_state:compress_state)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);    
    requires 0 <= round < 64;
    requires step == round * 2 + 1;
    requires 1 <= step <= 127 && step % 2 == 1;
    requires Karr != null && Warr != null;
    requires Karr.Length == 64 && Warr.Length == 64;
    requires forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i) && Word32(Karr[i]);
    requires forall i :: 0 <= i < Warr.Length ==> Warr[i] == W(i, block_index, m) && Word32(Warr[i]);
    requires valid_compress_state(old_state, step, block_index, m);
    ensures valid_compress_state(new_state, step+2, block_index, m);
{
    reveal_valid_compress_state();
    var BSIG1_of_e := BSIG1(old_state.e);
    var CH_of_e_f_g := Ch(old_state.e, old_state.f, old_state.g);
    var Maj_a_b_c := Maj(old_state.a, old_state.b, old_state.c);
    var BSIG0_of_a := BSIG0(old_state.a);
    var T1_local := AddInstruction(AddInstruction(AddInstruction(AddInstruction(old_state.h, BSIG1_of_e),
                                                                    CH_of_e_f_g),
                                                    Karr[round]),
                                    Warr[round]);
    var T2_local := AddInstruction(BSIG0_of_a, Maj_a_b_c);

    ghost var step_orig := step;
    ghost var step_new  := step + 1;
    assert step % 2 == 1;
    lemma_mod2_plus(step);
    assert step_new % 2 == 0;
        
    calc {
        T2_local;
        AddInstruction(BSIG0_of_a, Maj_a_b_c);
        AddInstruction(BSIG0(old_state.a), Maj(old_state.a, old_state.b, old_state.c));
        AddInstruction(BSIG0(a(step_new-1, block_index, m)), Maj(a(step_new-1, block_index, m), b(step_new-1, block_index, m), c(step_new-1, block_index, m)));
        T2(step_new, block_index, m);
    }

    calc {
        //T1_local;
        AddInstruction(AddInstruction(AddInstruction(AddInstruction(old_state.h, BSIG1_of_e),
                                                                    CH_of_e_f_g),
                                                    Karr[round]),
                                      Warr[round]);
        AddInstruction(AddInstruction(AddInstruction(AddInstruction(h(step_new-1, block_index, m), BSIG1_of_e),
                                                                    CH_of_e_f_g),
                                                    Karr[round]),
                                      Warr[round]);
        AddInstruction(AddInstruction(AddInstruction(AddInstruction(h(step_new-1, block_index, m), BSIG1_of_e),
                                                                    CH_of_e_f_g),
                                                    K(round)),
                                      W(round, block_index, m));
        T1(step_new, block_index, m);
    }

    new_state := build(AddInstruction(T1_local, T2_local), old_state.a, old_state.b, old_state.c, AddInstruction(old_state.d, T1_local), old_state.e, old_state.f, old_state.g);
    reveal_a(); reveal_e(); lemma_mod2_plus2(step);
    //assert     |m| < power2(64); 
    //assert 1 <= step+2 <= 129;
    assert (step+2) % 2 == 1; 
    assert 1 <= block_index <= NumBlocks(m);
    //assert Word32(new_state.a) && Word32(new_state.b) && Word32(new_state.c) && Word32(new_state.d) && Word32(new_state.e) && Word32(new_state.f) && Word32(new_state.g) && Word32(new_state.h);
//    assert new_state.a == a(step+2, block_index, m);
//    assert new_state.b == b(step+2, block_index, m);
//    assert new_state.c == c(step+2, block_index, m);
//    assert new_state.d == d(step+2, block_index, m);
//    assert new_state.e == e(step+2, block_index, m);
//    assert new_state.f == f(step+2, block_index, m);
//    assert new_state.g == g(step+2, block_index, m);
//    assert new_state.h == h(step+2, block_index, m);

    assert valid_compress_state(new_state, step+2, block_index, m);
}

static method {:timeLimit 61} compress(hash:array<int>, Karr:array<int>, Warr:array<int>, block_index:int, ghost m:seq<bool>) returns (state:compress_state)
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);    
    requires hash != null && Karr != null && Warr != null;
    requires hash.Length == 8 && Karr.Length == 64 && Warr.Length == 64;
    requires forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index - 1, m) && Word32(hash[i]);
    requires forall i :: 0 <= i < Karr.Length ==> Karr[i] == K(i) && Word32(Karr[i]);
    requires forall i :: 0 <= i < Warr.Length ==> Warr[i] == W(i, block_index, m) && Word32(Warr[i]);
    //modifies hash;
    ensures valid_compress_state(state, 129, block_index, m);    
{
    state := compress_init(hash, Karr, Warr, block_index, m);

    var round := 0;
    ghost var step := 1;
    assert step % 2 == 1;

    while (round < 64) 
        invariant 0 <= round <= 64;
        invariant step == round * 2 + 1;
        invariant 1 <= step <= 129;
        invariant step % 2 == 1;
        invariant 1 <= block_index <= NumBlocks(m);    
        invariant valid_compress_state(state, step, block_index, m);    
    {
        state := compress_step(state, step, round, Karr, Warr, block_index, m);
        lemma_mod2_plus2(step);
        step := step + 2;
        round := round + 1;
    }
    assert valid_compress_state(state, 129, block_index, m);    
}

static method extend_message(block_index:int, W_arr:array<int>, ghost m:seq<bool>) 
    requires |m| < power2(64);
    requires 1 <= block_index <= NumBlocks(m);
    requires W_arr != null && W_arr.Length == 64;
    requires forall i :: 0 <= i < 16 ==> W_arr[i] == PaddedMessageWord(i, block_index, Pad(m));
    modifies W_arr;
    ensures forall i :: 0 <= i < 16 ==> W_arr[i] == old(W_arr[i]);
    ensures forall i :: 0 <= i < 64 ==> W_arr[i] == W(i, block_index, m);
{
    
    assert forall i :: 0 <= i < 16 ==> W_arr[i] == W(i, block_index, m);

    var w_index := 16;
    while (w_index < 64) 
        invariant 16 <= w_index <= 64;
        invariant forall i :: 0 <= i < w_index ==> Word32(W_arr[i]);
        invariant forall i :: 0 <= i < w_index ==> W_arr[i] == W(i, block_index, m);
    {
        var w1_val := W_arr[w_index - 2];        
        var SSIG1_val := BitwiseXorInstruction(BitwiseXorInstruction(RotateRightInstruction(w1_val, 17), RotateRightInstruction(w1_val, 19)), RightShiftInstruction(w1_val, 10));
        assert SSIG1_val == SSIG1(W(w_index - 2, block_index, m));

        var w0_val := W_arr[w_index - 15];
        var SSIG0_val := BitwiseXorInstruction(BitwiseXorInstruction(RotateRightInstruction(w0_val, 7), RotateRightInstruction(w0_val, 18)), RightShiftInstruction(w0_val, 3));
        assert SSIG0_val == SSIG0(W(w_index - 15, block_index, m));

        W_arr[w_index] := AddInstruction(AddInstruction(AddInstruction(SSIG1_val, W_arr[w_index - 7]), SSIG0_val), W_arr[w_index - 16]);

        assert W_arr[w_index] == W(w_index, block_index, m);
        assert forall i :: 0 <= i <= w_index ==> W_arr[i] == W(i, block_index, m);
        w_index := w_index + 1;
    }

}

static method compress_final(state:compress_state, hash:array<int>, hash_old:seq<int>, block_index:int, ghost m:seq<bool>) 
    requires |m| < power2(64);
    //requires 1 <= block_index <= |m|/512;    
    requires 1 <= block_index <= NumBlocks(m);
    requires hash != null;
    requires hash.Length == 8;
    requires forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index - 1, m) && Word32(hash[i]);
    requires valid_compress_state(state, 129, block_index, m);
    requires hash_old == hash[..];
    modifies hash;
    ensures forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index, m) && Word32(hash[i]);
{
    reveal_valid_compress_state();
    //expose_valid_compress_state(state, 129, block_index, m);
    reveal_H();
    hash[0] := AddInstruction(state.a, hash[0]);
    hash[1] := AddInstruction(state.b, hash[1]);
    hash[2] := AddInstruction(state.c, hash[2]);
    hash[3] := AddInstruction(state.d, hash[3]);
    hash[4] := AddInstruction(state.e, hash[4]);
    hash[5] := AddInstruction(state.f, hash[5]);
    hash[6] := AddInstruction(state.g, hash[6]);
    hash[7] := AddInstruction(state.h, hash[7]);
}

/////////////////////////////////////////////////////
// Overall calculation
/////////////////////////////////////////////////////

static method {:timeLimit 30} SHA256impl(data: array<int>, len: int) returns (hash: array<int>) 
    requires Word32(len);
    requires len <= power2(32) - 1;
    requires data != null;
    requires 0 < len <= PaddedLength(len) <= data.Length * 32;        // Make padding easier
    requires forall i :: 0 <= i < data.Length ==> Word32(data[i]);
    //ensures hash = SHA256(len, data);
    modifies data;
  ensures fresh(hash);
    ensures hash != null && hash.Length == 8  && forall i :: 0 <= i < hash.Length ==> Word32(hash[i]); // && hash[i] == SHA256(old(ArrayToBitSequence(data, len)))[i];
    ensures len < power2(64) && hash[..] == SHA256(old(ArrayToBitSequence(data, len)));
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
        //invariant 1 <= block_index + 1 <= PaddedLength(len) / 512;
        invariant hash != null && hash.Length == 8 && forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, block_index, original_msg) && Word32(hash[i]);
        invariant forall i :: 0 <= i < data.Length ==> Word32(data[i]);
        invariant padded_seq == ArrayToBitSequence(data, PaddedLength(len));    
        modifies  hash;
    {        
        //lemma_PaddedLength();
        //assert block_index+1 <= |original_msg| / 512;
        assert block_index+1 <= num_blocks;
        ghost var old_hash := hash[..];
        ghost var old_Karr := Karr[..];
        var W_arr := copy_message_words(data, len, padded_seq, block_index+1, 64);
        assert hash[..] == old_hash;
        assert Karr[..] == old_Karr;
        extend_message(block_index+1, W_arr, original_msg);
        assert hash[..] == old_hash;
        assert Karr[..] == old_Karr;

        var state := compress(hash, Karr, W_arr, block_index+1, original_msg);
        compress_final(state, hash, hash[..], block_index+1, original_msg);

        block_index := block_index + 1;
    }    

    lemma_connect_SHA(hash[..], original_msg);
//    reveal_SHA256();
//    assert hash != null && hash.Length == 8 && forall i :: 0 <= i < hash.Length ==> hash[i] == H(i, NumBlocks(original_msg), original_msg) && Word32(hash[i]);    
//    assert forall i :: 0 <= i < hash.Length ==> hash[i] == SHA256(original_msg)[i];
    assert hash[..] == SHA256(original_msg);
}

static lemma lemma_connect_SHA(hash:seq<int>, original_msg:seq<bool>) 
    requires |original_msg| < power2(64);
    requires |hash| == 8;
    requires forall i :: 0 <= i < 8 ==> hash[i] == H(i, NumBlocks(original_msg), original_msg) && Word32(hash[i]);    
    ensures hash == SHA256(original_msg);
{
    reveal_SHA256();
    //assert forall i :: 0 <= i < |hash| ==> hash[i] == SHA256(original_msg)[i];
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
        |input| < power2(64) && hash[..] == SHA256(input);
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
        { lemma_IntSeq_ConvertMessage(data, len);
          assert forall i :: 0 <= i < len ==> WordSeqToBits(data[..])[i] == ArrayToBitSequence(data, len)[i]; }
        SeqXor(WordSeqToBits(key[..]), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len);
        { lemma_IntSeq_ConvertMessage(key, key.Length * 32); 
          assert forall i :: 0 <= i < key.Length * 32 ==> WordSeqToBits(key[..])[i] == ArrayToBitSequence(key, key.Length * 32)[i];
          assert ArrayToBitSequence(key, key.Length*32) == WordSeqToBits(key[..]); }
        SeqXor(ArrayToBitSequence(key, key.Length*32), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len);
    }

    hash := SHA256impl(input, len+512);
    lemma_2toX();
    assert hash[..] == SHA256(old_input);
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
    ensures    var k := ArrayToBitSequence(old(key), 32*key.Length);
            var m := ArrayToBitSequence(old(data), len);
            |m| < power2(64) - 8*64 &&
            hash[..] == HMAC(k, m);
{
    var inner_hash := HMAC_inner_hash(key, data, len);
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);
    lemma_2toX();
    assert inner_hash[..] == SHA256(SeqXor(ArrayToBitSequence(key, key.Length*32), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len));
    ghost var old_inner_hash := inner_hash[..];

    var input := HMAC_outer_input(key, inner_hash); 
    assert WordSeqToBits(input[..]) == SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]) + WordSeqToBits(input[16+8..]);
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
        (SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]) + WordSeqToBits(input[16+8..]))[..bit_len];
        (SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]))[..bit_len];
        SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(inner_hash[..]);
        SeqXor(WordSeqToBits(key[..]), Opad(|key[..]|*32)) + WordSeqToBits(SHA256(SeqXor(ArrayToBitSequence(key, key.Length*32), Ipad(|key[..]|*32)) + ArrayToBitSequence(data, len)));
    }

    hash := SHA256impl(input, bit_len);
    assert hash[..] == SHA256(old_input);
    assert old_inner_hash == inner_hash[..];
    assert key[..]  == old( key[..]);
    assert data[..] == old(data[..]);

    ghost var key_bits := key.Length*32;
    ghost var k := ArrayToBitSequence(key, key_bits);
    ghost var m := ArrayToBitSequence(data, len);
    calc {
        hash[..];
        SHA256(old_input);
        SHA256(SeqXor(WordSeqToBits(key[..]), 
                      Opad(|key[..]|*32)) 
               + WordSeqToBits(SHA256(SeqXor(ArrayToBitSequence(key, key.Length*32), 
                                               Ipad(|key[..]|*32)) 
                                     + ArrayToBitSequence(data, len))));
        { lemma_IntSeq_ConvertMessage(key, key_bits); 
          assert forall i :: 0 <= i < key_bits ==> WordSeqToBits(key[..])[i] == ArrayToBitSequence(key, key_bits)[i];
          assert ArrayToBitSequence(key, key_bits) == WordSeqToBits(key[..]);
        }                                      
        SHA256(SeqXor(k, 
                      Opad(|k|)) 
               + WordSeqToBits(SHA256(SeqXor(k, 
                                               Ipad(|k|)) 
                                     + m)));
        HMAC(k, m);
    }
}


// FIPS says:
// SHA256(“abc”) = BA7816BF 8F01CFEA 414140DE 5DAE2223 B00361A3 96177A9C B410FF61 F20015AD
// http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA256.pdf
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
    reveal_NumPaddingZeroes();
    reveal_PaddedLength();
    var hash := SHA256impl(data, 24);

    i := 0;
    while (i < hash.Length)
    {
        print hash[i];
        i := i + 1;
    }
}

// FIPS says:
// SHA256(“"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq") =
// 248D6A61 D20638B8 E5C02693 0C3E6039 A33CE459 64FF2167 F6ECEDD4 19DB06C1
// http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA256.pdf
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
    var hash := SHA256impl(data, 448);
    
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
