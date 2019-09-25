include "../../../../Trusted/Spec/Assembly.dfy"
include "../../../../Trusted/Spec/Libraries/Crypto/RSA/RSASpec.dfy"
include "../../BigNum/BigNum.dfy"
include "ByteSequences.dfy"

//////////////////////////////////////////////////////////////////////////////
// octet-string to octet-string encoding

method PadMessage(msg:seq<int>, keysize_octets:nat, pad_mode:PadMode)
	returns (padded_msg:seq<int>)
	requires ByteSeq(msg);
	requires |msg| <= keysize_octets - 11;
	ensures ByteSeq(padded_msg);
	ensures |padded_msg| == keysize_octets;
	ensures PKCS15_PaddingRelation(padded_msg, msg, pad_mode);
{
	var ps_len:int := keysize_octets - |msg| - 3;
	assert ps_len>=8;
	var ps := MakePaddingString(ps_len, pad_mode);
	padded_msg := [0, BlockType(pad_mode)] + ps + [0] + msg;
	assert |padded_msg| == keysize_octets;

	var i := ps_len + 3;

		assert i <= |padded_msg|;
		assert 2 <= |padded_msg|;
		assert padded_msg[0]==0;
		assert padded_msg[1]==2;
		assert forall j :: 2 <= j < i-1 ==> padded_msg[j]!=0;
		assert padded_msg[i-1]==0;
	assert PaddedMessageStartIndex(padded_msg, i, pad_mode);

	assert i >= 11;
	assert padded_msg[i..] == msg;

	assert PKCS15_PaddingRelationAt(padded_msg, i, msg, pad_mode);
}

method RandomNonzeroOctet() returns (octet:int)
	ensures IsByte(octet);
	ensures 0!=octet;
{
	var rand_word := Random32();
	octet := rand_word % 255;
	if (octet==0)
	{
		octet:=42;	// a popular value.
	}
	else
	{
	}
}

method MakePaddingString(ps_len:nat, pad_mode:PadMode) returns (os:seq<int>)
	requires 8 <= ps_len;	// just because. Not really required.
	ensures ByteSeq(os);
	ensures |os| == ps_len;
	ensures forall octet :: octet in os ==> octet != 0;
{
	os := [];
	while (|os|<ps_len)
		invariant |os| <= ps_len;
		invariant forall octet :: octet in os ==> IsByte(octet);
		invariant forall octet :: octet in os ==> octet != 0;
	{
		var next_octet:int;
		if (pad_mode == PadModeSign())
		{
			next_octet := 0xff;
		}
		else if (pad_mode == PadModeEncrypt())
		{
			next_octet := RandomNonzeroOctet();
		}
		else
		{
			assert false;
		}
		os := os + [next_octet];
	}
}

method UnpadMessage(padded_msg:seq<int>, pad_mode:PadMode) returns (msg:seq<int>)
	requires ByteSeq(padded_msg);
	requires exists m :: ByteSeq(m) && PKCS15_PaddingRelation(padded_msg, m, pad_mode);
	ensures ByteSeq(msg);
	ensures PKCS15_PaddingRelation(padded_msg, msg, pad_mode);
{
	ghost var gm :| ByteSeq(gm) && PKCS15_PaddingRelation(padded_msg, gm, pad_mode);
	ghost var pl:nat :| PKCS15_PaddingRelationAt(padded_msg, pl, gm, pad_mode);
	assert pl <= |padded_msg|;

	assert padded_msg[0]==0;
	assert padded_msg[1]==BlockType(pad_mode);

	var pad_idx:int := 2;
	while (padded_msg[pad_idx]!=0)
		decreases pl - pad_idx;
		invariant forall j::2<=j<pad_idx && j <pl ==> padded_msg[j]!=0;
		invariant pad_idx < pl;
	{
		pad_idx := pad_idx + 1;
		if (pad_idx >= pl)
		{
			assert padded_msg[pl-1] == 0;
			assert false;	// violates invariant
		}
	}
	pad_idx := pad_idx + 1;	// skip the end-of-pad zero
	msg := padded_msg[pad_idx..];
}

method UnpadMessageOrFail(padded_msg:seq<int>, pad_mode:PadMode) returns (success:bool, msg:seq<int>)
	requires ByteSeq(padded_msg);
	ensures ByteSeq(msg);
	ensures (success <==> exists m :: (ByteSeq(m) && PKCS15_PaddingRelation(padded_msg, m, pad_mode)));
	ensures (success ==> PKCS15_PaddingRelation(padded_msg, msg, pad_mode));
{
	msg := [];

	if (|padded_msg| < 11)
	{
		success := false;
		return;
	}

	// must start with zero, BlockType
	if (padded_msg[0]!=0)
	{
		success := false;
		return;
	}
	if (padded_msg[1]!=BlockType(pad_mode))
	{
		success := false;
		return;
	}

	var pad_idx:int := 2;
	while (pad_idx < |padded_msg| && padded_msg[pad_idx]!=0)
		invariant forall j::2<=j<pad_idx && j<|padded_msg|==> padded_msg[j]!=0;
	{
		pad_idx := pad_idx + 1;
	}

	if (pad_idx >= |padded_msg|)
	{
		success := false;
		return;

	}

	assert padded_msg[pad_idx] == 0;
	pad_idx := pad_idx + 1;	// skip the end-of-pad zero

	if (pad_idx < 11)
	{
		success := false;
		return;
	}

	success := true;
	msg := padded_msg[pad_idx..];

	assert PKCS15_PaddingRelationAt(padded_msg, pad_idx, msg, pad_mode);
	assert PKCS15_PaddingRelation(padded_msg, msg, pad_mode);
}

//////////////////////////////////////////////////////////////////////////////
// encoding an octet string to integers

function method LEBytesToWord(os:seq<int>) : int
	requires ByteSeq(os);
	requires |os|==4;
	ensures Word32(LEBytesToWord(os));
{
	lemma_2to32();
	os[0] + 256*os[1] + 65536*os[2] + 16777216*os[3]
}

lemma lemma_LEBytesToWord(os:seq<int>)
	requires ByteSeq(os);
	requires |os|==4;
	ensures LittleEndianIntegerValue(os) == LEBytesToWord(os);
{
	calc {
		LittleEndianIntegerValue(os);
		LittleEndianIntegerValue(os[1..])*256 + os[0];
		(LittleEndianIntegerValue(os[1..][1..])*256 + os[1..][0])*256 + os[0];
			{
				assert os[1..][1..] == os[2..];
				assert os[1..][0] == os[1];
			}
		(LittleEndianIntegerValue(os[2..])*256 + os[1])*256 + os[0];
		((LittleEndianIntegerValue(os[2..][1..])*256 + os[2..][0])*256 + os[1])*256 + os[0];
		((LittleEndianIntegerValue(os[3..])*256 + os[2])*256 + os[1])*256 + os[0];
		(((LittleEndianIntegerValue(os[3..][1..])*256 + os[3..][0])*256 + os[2])*256 + os[1])*256 + os[0];
		(((LittleEndianIntegerValue(os[4..])*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
		(((LittleEndianIntegerValue([])*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
		(((0*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
		((os[3]*256 + os[2])*256 + os[1])*256 + os[0];
		(os[3]*256*256 + os[2]*256 + os[1])*256 + os[0];
		os[3]*256*256*256 + os[2]*256*256 + os[1]*256 + os[0];
		LEBytesToWord(os);
	}
}

method OctetsToWords(os:seq<int>) returns (ws:seq<int>)
	requires ByteSeq(os);
	requires |os|%4==0;
	requires |os|>0;
	requires os[|os|-2] != 0;
	ensures WordSeq(ws);
	ensures LittleEndianIntegerValue(os) == V(ws);
	ensures |ws|>0;
	ensures ws[|ws|-1] != 0;
{
	var end_ptr:int := |os|;
	ws := [];

	calc {
		LittleEndianIntegerValue(os[end_ptr..]);
		LittleEndianIntegerValue([]);
		0;
			{ reveal_V(); }
		V([]);
		V(ws);
	}

	while (end_ptr > 0)
		invariant WordSeq(ws);
		invariant (end_ptr==|os|) == (ws==[]);
		invariant end_ptr >= 0;
		invariant end_ptr % 4 == 0;
		invariant LittleEndianIntegerValue(os[end_ptr..])==V(ws);
		invariant end_ptr==0 ==> |ws|>0;
		invariant |ws|>0 ==> ws[|ws|-1] != 0;
	{
		var sub_os := os[end_ptr-4..end_ptr];
		var word := LEBytesToWord(sub_os);
		ghost var old_ws := ws;
		ws := [word] + ws;

		calc {
			V(ws);
				{ reveal_V(); }
			Width()*V(old_ws) + word;
			Width()*LittleEndianIntegerValue(os[end_ptr..]) + word;
				{
					lemma_2to32();
					lemma_mul_is_mul_boogie(4294967296,LittleEndianIntegerValue(os[end_ptr..]));
				}
			4294967296*LittleEndianIntegerValue(os[end_ptr..]) + word;
			LittleEndianIntegerValue(os[end_ptr..])*256*256*256*256 + os[end_ptr-1]*256*256*256 + os[end_ptr-2]*256*256 + os[end_ptr-3]*256 + os[end_ptr-4];
			(((LittleEndianIntegerValue(os[end_ptr-0..])*256 + os[end_ptr-1])*256 + os[end_ptr-2])*256 + os[end_ptr-3])*256 + os[end_ptr-4];
				{ assert os[end_ptr-1..] == [os[end_ptr-1]] + os[end_ptr-0..]; }
			 ((LittleEndianIntegerValue(os[end_ptr-1..])*256 + os[end_ptr-2])*256 + os[end_ptr-3])*256 + os[end_ptr-4];
				{ assert os[end_ptr-2..] == [os[end_ptr-2]] + os[end_ptr-1..]; }
			  (LittleEndianIntegerValue(os[end_ptr-2..])*256 + os[end_ptr-3])*256 + os[end_ptr-4];
				{ assert os[end_ptr-3..] == [os[end_ptr-3]] + os[end_ptr-2..]; }
			   LittleEndianIntegerValue(os[end_ptr-3..])*256 + os[end_ptr-4];
				{ assert os[end_ptr-4..] == [os[end_ptr-4]] + os[end_ptr-3..]; }
			LittleEndianIntegerValue(os[end_ptr-4..]);
		}

		end_ptr := end_ptr - 4;
	}

	assert os[end_ptr..] == os;
}

method BESeqToInteger(be_padded_msg:seq<int>) returns (M:BigNat)
	requires ByteSeq(be_padded_msg);
	requires |be_padded_msg|%4==0;
	requires |be_padded_msg|>0;
	requires be_padded_msg[1] != 0;
	ensures WellformedBigNat(M);
	ensures I(M) == BigEndianIntegerValue(be_padded_msg);
{
	var little_endian_be_padded_msg := ReverseOctetString(be_padded_msg);

	var little_endian_word_string := OctetsToWords(little_endian_be_padded_msg);
	M := BigNat_ctor(little_endian_word_string);

	calc {
		BigEndianIntegerValue(be_padded_msg);
			{ lemma_endian_reversal(be_padded_msg); }
		LittleEndianIntegerValue(little_endian_be_padded_msg);
		V(little_endian_word_string);
			{ lemma_V_I(M); }
		I(M);
	}
}

method MessageToInteger(msg:seq<int>, keysize_octets:nat, pad_mode:PadMode) returns (M:BigNat, ghost pm:seq<int>)
	requires ByteSeq(msg);
	requires keysize_octets % 4 == 0;
	requires |msg| <= keysize_octets - 11;
	ensures WellformedBigNat(M);
	ensures ByteSeq(pm);
	ensures PKCS15_PaddingRelation(pm, msg, pad_mode);
	ensures BigEndianIntegerValue(pm)==I(M);
	ensures 7<8;
	ensures 0 < I(M) < power2(8*(keysize_octets-1));
{
	var be_padded_msg:seq<int> := PadMessage(msg, keysize_octets, pad_mode);
	pm := be_padded_msg;

	M := BESeqToInteger(be_padded_msg);

	calc {
		BigEndianIntegerValue(be_padded_msg);
			{ lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, be_padded_msg[1..]); }
		BigEndianIntegerValue(be_padded_msg[1..]);
		<	{ lemma_BigEndianIntegerValue_bound(be_padded_msg[1..]); }
		power2(8*|be_padded_msg[1..]|);
		power2(8*(|be_padded_msg|-1));
		power2(8*(keysize_octets-1));
	}

	calc {
		BigEndianIntegerValue(be_padded_msg);
			{ lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, be_padded_msg[1..]); }
		BigEndianIntegerValue(be_padded_msg[1..]);
		>=	{ lemma_BigEndianIntegerValue_bound(be_padded_msg[1..]); }
		power2(8*(|be_padded_msg[1..]|-1))*be_padded_msg[1..][0];
		mul(power2(8*(|be_padded_msg[1..]|-1)),2);
		mul(power2(8*(|be_padded_msg|-2)),2);
			{ lemma_mul_is_commutative_forall(); }
		mul(2,power2(8*(|be_padded_msg|-2)));
		>=	{
			lemma_mul_strictly_increases(2,power2(8*(|be_padded_msg|-2)));
			}
		power2(8*(|be_padded_msg|-2));
		power2(8*|be_padded_msg|-16);
		>=	{
				assert 11 <= keysize_octets;
				calc {
					8*(|be_padded_msg|-2);
					8*|be_padded_msg| - 16;
					8*keysize_octets - 16;
					>=
					8*11 - 16;
					88 - 16;
					72;
					> 0;
				}
				lemma_power2_increases(0, 8*(|be_padded_msg|-2));
			}
		power2(0);
			{ lemma_power2_0_is_1(); }
		1;
		> 0;
	}
}

method LEWordToBytes(word:int) returns (os:seq<int>)
	requires Word32(word);
	ensures ByteSeq(os);
	ensures |os|==4;
	ensures LEBytesToWord(os) == word;
{
	// TODO Shifts and masks would be nice here.
	var r0 := word % 256;
	var q0 := word / 256;
	var r1 := q0 % 256;
	var q1 := q0 / 256;
	var r2 := q1 % 256;
	var q2 := q1 / 256;
	os := [ r0, r1, r2, q2 ];

	lemma_2to32();

	calc {
		LEBytesToWord(os);
		os[0] + 256*os[1] + 65536*os[2] + 16777216*os[3];
		r0 + 256*r1 + 65536*r2 + 16777216*q2;
		r0 + 256*(r1 + 256*r2 + 65536*q2);
		r0 + 256*(r1 + 256*(r2 + 256*q2));
			{
				lemma_mul_is_mul_boogie(256,q2);
				lemma_mul_is_mul_boogie(256,r2 + 256*q2);
				lemma_mul_is_mul_boogie(256,r1 + 256*(r2 + 256*q2));
			}
		r0 + mul(256,(r1 + mul(256,(r2 + mul(256,q2)))));
			{
				lemma_fundamental_div_mod(q1, 256);
				assert q1 == mul(256, div(q1, 256)) + mod(q1,256);
				lemma_div_is_div_boogie_for_256_which_is_also_a_number(q1);
				lemma_mod_is_mod_boogie_for_256_which_is_also_a_number(q1);
				assert div(q1,256) == q1/256 == q2;
				assert q1 == mul(256, q2) + r2;
			}
		r0 + mul(256,(r1 + mul(256,q1)));
			{
				lemma_fundamental_div_mod(q0, 256);
				assert q0 == mul(256, div(q0, 256)) + mod(q0,256);
				lemma_div_is_div_boogie_for_256_which_is_also_a_number(q0);
				lemma_mod_is_mod_boogie_for_256_which_is_also_a_number(q0);
				assert q0 == mul(256, q1) + r1;
			}
		r0 + mul(256,q0);
			{
				lemma_fundamental_div_mod(word, 256);
				assert word == mul(256, div(word, 256)) + mod(word,256);
				lemma_div_is_div_boogie_for_256_which_is_also_a_number(word);
				lemma_mod_is_mod_boogie_for_256_which_is_also_a_number(word);
				assert word == mul(256, q0) + r0;
			}
		word;
	}
}

lemma lemma_LittleEndianIntegerValue_chomps_word(os:seq<int>)
	requires ByteSeq(os);
	requires |os|>=4;
	ensures LittleEndianIntegerValue(os)
		== LEBytesToWord(os[0..4]) + Width()*LittleEndianIntegerValue(os[4..]);
{
	calc {
		LittleEndianIntegerValue(os);
		LittleEndianIntegerValue(os[1..])*256 + os[0];
		(LittleEndianIntegerValue(os[1..][1..])*256 + os[1..][0])*256 + os[0];
			{
				assert os[1..][1..] == os[2..];
				assert os[1..][0] == os[1];
			}
		(LittleEndianIntegerValue(os[2..])*256 + os[1])*256 + os[0];
		((LittleEndianIntegerValue(os[2..][1..])*256 + os[2..][0])*256 + os[1])*256 + os[0];
			{
				assert os[2..][1..] == os[3..];
				assert os[2..][0] == os[2];
			}
		((LittleEndianIntegerValue(os[3..])*256 + os[2])*256 + os[1])*256 + os[0];
		(((LittleEndianIntegerValue(os[3..][1..])*256 + os[3..][0])*256 + os[2])*256 + os[1])*256 + os[0];
			{
				assert os[3..][1..] == os[4..];
				assert os[3..][0] == os[3];
			}
		(((LittleEndianIntegerValue(os[4..])*256 + os[3])*256 + os[2])*256 + os[1])*256 + os[0];
		((LittleEndianIntegerValue(os[4..])*256*256 + os[3]*256 + os[2])*256 + os[1])*256 + os[0];
		(LittleEndianIntegerValue(os[4..])*256*256*256 + os[3]*256*256 + os[2]*256 + os[1])*256 + os[0];
		LittleEndianIntegerValue(os[4..])*256*256*256*256 + os[3]*256*256*256 + os[2]*256*256 + os[1]*256 + os[0];
			{
				lemma_2to32();
				lemma_mul_is_mul_boogie(LittleEndianIntegerValue(os[4..]), Width());
			}
		LittleEndianIntegerValue(os[4..])*Width() + os[3]*256*256*256 + os[2]*256*256 + os[1]*256 + os[0];
		LittleEndianIntegerValue(os[4..])*Width() + os[0] + 256*os[1] + 65536*os[2] + 16777216*os[3];
			{ lemma_mul_is_commutative(LittleEndianIntegerValue(os[4..]),Width()); }
		LEBytesToWord(os[0..4]) + Width()*LittleEndianIntegerValue(os[4..]);
	}
}

method WordsToOctets(ws:seq<int>) returns (os:seq<int>)
	requires WordSeq(ws);
	ensures ByteSeq(os);
	ensures LittleEndianIntegerValue(os) == V(ws);
{
	os := [];
	var end_ptr := |ws|;

	calc {
		LittleEndianIntegerValue(os);
		0;
			{ reveal_V(); }
		V([]);
			{ assert ws[end_ptr..] == []; }
		V(ws[end_ptr..]);
	}

	while (end_ptr > 0)
		invariant end_ptr >= 0;
		invariant ByteSeq(os);
		invariant LittleEndianIntegerValue(os) == V(ws[end_ptr..]);
	{
		var word_os := LEWordToBytes(ws[end_ptr-1]);
		ghost var old_os := os;
		os := word_os + os;

		calc {
			LittleEndianIntegerValue(os);
				{ lemma_LittleEndianIntegerValue_chomps_word(os); }
			LEBytesToWord(word_os) + Width()*LittleEndianIntegerValue(old_os);
			ws[end_ptr-1] + Width()*V(ws[end_ptr..]);
				{ reveal_V(); }
			V([ws[end_ptr-1]] + ws[end_ptr..]);
				{ assert [ws[end_ptr-1]] + ws[end_ptr..] == ws[end_ptr-1..]; }
			V(ws[end_ptr-1..]);
		}

		end_ptr := end_ptr - 1;
	}
	assert ws==ws[0..];
}

predicate CanDecodeInteger(M:BigNat, pad_mode:PadMode)
	requires WellformedBigNat(M);
{
	exists pm:seq<int>, m:seq<int> ::
		ByteSeq(pm)
		&& ByteSeq(m)
		&& PKCS15_PaddingRelation(pm, m, pad_mode)
		&& BigEndianIntegerValue(pm)==I(M)
}

method IntegerToBESeq(M:BigNat) returns (be_padded_msg:seq<int>)
	requires WellformedBigNat(M);
	ensures ByteSeq(be_padded_msg);
	ensures |be_padded_msg| > 0;
	ensures be_padded_msg[0] == 0;
	ensures (|be_padded_msg| > 1) ==> be_padded_msg[1] != 0;
	ensures I(M) == BigEndianIntegerValue(be_padded_msg);
	ensures |be_padded_msg| > 2 ==> power2(8*(|be_padded_msg|-2)) <= BigEndianIntegerValue(be_padded_msg);
{
	var le_padded_msg := WordsToOctets(M.words);

	var wordy_be_padded_msg := ReverseOctetString(le_padded_msg);
		// approximately right, but may have as many as 3 most-significant zeros

	var stripped_be_padded_msg := StripLeadingZeros(wordy_be_padded_msg );
		// now no zeros.

	be_padded_msg := [0] + stripped_be_padded_msg;
		// juuust right.

	assert |stripped_be_padded_msg|>0 ==> stripped_be_padded_msg[0]!=0;
	assert |be_padded_msg|>1 ==> be_padded_msg[1]!=0;

	calc {
		BigEndianIntegerValue(be_padded_msg);
			{ lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, stripped_be_padded_msg); }
		BigEndianIntegerValue(stripped_be_padded_msg);
			{ lemma_BigEndianIntegerValue_zero_prefix(wordy_be_padded_msg, stripped_be_padded_msg); }
		BigEndianIntegerValue(wordy_be_padded_msg);
			{ lemma_endian_reversal(wordy_be_padded_msg); }
		LittleEndianIntegerValue(Reverse(wordy_be_padded_msg));
			{ lemma_Reverse_symmetry(wordy_be_padded_msg, le_padded_msg); }
		LittleEndianIntegerValue(le_padded_msg);
		V(M.words);
			{ lemma_V_I(M); }
		I(M);
	}

	if (|be_padded_msg| > 2)
	{
		assert |stripped_be_padded_msg| > 0;
		calc {
			power2(8*(|be_padded_msg|-2));
			power2(8*(|stripped_be_padded_msg|-1));
			power2(8*(|stripped_be_padded_msg|-1))*1;
				{ lemma_mul_is_mul_boogie(power2(8*(|stripped_be_padded_msg|-1)),1); }
			mul(power2(8*(|stripped_be_padded_msg|-1)),1);
			<=	{ lemma_mul_left_inequality(power2(8*(|stripped_be_padded_msg|-1)), 1, stripped_be_padded_msg[0]); }
			power2(8*(|stripped_be_padded_msg|-1))*stripped_be_padded_msg[0];
			<=	{ lemma_BigEndianIntegerValue_bound(stripped_be_padded_msg); }
			BigEndianIntegerValue(stripped_be_padded_msg);
				{ lemma_BigEndianIntegerValue_zero_prefix(be_padded_msg, stripped_be_padded_msg); }
			BigEndianIntegerValue(be_padded_msg);
		}
	}
}

method IntegerToMessage(M:BigNat, pad_mode:PadMode) returns (success:bool, msg:seq<int>, ghost be_padded_msg:seq<int>)
	requires WellformedBigNat(M);
	ensures ByteSeq(msg);
	ensures success <==> CanDecodeInteger(M, pad_mode);
	ensures success ==>
		ByteSeq(be_padded_msg)
		&& PKCS15_PaddingRelation(be_padded_msg, msg, pad_mode)
		&& BigEndianIntegerValue(be_padded_msg)==I(M);
{
	var be_padded_msg_real := IntegerToBESeq(M);
	be_padded_msg := be_padded_msg_real;

	success,msg := UnpadMessageOrFail(be_padded_msg_real, pad_mode);

	if (!success)
	{
		forall pm:seq<int>, m:seq<int>
			ensures !(ByteSeq(pm)
				&& ByteSeq(m)
				&& PKCS15_PaddingRelation(pm, m, pad_mode)
				&& BigEndianIntegerValue(pm)==I(M));
		{
			if (ByteSeq(pm)
				&& ByteSeq(m)
				&& BigEndianIntegerValue(pm)==I(M))
			{
				lemma_BigEndianIntegerValue_zero_prefix_converse(pm, be_padded_msg);
				if (pm == be_padded_msg)
				{
					assert !(exists m :: (ByteSeq(m) && PKCS15_PaddingRelation(be_padded_msg, m, pad_mode)));
					assert !PKCS15_PaddingRelation(pm, m, pad_mode);
				}
				else if (ZeroPrefix(pm, be_padded_msg))
				{
					assert |pm| >= |be_padded_msg|;
					assert |pm| > |be_padded_msg|;
					if (1 < |pm|-|be_padded_msg|)
					{
						assert pm[1]==0;
					}
					else if (1 == |pm|-|be_padded_msg|)
					{
						calc {
							pm[1];
							pm[ 1 .. ][0];
							be_padded_msg[0];
							0;
						}
					}
					else
					{
						assert 0 == |pm|-|be_padded_msg|;
						assert pm == be_padded_msg;
						assert false;
					}
					assert !PKCS15_PaddingRelation(pm, m, pad_mode);
				}
				else
				{
					assert ZeroPrefix(be_padded_msg, pm);
					if (0 == |be_padded_msg|-|pm|)
					{
						assert pm == be_padded_msg;
						assert false;
					}
					else if (1 < |be_padded_msg|-|pm|)
					{
						assert be_padded_msg[1] == 0;
						assert false;
					}
					else if (|pm| < 1)
					{
						assert !PKCS15_PaddingRelation(pm, m, pad_mode);
					}
					else if (|be_padded_msg| < 2)
					{
						assert |pm| <= |be_padded_msg|;
						assert !PKCS15_PaddingRelation(pm, m, pad_mode);
					}
					else
					{
						assert 1 == |be_padded_msg|-|pm|;
						calc {
							be_padded_msg[1];
							be_padded_msg[ 1.. ][0];
							pm[0];
						}
						assert pm[0]!=0;
						assert !PKCS15_PaddingRelation(pm, m, pad_mode);
					}
				}
			}
		}
	}
	else
	{
		assert ByteSeq(be_padded_msg);
		assert PKCS15_PaddingRelation(be_padded_msg, msg, pad_mode);
	}
}

method BEWordToBytes(word:int) returns (os:seq<int>)
	requires Word32(word);
	ensures ByteSeq(os);
	ensures |os|==4;
	ensures BigEndianIntegerValue(os) == word;
{
	var leseq := LEWordToBytes(word);
	os := ReverseOctetString(leseq);

	calc {
		BigEndianIntegerValue(os);
			{ lemma_endian_reversal(os); }
		LittleEndianIntegerValue(Reverse(os));
			{ lemma_Reverse_symmetry(os, leseq); }
		LittleEndianIntegerValue(leseq);
			{ lemma_LEBytesToWord(leseq); }
		LEBytesToWord(leseq);
		word;
	}
}
