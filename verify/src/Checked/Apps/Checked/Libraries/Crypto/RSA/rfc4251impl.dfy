include "../../BigNum/BigNum.dfy"
include "../../../../Trusted/Spec/Libraries/Crypto/RSA/rfc4251.dfy"
include "../../../../Trusted/Spec/Libraries/Crypto/RSA/RSASpec.dfy"
	// BigEndianIntegerValue -- factor out?
include "BlockEncoding.dfy"

method rfc4251_encode_word32(w:int) returns (msg:seq<int>)
	requires Word32(w);	// redundant; falls out of definition.
	ensures ByteSeq(msg);
	ensures rfc4251_word32_encoding(msg, w);
{
	msg := BEWordToBytes(w);
}

method rfc4251_encode_string(s:seq<int>) returns (msg:seq<int>)
	requires ByteSeq(s);
	requires Word32(|s|);
	ensures ByteSeq(msg);
	ensures rfc4251_string_encoding(msg, s);
{
	var l := rfc4251_encode_word32(|s|);
	msg := l + s;

	assert msg[0..4] == l;
}

method rfc4251_encode_mpint(V:BigNat) returns (msg:seq<int>)
	requires ModestBigNatValue(V);
	ensures ByteSeq(msg);
	ensures rfc4251_mpint_encoding(msg, I(V));
{
	var v_bits := IntegerToBESeq(V);

	lemma_2to32();

	assert I(V) < power2(power2(31));
	if (|v_bits|>2)
	{
		assert power2(8*(|v_bits|-2)) <= BigEndianIntegerValue(v_bits);

		calc ==> {
			power2(8*(|v_bits|-2)) <= power2(power2(31));
				{ lemma_power2_increases_converse(8*(|v_bits|-2), power2(31)); }
			8*(|v_bits|-2) <= power2(31);
				{ lemma_power2_adds(3,28); }
			8*(|v_bits|-2) <= power2(3)*power2(28);
				{ lemma_2toX(); reveal_power2(); }
			8*(|v_bits|-2) <= mul(8,power2(28));
				{ lemma_mul_is_mul_boogie(8, power2(28)); }
			8*(|v_bits|-2) <= 8*power2(28);
				{ lemma_mul_inequality_forall(); }
			|v_bits|-2 <= power2(28);
			|v_bits| <= power2(28)+2;
				{ lemma_2toX(); reveal_power2(); }
			|v_bits| < power2(28)+power2(28);
			|v_bits| < 2*power2(28);
				{ lemma_mul_is_mul_boogie(2, power2(28)); }
			|v_bits| < mul(2,power2(28));
				{ lemma_power2_1_is_2(); }
			|v_bits| < mul(power2(1),power2(28));
				{ lemma_power2_adds(1,28); }
			|v_bits| < power2(29);
				{ lemma_power2_strictly_increases(29,32); }
			|v_bits| < Width();
		}
		assert Word32(|v_bits|);
	}
	else
	{
		assert |v_bits| <= 2;
		assert Word32(|v_bits|);
	}
	assert Word32(|v_bits|);
			
	if (|v_bits|>=2 && v_bits[1]<128)
	{
		ghost var old_v_bits := v_bits;
		v_bits := v_bits[1..];
		lemma_BigEndianIntegerValue_zero_prefix(old_v_bits, v_bits);
	}
	else if (|v_bits|==1)
	{
		ghost var old_v_bits := v_bits;
		assert v_bits[0]==0;
		v_bits := [];
	}

	assert Word32(|v_bits|);
	var len_bits := rfc4251_encode_word32(|v_bits|);
	msg := len_bits + v_bits;

	assert msg[0..4] == len_bits;
}

method rfc4251_encode_sshrsa(E:BigNat, N:BigNat) returns (msg:seq<int>)
	requires ModestBigNatValue(E);
	requires ModestBigNatValue(N);
	ensures ByteSeq(msg);
	ensures rfc4251_sshrsa_encoding(msg, I(E), I(N));
{
	lemma_2to32();
	assert |STR_SSH_RSA()| < power2(32);

	var enc_s := rfc4251_encode_string(STR_SSH_RSA());
	var enc_e := rfc4251_encode_mpint(E);
	var enc_n := rfc4251_encode_mpint(N);

	msg := enc_s + enc_e + enc_n;

		assert ByteSeq(enc_s);
		assert ByteSeq(enc_e);
		assert ByteSeq(enc_n);
		assert ByteSeq(msg);
		assert rfc4251_string_encoding(enc_s, STR_SSH_RSA());
		assert rfc4251_mpint_encoding(enc_e, I(E));
		assert rfc4251_mpint_encoding(enc_n, I(N));
		assert msg == enc_s + enc_e + enc_n;
	assert rfc4251_sshrsa_encoding(msg, I(E), I(N));
}
