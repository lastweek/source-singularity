include "../../../Assembly.dfy"
include "BigEndianByteStrings.dfy"

predicate rfc4251_word32_encoding(msg:seq<int>, w:int)
	requires ByteSeq(msg);
{
	|msg|==4
	&& Word32(w)
	&& BigEndianIntegerValue(msg)==w
}

predicate rfc4251_string_encoding(msg:seq<int>, s:seq<int>)
	requires ByteSeq(msg);
	requires ByteSeq(s);
{
	|msg| >= 4
	&& rfc4251_word32_encoding(msg[0..4], |s|)
	&& msg[4..] == s
}

predicate rfc4251_wellformed_positive_seq(enc_v:seq<int>)
	requires ByteSeq(enc_v);
{
	// RFC4251 allows for encoding negative numbers two's-complement,
	// and thus is particular about how we encode positive numbers
	// that use the top bit.
	|enc_v|==0
	|| (enc_v[0] < 128
		&& (enc_v[0]>0
			|| (|enc_v|>1 && enc_v[1] >= 128)
			)
		)
}

predicate rfc4251_mpint_encoding(msg:seq<int>, v:nat)
	requires ByteSeq(msg);
{
	|msg| >= 4
	&& exists enc_v:seq<int> ::
		ByteSeq(enc_v)
		&& rfc4251_word32_encoding(msg[0..4], |enc_v|)
		&& BigEndianIntegerValue(enc_v) == v
		&& rfc4251_wellformed_positive_seq(enc_v)
}

function method STR_SSH_RSA() : seq<int>
	//ensures ByteSeq(STR_SSH_RSA())
{
	// Hey guys, Dafny needs string literals! :v)
	[115, 115, 104, 45, 114, 115, 97]
}

predicate rfc4251_sshrsa_encoding(msg:seq<int>, e:nat, n:nat)
	requires ByteSeq(msg);
{
	exists enc_s:seq<int>, enc_e:seq<int>, enc_n:seq<int> ::
		ByteSeq(enc_s)
		&& ByteSeq(enc_e)
		&& ByteSeq(enc_n)
		&& rfc4251_string_encoding(enc_s, STR_SSH_RSA())
		&& rfc4251_mpint_encoding(enc_e, e)
		&& rfc4251_mpint_encoding(enc_n, n)
		&& msg == enc_s + enc_e + enc_n
}
