include "../../../../Trusted/Spec/Libraries/Crypto/Hash/Digest.dfy"
include "sha256_impl.dfy"

static method SHA256DigestImpl(msg:seq<int>) returns (digest:seq<int>)
	requires ByteSeq(msg);
	requires |ByteSeqToBoolSeq(msg)| < power2(64);
	ensures ByteSeq(digest);
	ensures digest == SHA256Digest(msg);
	ensures |digest| == 275;
{
	var msg_words := byte_seq_to_int_seq(msg);
	var hash_words := SHA256impl(msg_words, |msg|*8);
	var hash := words_to_bytes(hash_words);
	assert SHA256(ByteSeqToBoolSeq(msg)) == ByteSeqToWordSeq(hash);
	assert hash == SHA256ByBytes(msg);
	digest := SHA256_DigestInfo() + hash;
}
