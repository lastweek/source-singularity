include "../Hash/sha256_spec.dfy"

static function SHA256ByBytes(bs:seq<int>) : seq<int>
	requires ByteSeq(bs);
	requires |ByteSeqToBoolSeq(bs)| < power2(64);	// yuck!
	ensures ByteSeq(SHA256ByBytes(bs));
{
	WordSeqToByteSeq(SHA256(ByteSeqToBoolSeq(bs)))
}

static function method SHA256_DigestInfo() : seq<int>
{
	[ 0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01,
	  0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20 ]
}

static function SHA256Digest(msg:seq<int>) : seq<int>
	requires ByteSeq(msg);
	requires |ByteSeqToBoolSeq(msg)| < power2(64);	// yuck!
{
	SHA256_DigestInfo() + SHA256ByBytes(msg)
}
