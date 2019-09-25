include "../Hash/Digest.dfy"
include "../../Math/power.dfy"
include "../../../Assembly.dfy"
include "BigEndianByteStrings.dfy"

datatype PadMode = PadModeEncrypt() | PadModeSign();

function method BlockType(pad_mode:PadMode) : int
{
	if (pad_mode==PadModeSign()) then 1 else 2
}

predicate PaddedMessageStartIndex(padded_msg:seq<int>, i:nat, pad_mode:PadMode)
	requires ByteSeq(padded_msg);
{
	0 < i <= |padded_msg|
	&& 2 <= |padded_msg|
	&& padded_msg[0]==0
	&& padded_msg[1]==BlockType(pad_mode)
	&& (forall j :: 2 <= j < i-1 ==> padded_msg[j]!=0)
	&& padded_msg[i-1]==0
}

predicate PKCS15_PaddingRelationAt(padded_msg:seq<int>, i:nat, msg:seq<int>, pad_mode:PadMode)
	requires ByteSeq(padded_msg);
	requires ByteSeq(msg);
	// i points *after* all the padding, at the first byte of real message
{
	PaddedMessageStartIndex(padded_msg, i, pad_mode)
	&& i >= 11			// 8 bytes of padding required
	&& padded_msg[i..] == msg
}

predicate PKCS15_PaddingRelation(padded_msg:seq<int>, msg:seq<int>, pad_mode:PadMode)
	requires ByteSeq(padded_msg);
	requires ByteSeq(msg);
{
	exists i:nat :: PKCS15_PaddingRelationAt(padded_msg, i, msg, pad_mode)
}

datatype RSAPubKeySpec = RSAPublicKeySpec_c(
	n:nat,	// modulus
	e:nat	// public key exponent
	);

predicate WellformedRSAPubKeySpec(pubkey:RSAPubKeySpec)
{ pubkey.n > 0 }

predicate KeySizeIs(pubkey:RSAPubKeySpec, k:nat)
{
	(k>0 ==> power2(8*(k-1)) <= pubkey.n)
	&& pubkey.n < power2(8*k)
}

datatype RSAKeyPairSpec = RSAKeyPairSpec_c(
	pub:RSAPubKeySpec,
	d:nat	// private key exponent
	);

predicate WellformedRSAKeyPairSpec(key:RSAKeyPairSpec)
{ WellformedRSAPubKeySpec(key.pub) }

predicate RSAEncryptionRelation(pubkey:RSAPubKeySpec, msg:seq<int>, ciphertext:seq<int>)
	requires WellformedRSAPubKeySpec(pubkey);
	requires ByteSeq(msg);
	requires ByteSeq(ciphertext);
{
	exists padded_plaintext:seq<int> ::
		ByteSeq(padded_plaintext)
		&& PKCS15_PaddingRelation(padded_plaintext, msg, PadModeEncrypt())
		&& power(BigEndianIntegerValue(padded_plaintext), pubkey.e) % pubkey.n
			== BigEndianIntegerValue(ciphertext)
}

predicate RSADecryptionRelation(key:RSAKeyPairSpec, ciphertext:seq<int>, msg:seq<int>)
	requires WellformedRSAKeyPairSpec(key);
	requires ByteSeq(ciphertext);
	requires ByteSeq(msg);
{
	exists padded_plaintext:seq<int> ::
		ByteSeq(padded_plaintext)
		&& power(BigEndianIntegerValue(ciphertext), key.d) % key.pub.n
			== BigEndianIntegerValue(padded_plaintext)
		&& PKCS15_PaddingRelation(padded_plaintext, msg, PadModeEncrypt())
}

predicate RSASignatureRelation(key:RSAKeyPairSpec, message:seq<int>, signature:seq<int>)
	requires WellformedRSAKeyPairSpec(key);
	requires ByteSeq(message);
	requires |ByteSeqToBoolSeq(message)| < power2(64);	// yuck!
	requires ByteSeq(signature);
{
	exists padded_msg:seq<int> ::
		ByteSeq(padded_msg)
		&& PKCS15_PaddingRelation(padded_msg, SHA256Digest(message), PadModeSign())
		&& power(BigEndianIntegerValue(padded_msg), key.d) % key.pub.n
			== BigEndianIntegerValue(signature)
}

predicate RSAVerificationRelation(pubkey:RSAPubKeySpec, message:seq<int>, signature:seq<int>)
	requires WellformedRSAPubKeySpec(pubkey);
	requires ByteSeq(message);
	requires |ByteSeqToBoolSeq(message)| < power2(64);	// yuck!
	requires ByteSeq(signature);
{
	exists padded_msg:seq<int> ::
		ByteSeq(padded_msg)
		&& PKCS15_PaddingRelation(padded_msg, SHA256Digest(message), PadModeSign())
		&& power(BigEndianIntegerValue(signature), pubkey.e) % pubkey.n
			== BigEndianIntegerValue(padded_msg)
}
