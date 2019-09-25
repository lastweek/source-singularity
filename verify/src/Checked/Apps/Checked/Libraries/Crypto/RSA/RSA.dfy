include "../../../../Trusted/Spec/Libraries/Crypto/RSA/RSASpec.dfy"
include "../Hash/DigestImpl.dfy"
include "../../BigNum/BigNum.dfy"
include "../../BigNum/BigNatDiv.dfy"
include "../../BigNum/BigNatMod.dfy"
include "Extended_GCD.dfy"
include "KeyGen.dfy"
include "BlockEncoding.dfy"

method MultiplicativeInverse(phi:BigNat, e:BigNat) returns (success:bool, d:BigNat)
	requires FrumpyBigNat(phi);
	requires 1<I(phi);
	requires FrumpyBigNat(e);
	requires I(e) < I(phi);
	requires 0<I(phi);
	ensures success ==> WellformedBigNat(d);
	ensures success ==> I(d) <= I(phi);
	ensures success ==> mul(I(d), I(e)) % I(phi) == 1;
{
	lemma_frumpy_is_modest(phi);
	lemma_frumpy_is_modest(e);
	var k_num:BigNum,d_num:BigNum := extended_gcd(phi,e);

	var phik:BigNum := BigNumMul(BigNum_ctor(false, phi),k_num);
	var ed:BigNum := BigNumMul(BigNum_ctor(false, e),d_num);
	var gcd:BigNum := BigNumAdd(phik,ed);

	var sane_gcd:bool := BigNumEq(gcd, MakeSmallLiteralBigNum(1));
	if (sane_gcd)
	{
		success := true;
	}
	else
	{
		success := false;
	}

	if (success)
	{
		calc {
			1;
				// sane_gcd
			BV(gcd);
			BV(phik)+BV(ed);
			I(phi) * BV(k_num) + BV(ed);
			I(phi) * BV(k_num) + I(e) * BV(d_num);
			I(phi) * BV(k_num) + I(e) * BV(d_num) + 0 * I(phi);
				{ lemma_mul_is_mul_boogie(0, I(phi)); }
			I(phi) * BV(k_num) + I(e) * BV(d_num) + mul(0, I(phi));
		}

		lemma_fundamental_div_mod_converse(
			I(phi) * BV(k_num) + I(e) * BV(d_num),
			I(phi),
			0,
			1);
		assert (I(phi) * BV(k_num) + I(e) * BV(d_num)) % I(phi) == 1;

		calc ==> {
			(I(phi) * BV(k_num) + I(e) * BV(d_num)) % I(phi) == 1;
				{ lemma_mod_multiples_vanish(BV(k_num), I(e) * BV(d_num), I(phi)); }
			(I(e) * BV(d_num)) % I(phi) == 1;
				{ lemma_mul_is_commutative_forall(); }
			(BV(d_num) * I(e)) % I(phi) == 1;
		}

		if (!d_num.negate)
		{
			d := d_num.value;

			assert I(d) == BV(d_num);
			assert (I(d) * I(e)) % I(phi) == 1;
			assert WellformedBigNum(d_num);
			assert WellformedBigNat(d);

			calc {
				I(d);
				BV(d_num);
				<= I(phi);
			}
		}
		else
		{
			var d_prime:BigNum := BigNumAdd(d_num, BigNum_ctor(false, phi));
			assert 0<=BV(d_prime);
			d := d_prime.value;
			assert BV(d_prime) == I(d);

			calc {
				1;
				(BV(d_num)*I(e)) % I(phi);
					{ lemma_mod_multiples_vanish(I(e), BV(d_num)*I(e), I(phi)); }
				(I(phi)*I(e) + BV(d_num)*I(e)) % I(phi);
					{ lemma_mul_is_commutative_forall(); }
				(BV(d_num)*I(e) + I(e) * I(phi)) % I(phi);
					{ lemma_mul_is_commutative_forall(); }
				(BV(d_num)*I(e) + I(phi) * I(e)) % I(phi);
					{ lemma_mul_is_distributive_forall(); }
				((BV(d_num) + I(phi)) * I(e)) % I(phi);
				(BV(d_prime)*I(e)) % I(phi);
				(I(d)*I(e)) % I(phi);
			}

			assert WellformedBigNum(d_prime);
			assert WellformedBigNat(d);

			calc {
				I(d);
				BV(d_prime);
				BV(d_num)+I(phi);
				<= I(phi);
			}
		}
		assert WellformedBigNat(d);
	}
}

datatype RSAPublicKey = RSAPublicKey_c(
	n:BigNat,	// modulus
	e:BigNat	// public key exponent
	);

predicate WellformedPublicKey(pub:RSAPublicKey)
{
	FrumpyBigNat(pub.n)
	&& !zero(pub.n)
	&& FrumpyBigNat(pub.e)
}

datatype RSAKeyPair = RSAKeyPair_c(
	pub:RSAPublicKey,
	d:BigNat	// private key exponent
	);

predicate WellformedKeyPair(p:RSAKeyPair)
{
	WellformedPublicKey(p.pub)
	&& FrumpyBigNat(p.d)
}

method RSAKeyGen(bits:nat) returns (key:RSAKeyPair)
	requires 20<bits;
	requires bits<power2(29);
//	ensures ValidKeyLength(key);	// dead idea
	ensures WellformedKeyPair(key);
	ensures I(key.pub.n) >= power2(bits);
    ensures ImplKeyPairSize(key) >= bits / 8;
{
	lemma_2to32();
	var one := MakeSmallLiteralBigNat(1);
	var e := MakeSmallLiteralBigNat(65537);

	calc {
		I(e);
		< 131072;
			{ lemma_2toX(); reveal_power2(); }
		power2(17);
		<	{ lemma_power2_strictly_increases(17,1073741824); }
		power2(1073741824);
			{ lemma_2toX(); reveal_power2(); }
		power2(power2(30));
		Frump();
	}

	var halfbits:nat := bits/2 + 2;

	lemma_div_is_ordered(20, bits, 2);
	assert 20/2 <= bits/2;
	assert 10 <= bits/2;
	assert 10 <= halfbits;

	calc {
		halfbits;
		bits/2 + 2;
		<=	{ lemma_div_is_ordered(bits, power2(29), 2); }
		power2(29)/2 + 2;
			{
				calc {
					power2(29)/2;
						{ reveal_power2(); }
					(2*power2(28))/2;
					(power2(28)*2)/2;
						{ lemma_mul_is_mul_boogie(power2(28), 2); }
					mul(power2(28),2)/2;
						{ lemma_div_is_div_boogie_at_least_for_2(mul(power2(28),2)); }
					INTERNAL_div(mul(power2(28),2),2);
						{ lemma_div_by_multiple(power2(28), 2); }
					power2(28);
				}
			}
		power2(28) + 2;
		<=	{
				calc {
					2;
						{ lemma_power2_1_is_2(); }
					power2(1);
					<	{ lemma_power2_strictly_increases(1,28); }
					power2(28);
				}
			}
		power2(28) + power2(28);
		2*power2(28);
			{ reveal_power2(); }
		power2(29);
	}
	lemma_power2_strictly_increases(29,30);

	calc {
		power2(halfbits);
		<=	{ lemma_power2_increases(halfbits, power2(29)); }
		power2(power2(29));
	}

	var success:bool := false;
	var p:BigNat, q:BigNat, d:BigNat;
	ghost var n:int;

	while (!success)
		decreases *;
		invariant success ==> WellformedBigNat(p);
		invariant success ==> WellformedBigNat(q);
		invariant success ==> FrumpyBigNat(d);
		invariant success ==> n == I(p)*I(q);
		invariant success ==> n < Frump();
		invariant success ==> n != 0;
		invariant success ==> power2(bits) <= n;
		invariant success ==> ((I(p)-1)*(I(q)-1)) != 0;
		invariant success ==> mul(I(d), I(e)) % ((I(p)-1)*(I(q)-1)) == 1;
	{
		p := GenRandomPrime(halfbits);
		q := GenRandomPrime(halfbits);
		assert I(p) < power2(power2(29));
		assert I(q) < power2(power2(29));

		assert !zero(p);
		assert !zero(q);
		n := I(p)*I(q);
		lemma_mul_nonzero(I(p), I(q));
		assert n!=0;

		calc {
			power2(bits);
			<= { lemma_power2_increases(bits, halfbits-1 + halfbits-1); }
			power2(halfbits-1 + halfbits-1);
				{ lemma_power2_adds(halfbits-1, halfbits-1); }
			power2(halfbits-1) * power2(halfbits-1);
			<=	{ lemma_mul_inequality(power2(halfbits-1), I(p), power2(halfbits-1)); }
			I(p) * power2(halfbits-1);
			<=	{ lemma_mul_left_inequality(I(p), power2(halfbits-1), I(q)); }
			I(p) * I(q);
			n;
		}

		var pMinus1:BigNat := BigNatSub(p,one);
		var qMinus1:BigNat := BigNatSub(q,one);
		assert I(pMinus1) < power2(power2(29));
		assert I(qMinus1) < power2(power2(29));

		var phi_n:BigNat := BigNatMul(pMinus1,qMinus1);
		calc {
			1;
				{ lemma_power2_0_is_1(); }
			power2(0);
			<	{ lemma_power2_strictly_increases(0,halfbits-2); }
			power2(halfbits-2);
			power2(halfbits-2) + power2(halfbits-2) - power2(halfbits-2);
			2*power2(halfbits-2) - power2(halfbits-2);
//				{ lemma_mul_is_mul_boogie(2, power2(halfbits-2)); }
//			mul(2,power2(halfbits-2)) - power2(halfbits-2);
				{ reveal_power2(); }
			power2(halfbits-1) - power2(halfbits-2);
			<=	{ lemma_power2_strictly_increases(0,halfbits-2); }
			power2(halfbits-1) - power2(0);
				{ lemma_power2_0_is_1(); }
			power2(halfbits-1) - 1;
		}

		calc {
			power2(halfbits-2);
			power2(halfbits-2) + power2(halfbits-2) - power2(halfbits-2);
			<	{
					lemma_power2_0_is_1();
					lemma_power2_strictly_increases(0,halfbits-2);
				}
			power2(halfbits-2) + power2(halfbits-2) - 1;
			2*power2(halfbits-2) - 1;
				{ reveal_power2(); }
			power2(halfbits-1) - 1;
		}

		calc {
			power2(halfbits-1) - 1;
			<=	// GenRandomPrime ensures ensures
			I(p) - 1;
			I(pMinus1);
		}
		assert power2(halfbits-1) - 1 <= I(pMinus1);
		calc {
			power2(halfbits-1) - 1;
			<=	// GenRandomPrime ensures ensures
			I(q) - 1;
			I(qMinus1);
		}
		assert power2(halfbits-1) - 1 <= I(qMinus1);
		assert 1 < power2(halfbits-1) - 1;

		calc {
			I(e);
			< 131072;
				{ lemma_2toX(); reveal_power2(); }
			power2(17);
			<	{ lemma_power2_strictly_increases(17,2*halfbits-4); }
			power2(2*halfbits-4);
			power2(halfbits-2 + halfbits-2);
				{ lemma_power2_adds(halfbits-2, halfbits-2); }
			power2(halfbits-2) * power2(halfbits-2);
			<=	{ lemma_mul_inequality(power2(halfbits-2), I(pMinus1), power2(halfbits-2)); }
			I(pMinus1) * power2(halfbits-2);
			<=	{
				assert power2(halfbits-2) <= I(qMinus1);
				lemma_mul_left_inequality(I(pMinus1), power2(halfbits-2), I(qMinus1));
				}
			I(pMinus1) * I(qMinus1);
			I(phi_n);
		}
		
		calc {
			I(p) * I(q);
			<	{ lemma_mul_strict_inequality(
					I(p), power2(power2(29)), I(q)); }
			power2(power2(29)) * I(q);
			<	{ lemma_mul_left_inequality(
					power2(power2(29)), I(q), power2(power2(29))); }
			power2(power2(29)) * power2(power2(29));
				{ lemma_power2_adds(power2(29), power2(29)); }
			power2(power2(29) + power2(29));
			power2(2*power2(29));
				{ reveal_power2(); }
			power2(power2(30));
			Frump();
		}

		calc {
			I(phi_n);
			I(pMinus1) * I(qMinus1);
			<	{ lemma_mul_strict_inequality(
					I(pMinus1), power2(power2(29)), I(qMinus1)); }
			power2(power2(29)) * I(qMinus1);
			<	{ lemma_mul_left_inequality(
					power2(power2(29)), I(qMinus1), power2(power2(29))); }
			power2(power2(29)) * power2(power2(29));
				{ lemma_power2_adds(power2(29), power2(29)); }
			power2(power2(29) + power2(29));
			power2(2*power2(29));
				{ reveal_power2(); }
			power2(power2(30));
			Frump();
		}

		calc {
			1;
			< I(qMinus1);
			<	{
					assert 1 < I(pMinus1);
					assert 0 < I(qMinus1);
					lemma_mul_strictly_increases(I(pMinus1), I(qMinus1));
					assert I(qMinus1) < I(pMinus1)*I(qMinus1);
				}
			I(pMinus1) * I(qMinus1);
			I(phi_n);
		}

		assert I(phi_n) < power2(power2(30)) == Frump();
		assert FrumpyBigNat(phi_n);

		assert I(e) < I(phi_n);
		assert FrumpyBigNat(e);

		success,d := MultiplicativeInverse(phi_n, e);

		if (success) {
			calc {
				I(d);
				<= I(phi_n);
				< Frump();
			}
			assert FrumpyBigNat(d);
		}
	}

	var N:BigNat := BigNatMul(p, q);
	assert I(N)==n;
	assert FrumpyBigNat(N);
	assert !zero(N);

	key := RSAKeyPair_c(RSAPublicKey_c(N, e), d);

    ghost var ikps := ImplKeyPairSize(key);
    if (ikps < bits / 8) {
        assert KeySizeIs(PubKeyToSpec(key.pub), ikps) && 0 <= ikps;
        calc {
            power2(bits);
            <= I(key.pub.n);
            < power2(8 * ikps);
            < { lemma_power2_strictly_increases(8 * ikps, 8 * (bits / 8)); }
              power2(8 * (bits / 8));
            <= { lemma_power2_increases(8 * (bits / 8), bits); }
               power2(bits);
        }
        assert false;
    }
}

method MakeNullKey(bits:nat) returns (key:RSAKeyPair)
	requires Word32(bits);
{
	var n := MakePower2Simple(bits);
	lemma_2to32();
	var one := MakeSmallLiteralBigNat(1);
	key := RSAKeyPair_c(RSAPublicKey_c(n, one), one);
}

// Eventually useful for lemma_message_transmission
predicate EncryptionRelation(pubkey:RSAPublicKey, p:BigNat, c:BigNat)
	requires WellformedPublicKey(pubkey);
	requires WellformedBigNat(p);
	requires WellformedBigNat(c);
{
	I(c)==power(I(p),I(pubkey.e)) % I(pubkey.n)
}

method InnerEncrypt(pubkey:RSAPublicKey, plaintext:BigNat) returns (ciphertext:BigNat)
	requires WellformedPublicKey(pubkey);
	requires FrumpyBigNat(plaintext);
	requires 0 < I(plaintext) < I(pubkey.n);
	ensures FrumpyBigNat(ciphertext);
	ensures I(ciphertext) < I(pubkey.n);
	ensures EncryptionRelation(pubkey, plaintext, ciphertext);
{
	ciphertext := BigNatModExp(plaintext, pubkey.e, pubkey.n);
}

function PubKeyToSpec(pubkey:RSAPublicKey) : RSAPubKeySpec
	requires WellformedPublicKey(pubkey);
{
	RSAPublicKeySpec_c(I(pubkey.n), I(pubkey.e))
}

function KeyPairToSpec(key:RSAKeyPair) : RSAKeyPairSpec
	requires WellformedKeyPair(key);
{
	RSAKeyPairSpec_c(PubKeyToSpec(key.pub), I(key.d))
}

predicate KeySizeIsCore(n:int, k:nat)
{
	(k>0 ==> power2(8*(k-1)) <= n) && n < power2(8*k)
}

lemma lemma_KeySizeIsCore_exists(n:nat)
	ensures exists j:nat :: KeySizeIsCore(n, j);
{
	var j;

	if (n==0)
	{
		calc {
			0;
			< 1;
				{ lemma_power2_0_is_1(); }
			power2(0);
			power2(8*0);
		}
		j:=0;
		assert KeySizeIsCore(n,j);
	}
	else
	{
		lemma_KeySizeIsCore_exists(n-1);
		var j1:nat :| KeySizeIsCore(n-1, j1);
		assert (j1>0 ==> power2(8*(j1-1)) <= n-1) && n-1 < power2(8*j1);

		if (n < power2(8*j1))
		{
//			assert j1>0 ==> power2(8*(j1-1)) <= n-1;
//			assert j1>0 ==> power2(8*(j1-1)) <= n;
//			assert n-1 < power2(8*j1);
			j := j1;
			assert KeySizeIsCore(n,j);
		}
		else
		{
			j := j1+1;
			assert power2(8*j1) <= n;
			assert power2(8*(j-1)) <= n;

			assert n-1 < power2(8*j1);
			assert n <= power2(8*j1);
			assert n == power2(8*j1);
			assert 8*j1 < 8*j;
			lemma_power2_strictly_increases(8*j1, 8*j);
			assert n < power2(8*j);

			assert KeySizeIsCore(n,j);
		}
	}
}

lemma lemma_KeySizeIs_exists(pubkey:RSAPubKeySpec)
	ensures exists j:nat :: KeySizeIs(pubkey, j);
{
	lemma_KeySizeIsCore_exists(pubkey.n);
	var j:nat :| KeySizeIsCore(pubkey.n, j);
	assert KeySizeIs(pubkey, j);
}

lemma lemma_KeySizeIs_uniq_sym(pubkey:RSAPubKeySpec, j:nat, k:nat)
	requires KeySizeIs(pubkey, j);
	requires KeySizeIs(pubkey, k);
	requires j<k;
	ensures false;
{
	calc ==> {
		j <= k-1;
		8*j <= 8*(k-1);
			{ lemma_power2_increases(8*j, 8*(k-1)); }
		power2(8*j) <= power2(8*(k-1));
		pubkey.n < power2(8*j) <= power2(8*(k-1)) <= pubkey.n;
		false;
	}
}

lemma lemma_KeySizeIs_uniq(pubkey:RSAPubKeySpec)
	ensures forall j:nat, k:nat :: KeySizeIs(pubkey, j) && KeySizeIs(pubkey, k) ==> j==k;
{
	forall (j:nat,k:nat | KeySizeIs(pubkey, j) && KeySizeIs(pubkey, k))
		ensures j==k;
	{
		if (j < k)
		{
			lemma_KeySizeIs_uniq_sym(pubkey, j, k);
		}
		else if (j > k)
		{
			lemma_KeySizeIs_uniq_sym(pubkey, k, j);
		}
	}
}

function KeySize(pubkey:RSAPubKeySpec) : int
	requires WellformedRSAPubKeySpec(pubkey);
	ensures 0<=KeySize(pubkey);
	ensures KeySizeIs(pubkey, KeySize(pubkey));
	ensures forall k:nat :: KeySizeIs(pubkey, k) ==> KeySize(pubkey)==k;
{
	lemma_KeySizeIs_exists(pubkey);
	lemma_KeySizeIs_uniq(pubkey);
	var k:nat :| KeySizeIs(pubkey, k) && 0<=k;
	k
}

method MeasureKeySize(pubkey:RSAPublicKey) returns (k:nat)
	requires WellformedPublicKey(pubkey);
	ensures KeySizeIs(PubKeyToSpec(pubkey), k);
	ensures k>0;
{
	// Can't compute this from |pubkey.n.words|, since that's only
	// word-level precision; need byte-level. So we'll start from bits.
	lemma_frumpy_is_modest(pubkey.n);
	var bit_count := BigNatCountBits(pubkey.n);
	assert 0 < bit_count;
	k := (bit_count-1) / 8 + 1;

	ghost var spubkey := PubKeyToSpec(pubkey);

	calc {
		bit_count-1;
			{ lemma_fundamental_div_mod(bit_count-1,8); }
		mul(8,div(bit_count-1,8)) + mod(bit_count-1,8);
			{ lemma_mul_is_mul_boogie(8,div(bit_count-1,8)); }
		8*div(bit_count-1,8) + mod(bit_count-1,8);
			{ lemma_div_is_div_boogie_for_8_which_is_also_a_number(bit_count-1); }
		8*((bit_count-1)/8) + mod(bit_count-1,8);
		8*((bit_count-1)/8) + 8 - 8 + mod(bit_count-1,8);
		8*((bit_count-1)/8+1) - 8 + mod(bit_count-1,8);
		8*k - 8 + mod(bit_count-1,8);
	}

	if (k>0)
	{
		calc {
			power2(8*(k-1));
			power2(8*k-8);
			<=	{
					lemma_mod_remainder();
					assert 0 <= mod(bit_count-1,8);
					assert 8*k-8 <= 8*k - 8 + mod(bit_count-1,8);
					lemma_power2_increases(8*k-8, 8*k - 8 + mod(bit_count-1,8));
				}
			power2(8*k - 8 + mod(bit_count-1,8));
			power2(bit_count-1);
			<= I(pubkey.n);
			spubkey.n;
		}
	}

	calc {
		spubkey.n;
		I(pubkey.n);
		< power2(bit_count);
		power2(bit_count-1+1);
		power2(8*k - 8 + mod(bit_count-1,8) + 1);
		power2(8*k - 7 + mod(bit_count-1,8));
		<=	{
			lemma_mod_remainder();
			assert mod(bit_count-1,8) < 8;
			lemma_power2_increases(8*k - 7 + mod(bit_count-1,8), 8*k);
			}
		power2(8*k);
	}
}

method Encrypt(pubkey:RSAPublicKey, plaintext:seq<int>) returns (success:bool,ciphertext:seq<int>)
	requires ByteSeq(plaintext);
	requires WellformedPublicKey(pubkey);
	requires exists k:nat :: KeySizeIs(PubKeyToSpec(pubkey), k) && |plaintext| <= k - 11;
	ensures WellformedRSAPubKeySpec(PubKeyToSpec(pubkey));
	ensures ByteSeq(ciphertext);
	ensures success ==> RSAEncryptionRelation(PubKeyToSpec(pubkey), plaintext, ciphertext);
{
	var keysize := MeasureKeySize(pubkey);

	if (!(|plaintext| <= keysize - 11))
	{
		success := false;
		ciphertext := [];
	}
	else if (keysize % 4 != 0)
	{
		// TODO completeness: I'm only getting away with this because
		// this implementation doesn't promise to decode every valid message.
		success := false;
		ciphertext := [];
	}
	else
	{
		var plainN:BigNat;
		ghost var padded_plaintext:seq<int>;
		plainN,padded_plaintext := MessageToInteger(plaintext, keysize, PadModeEncrypt());

		calc {
			I(plainN);
			<= power2(8*(keysize-1));
			<= {
				// KeySizeIs ensures
				assert KeySizeIs(PubKeyToSpec(pubkey), keysize);
				assert (keysize>0 ==> power2(8*(keysize-1)) <= I(pubkey.n));
				assert power2(8*(keysize-1)) <= I(pubkey.n);
			}
			I(pubkey.n);
		}
		assert FrumpyBigNat(plainN);

		var cipherN:BigNat := InnerEncrypt(pubkey, plainN);
		ciphertext := IntegerToBESeq(cipherN);

		assert ByteSeq(padded_plaintext);
		assert PKCS15_PaddingRelation(padded_plaintext, plaintext, PadModeEncrypt());

		calc {
			BigEndianIntegerValue(ciphertext);
			I(cipherN);
				// InnerEncrypt ensures, EncryptionRelation ensures
			power(I(plainN),I(pubkey.e)) % I(pubkey.n);
			power(BigEndianIntegerValue(padded_plaintext),I(pubkey.e)) % I(pubkey.n);
			power(BigEndianIntegerValue(padded_plaintext),PubKeyToSpec(pubkey).e) % PubKeyToSpec(pubkey).n;
			power(BigEndianIntegerValue(padded_plaintext),PubKeyToSpec(pubkey).e) % PubKeyToSpec(pubkey).n;
		}
		assert power(BigEndianIntegerValue(padded_plaintext), PubKeyToSpec(pubkey).e) % PubKeyToSpec(pubkey).n
			== BigEndianIntegerValue(ciphertext);

		assert RSAEncryptionRelation(PubKeyToSpec(pubkey), plaintext, ciphertext);
	}
}

// Eventually useful for lemma_message_transmission
predicate DecryptionRelation(key:RSAKeyPair, c:BigNat, p:BigNat)
	requires WellformedKeyPair(key);
	requires WellformedBigNat(c);
	requires WellformedBigNat(p);
{
	I(p)==power(I(c),I(key.d)) % I(key.pub.n)
}

method InnerDecrypt(key:RSAKeyPair, ciphertext:BigNat) returns (plaintext:BigNat)
	requires WellformedKeyPair(key);
	requires FrumpyBigNat(ciphertext);
	requires 0 < I(ciphertext) < I(key.pub.n);
	ensures FrumpyBigNat(plaintext);
	ensures I(plaintext) < I(key.pub.n);
	ensures DecryptionRelation(key, ciphertext, plaintext);
{
	plaintext := BigNatModExp(ciphertext, key.d, key.pub.n);
}

method Decrypt(key:RSAKeyPair, ciphertext:seq<int>) returns (success:bool,plaintext:seq<int>)
	requires WellformedKeyPair(key);
	requires ByteSeq(ciphertext);
	ensures WellformedRSAKeyPairSpec(KeyPairToSpec(key));
	ensures ByteSeq(plaintext);
	ensures success ==> RSADecryptionRelation(KeyPairToSpec(key), ciphertext, plaintext);
{
	var keysize := MeasureKeySize(key.pub);

	plaintext := [];

	if (|ciphertext|%4!=0)
	{
		// This constraint is a limitation of our stupid bytes->words
		// conversion; it may prevent us from decoding legitimate
		// messages from other senders.
		// TODO completeness: I'm only getting away with this because
		// this implementation doesn't promise to decode every valid message.
		success := false;
	}
	else if (|ciphertext|==0)
	{
		// well, okay, that's legit -- no message here.
		success := false;
	}
	else if (ciphertext[1] == 0)
	{
		// wait, this may also be a legitimate encoding. Hrm.
		// TODO completeness: I'm only getting away with this because
		// this implementation doesn't promise to decode every valid message.
		success := false;
	}
	else
	{
		var cipherN:BigNat := BESeqToInteger(ciphertext);

		var ciphertext_too_big:bool := BigNatGe(cipherN, key.pub.n);
		if (zero(cipherN) || ciphertext_too_big)
		{
			// the ciphertext is too big to even try to decode.
			// It wouldn't have been a valid message -- although we
			// haven't proven that:
			// TODO completeness: I'm only getting away with this because
			// this implementation doesn't promise to decode every valid message.
			success := false;
		}
		else
		{
			assert I(cipherN) < I(key.pub.n);	// we just checked.
			assert I(cipherN) < Frump();
			assert FrumpyBigNat(cipherN);

			var plainN:BigNat := InnerDecrypt(key, cipherN);
			ghost var padded_plaintext:seq<int>;
			success,plaintext,padded_plaintext := IntegerToMessage(plainN, PadModeEncrypt());

			if (success) {
				assert ByteSeq(padded_plaintext);

				calc {
					power(BigEndianIntegerValue(ciphertext), I(key.d)) % I(key.pub.n);
					power(I(cipherN), I(key.d)) % I(key.pub.n);
					I(plainN);
					BigEndianIntegerValue(padded_plaintext);
				}
				
				assert power(BigEndianIntegerValue(ciphertext), I(key.d)) % I(key.pub.n)
					== BigEndianIntegerValue(padded_plaintext);
				assert PKCS15_PaddingRelation(padded_plaintext, plaintext, PadModeEncrypt());

				assert RSADecryptionRelation(KeyPairToSpec(key), ciphertext, plaintext);
			}
		}
	}
}

// TODO there's some copypasta in here, that could use refactoring.
//
// Verify starts like Decrypt (since the signature is an exponeniated
// already-padded thing) and ends like Encrypt (since we exponentiate
// with the public key).
// Conversely,
// Sign starts like Encrypt (since the message needs padding before
// exponentiating), and ends like Decrypt (since we exponentiate
// with the private key).

predicate UnDigestedSignatureRelation(key:RSAKeyPairSpec, digest:seq<int>, signature:seq<int>, padded_msg:seq<int>)
	requires WellformedRSAKeyPairSpec(key);
	requires ByteSeq(digest);
	requires ByteSeq(signature);
{
	ByteSeq(padded_msg)
	&& PKCS15_PaddingRelation(padded_msg, digest, PadModeSign())
	&& power(BigEndianIntegerValue(padded_msg), key.d) % key.pub.n
		== BigEndianIntegerValue(signature)
}

predicate UnDigestedVerificationRelation(pubkey:RSAPubKeySpec, digest:seq<int>, signature:seq<int>)
	requires WellformedRSAPubKeySpec(pubkey);
	requires ByteSeq(digest);
	requires ByteSeq(signature);
{
	exists padded_msg:seq<int> ::
		ByteSeq(padded_msg)
		&& PKCS15_PaddingRelation(padded_msg, digest, PadModeSign())
		&& power(BigEndianIntegerValue(signature), pubkey.e) % pubkey.n
			== BigEndianIntegerValue(padded_msg)
}

method UndigestedVerify(pubkey:RSAPublicKey, signature:seq<int>) returns (success:bool,message:seq<int>)
	requires WellformedPublicKey(pubkey);
	requires ByteSeq(signature);
	ensures WellformedRSAPubKeySpec(PubKeyToSpec(pubkey));
	ensures ByteSeq(message);
	ensures success ==> UnDigestedVerificationRelation(PubKeyToSpec(pubkey), message, signature);
{
	var keysize := MeasureKeySize(pubkey);
	var x:=7;

	message := [];

	if (|signature|%4!=0)
	{
		// This constraint is a limitation of our stupid bytes->words
		// conversion; it may prevent us from decoding legitimate
		// messages from other senders.
		// TODO completeness: I'm only getting away with this because
		// this implementation doesn't promise to decode every valid message.
		success := false;
	}
	else if (|signature|==0)
	{
		// well, okay, that's legit -- no message here.
		success := false;
	}
	else if (signature[1] == 0)
	{
		// wait, this may also be a legitimate encoding. Hrm.
		// TODO completeness: I'm only getting away with this because
		// this implementation doesn't promise to decode every valid message.
		success := false;
	}
	else
	{
		var signatureN:BigNat := BESeqToInteger(signature);

		var ciphertext_too_big:bool := BigNatGe(signatureN, pubkey.n);
		if (zero(signatureN) || ciphertext_too_big)
		{
			// the signature is too big to even try to decode.
			// It wouldn't have been a valid message -- although we
			// haven't proven that:
			// TODO completeness: I'm only getting away with this because
			// this implementation doesn't promise to decode every valid message.
			success := false;
		}
		else
		{
			assert I(signatureN) < I(pubkey.n);	// we just checked.
			assert I(signatureN) < Frump();
			assert FrumpyBigNat(signatureN);

			var messageN:BigNat := InnerEncrypt(pubkey, signatureN);
			message := IntegerToBESeq(messageN);

			ghost var padded_message:seq<int>;
			success,message,padded_message := IntegerToMessage(messageN, PadModeSign());

			if (success)
			{
				assert ByteSeq(padded_message);
				assert PKCS15_PaddingRelation(padded_message, message, PadModeSign());

				calc {
					BigEndianIntegerValue(padded_message);
					I(messageN);
						// InnerEncrypt ensures, EncryptionRelation ensures
					power(I(signatureN),I(pubkey.e)) % I(pubkey.n);
					power(BigEndianIntegerValue(signature),I(pubkey.e)) % I(pubkey.n);
				}

				assert power(BigEndianIntegerValue(signature), I(pubkey.e)) % I(pubkey.n)
					== BigEndianIntegerValue(padded_message);
				assert UnDigestedVerificationRelation(PubKeyToSpec(pubkey), message, signature);
			}
		}
	}
}

function ImplKeyPairSize(key:RSAKeyPair) : int
	requires WellformedKeyPair(key);
	ensures 0<=ImplKeyPairSize(key);
	ensures KeySizeIs(PubKeyToSpec(key.pub), ImplKeyPairSize(key));
{
	lemma_KeySizeIs_exists(PubKeyToSpec(key.pub));
	var keysize:nat :| KeySizeIs(PubKeyToSpec(key.pub), keysize) && 0<=keysize;
	keysize
}

method UndigestedSign(key:RSAKeyPair, message:seq<int>) returns (success:bool,signature:seq<int>,ghost padded_msg:seq<int>)
	requires WellformedKeyPair(key);
	requires ByteSeq(message);
	ensures WellformedRSAKeyPairSpec(KeyPairToSpec(key));
	ensures ByteSeq(signature);
	ensures (|message| <= ImplKeyPairSize(key) - 11)
		&& (ImplKeyPairSize(key) % 4 == 0) ==> success;
	ensures ByteSeq(padded_msg);
	ensures success ==> UnDigestedSignatureRelation(KeyPairToSpec(key), message, signature, padded_msg);
{
	var keysize := MeasureKeySize(key.pub);
	assert keysize == KeySize(PubKeyToSpec(key.pub)) == ImplKeyPairSize(key);

	if (!(|message| <= keysize - 11))
	{
		success := false;
		signature := [];
		padded_msg := [];
	}
	else if (keysize % 4 != 0)
	{
		// TODO completeness: I'm only getting away with this because
		// this implementation doesn't promise to decode every valid message.
		success := false;
		signature := [];
		padded_msg := [];
	}
	else
	{
		var messageN:BigNat;
		messageN,padded_msg := MessageToInteger(message, keysize, PadModeSign());

		calc {
			I(messageN);
			<= power2(8*(keysize-1));
			<= {
				// KeySizeIs ensures
				assert KeySizeIs(PubKeyToSpec(key.pub), keysize);
				assert (keysize>0 ==> power2(8*(keysize-1)) <= I(key.pub.n));
				assert power2(8*(keysize-1)) <= I(key.pub.n);
			}
			I(key.pub.n);
		}
		assert FrumpyBigNat(messageN);

		var signatureN:BigNat := InnerDecrypt(key, messageN);
		success := true;
		signature := IntegerToBESeq(signatureN);

		assert PKCS15_PaddingRelation(padded_msg, message, PadModeSign());

		calc {
			power(BigEndianIntegerValue(padded_msg), I(key.d)) % I(key.pub.n);
			power(I(messageN), I(key.d)) % I(key.pub.n);
			I(signatureN);
			BigEndianIntegerValue(signature);
		}
		
		assert power(BigEndianIntegerValue(padded_msg), I(key.d)) % I(key.pub.n)
			== BigEndianIntegerValue(signature);

		assert UnDigestedSignatureRelation(KeyPairToSpec(key), message, signature, padded_msg);
	}
}

method HashedSign(key:RSAKeyPair, message:seq<int>) returns (signature:seq<int>)
	requires WellformedKeyPair(key);
	requires ByteSeq(message);
	requires |message| < power2(61);
	requires 286 <= ImplKeyPairSize(key);
	requires (ImplKeyPairSize(key) % 4 == 0);
	ensures |ByteSeqToBoolSeq(message)| < power2(64);
	ensures WellformedRSAKeyPairSpec(KeyPairToSpec(key));
	ensures ByteSeq(signature);
	ensures RSASignatureRelation(KeyPairToSpec(key), message, signature);
{

	// ImplKeyPairSize ensures:
//	assert KeySizeIs(PubKeyToSpec(key.pub), ImplKeyPairSize(key));
	// KeySizeIs ensures:
//	assert (ImplKeyPairSize(key)>0 ==> power2(8*(ImplKeyPairSize(key)-1)) <= pubkey.n);
	// WellformedPublicKey ensures:
//	assert I(key.pub.n) < power2(power2(30));
	if (ImplKeyPairSize(key)>0) {
		calc ==> {
			power2(8*(ImplKeyPairSize(key)-1)) <= power2(power2(30));
				{ lemma_power2_increases_converse(8*(ImplKeyPairSize(key)-1), power2(30)); }
			8*(ImplKeyPairSize(key)-1) <= power2(30);
			8*ImplKeyPairSize(key)-8 <= power2(30);
		}
		calc {
			8*ImplKeyPairSize(key);
			<= power2(30) + 8;
			<	{ lemma_2toX(); reveal_power2(); lemma_power2_strictly_increases(3, 30); }
			power2(30) + power2(30);
				{ lemma_mul_is_mul_boogie(2,power2(30)); }
			mul(2,power2(30));
				{ lemma_power2_1_is_2(); }
			mul(power2(1),power2(30));
				{ lemma_power2_adds(1,30); }
			power2(31);
			<	{ lemma_power2_strictly_increases(31,64); }
			power2(64);
		}
	} else {
		calc {
			8*ImplKeyPairSize(key);
			0;
			<=	{ lemma_2toX(); }
			power2(32);
			<	{ lemma_power2_strictly_increases(32,64); }
			power2(64);
		}
	}

	calc {
		|ByteSeqToBoolSeq(message)|;
		8*|message|;
		< 8*power2(61);
        { lemma_2toX(); reveal_power2(); assert 8 == power2(3); lemma_mul_is_mul_boogie(power2(3), power2(61)); }
        power2(3)*power2(61);
        { lemma_power2_adds(3, 61); }
		power2(64);
	}

	var digested_message := SHA256DigestImpl(message);
	var success:bool;
	ghost var padded_msg:seq<int>;
	success,signature,padded_msg := UndigestedSign(key, digested_message);

	assert |digested_message| <= ImplKeyPairSize(key) - 11;
	assert success;

	assert UnDigestedSignatureRelation(KeyPairToSpec(key), digested_message, signature, padded_msg);
	assert PKCS15_PaddingRelation(padded_msg, digested_message, PadModeSign());
	assert digested_message == SHA256Digest(message);
	assert ByteSeq(padded_msg);
	assert PKCS15_PaddingRelation(padded_msg, SHA256Digest(message), PadModeSign());
	assert power(BigEndianIntegerValue(padded_msg), KeyPairToSpec(key).d) % KeyPairToSpec(key).pub.n
			== BigEndianIntegerValue(signature);

	assert RSASignatureRelation(KeyPairToSpec(key), message, signature);
}

method HashedVerify(pubkey:RSAPublicKey, message:seq<int>, signature:seq<int>) returns (verifies:bool)
	requires WellformedPublicKey(pubkey);
	requires ByteSeq(message);
	requires |ByteSeqToBoolSeq(message)| < power2(64);	// yuck!
	requires ByteSeq(signature);
	ensures WellformedRSAPubKeySpec(PubKeyToSpec(pubkey));
	ensures verifies ==> RSAVerificationRelation(PubKeyToSpec(pubkey), message, signature);
{
	var digested_message := SHA256DigestImpl(message);
	var success,putative_message := UndigestedVerify(pubkey, signature);
	if (!success)
	{
		verifies := false;
	}
	else
	{
		verifies := digested_message == putative_message;
	}
}

lemma lemma_message_transmission(key:RSAKeyPair, p_in:BigNat, c:BigNat, p_out:BigNat)
	requires WellformedKeyPair(key);
	requires WellformedBigNat(p_in);
	requires WellformedBigNat(c);
	requires WellformedBigNat(p_out);
	requires I(p_in) < I(key.pub.n);
	requires I(c) < I(key.pub.n);
	requires I(p_out) < I(key.pub.n);
	requires EncryptionRelation(key.pub, p_in, c);
	requires DecryptionRelation(key, c, p_out);
	ensures p_in == p_out;
// Once we've proven this, we can remove RSADecryptionRelation from the spec,
// and just use RSAEncryptionRelation for both directions.
{ assume false; }	// TODO
