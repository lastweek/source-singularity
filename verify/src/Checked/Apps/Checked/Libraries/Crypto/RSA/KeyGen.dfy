include "MillerRabin.dfy"

method GenRandomPrime(bits:nat) returns (Random:BigNat)
	requires 3 < bits < power2(30);
	ensures FrumpyBigNat(Random);
	ensures IsProbablyPrime(I(Random), MILLER_RABIN_STRENGTH());
	ensures power2(bits-1) <= I(Random) < power2(bits);
{
	var isProbablyPrime:bool := false;

	lemma_power2_strictly_increases(30,32);
	assert(Word32(bits-1));
	var Offset := MakePower2Simple(bits-1);

	while (!isProbablyPrime)
		decreases *;
		invariant isProbablyPrime ==> FrumpyBigNat(Random);
		invariant isProbablyPrime ==> power2(bits-1) <= I(Random) < power2(bits);
		invariant isProbablyPrime ==> IsProbablyPrime(I(Random), MILLER_RABIN_STRENGTH());
	{
		var Entropy:BigNat := BigNatRandomPower2(bits-1);
		assert 0<=I(Entropy)<power2(bits-1);
		Random := BigNatAdd(Entropy, Offset);
		assert power2(bits-1)==I(Offset)<=I(Random)<power2(bits-1)+I(Offset);
		calc {
			I(Random);
			< power2(bits-1)+I(Offset);
			power2(bits-1)+power2(bits-1);
				{ lemma_mul_is_mul_boogie(2,power2(bits-1)); }
			mul(2,power2(bits-1));
				{ lemma_power2_1_is_2(); }
			mul(power2(1),power2(bits-1));
				{ lemma_power2_adds(1, bits-1); }
			power2(bits);
		}
		calc {
			3;
			< 4;
				{ lemma_power2_1_is_2(); reveal_power2(); }
			power2(2);
			<	{ lemma_power2_strictly_increases(2, bits-1); }
			power2(bits-1);
			<= I(Random);
		}
		calc {
			I(Random);
			< power2(bits);
			<	{ lemma_power2_strictly_increases(bits, power2(30)); }
			power2(power2(30));
			Frump();
		}
		assert FrumpyBigNat(Random);

		// TODO save time generating random strings and rejecting the even
		// ones by forcing odd values. Flip a bit; no spec burden! :v)

		isProbablyPrime := MillerRabinTest(Random, MILLER_RABIN_STRENGTH());
	}
}
