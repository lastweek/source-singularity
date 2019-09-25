include "BigNatCompare.dfy"
include "BigNatBitCount.dfy"

// NB we don't have a way to actually reason about the distribution
// of random numbers, so this implementation doesn't provy any such
// guarantee. However, it's probably right. :v)
// In its non-guaranteed attempts at uniformity, it
// may take about H-L / 2^ceil(lg2(H)) tries to find a number within the range.
// But in our application, L is close to zero, so it's probably not
// worse that two tries.

method rand_word_seq(l:nat) returns (rs:seq<int>)
	ensures WordSeq(rs);
	ensures |rs|==l;
	// TODO this is where I'd make a claim about the entropy in all
	// the words in the sequence.
{
	if (l==0)
	{
		rs := [];
	} else {
		var prefix := rand_word_seq(l-1);
		var tail := Random32();
		rs := prefix + [tail];
	}
}

method truncate_high_zeros(ws:seq<int>) returns (ts:seq<int>)
	decreases |ws|;
	ensures |ts| <= |ws|;
	ensures forall i:nat :: i<|ts| ==> ws[i]==ts[i];
	ensures 0<|ts| ==> ts[|ts|-1] != 0;
{
	if (|ws|==0)
	{
		ts := ws;
	}
	else if (ws[|ws|-1] != 0)
	{
		ts := ws;
	}
	else
	{
		ts := truncate_high_zeros(ws[0..|ws|-1]);
	}
}

method BigNatRandomPower2(c:nat) returns (R:BigNat)
	requires Word32(c);
	ensures WellformedBigNat(R);
	ensures I(R) < power2(c);
	// ensures UniformlyRandom(R, [0,power2(c)) )
	// can we ensure that there is a randomness input that can generate
	// each possible output value?
{
	// String together the right number of words.
	lemma_2to32();
	var full_words,extra_bits := Divide32(c, 32);
	assert mul(full_words,32)+extra_bits == c;
	var word_count;
	if (extra_bits == 0)
	{
		word_count := full_words;
	}
	if (extra_bits > 0)
	{
		// pluck an extra word to get the extra bits from
		word_count := full_words + 1;
	}
	lemma_mod_pos_bound(extra_bits, 32);
	assert c == mul(full_words,32)+extra_bits;
	lemma_fundamental_div_mod_converse(c, 32, full_words, extra_bits);

	var word_seq := rand_word_seq(word_count);

	// Mask the high word.
	// TODO all this stuff has no meaningful spec; I could be doing it wrong.
	if (|word_seq|==0)
	{
	}
	else if (extra_bits == 0)
	{
		// Keep the whole top word
	}
	else
	{
		var top:int := word_seq[|word_seq|-1];
		assert extra_bits<32;
		var mask := MakePower2Word32(extra_bits);
		assert mask == power2(extra_bits) > 0;
		assert Word32(mask);
		var masked_top := top % mask;
		lemma_mod_pos_bound(top, mask);
		assert Word32(masked_top);
		word_seq := word_seq[0..|word_seq|-1] + [masked_top];
		assert |word_seq| == word_count;
		assert WordSeq(word_seq);
	}

	var truncated_seq:seq<int> := truncate_high_zeros(word_seq);
	R := BigNat_ctor(truncated_seq);
	assert WellformedBigNat(R);

	// Prove the bitcount is correct.
	if (full_words==0 && extra_bits==0)
	{
		assert word_count==0;
		assert |word_seq|==0;
		assert |truncated_seq|==0;
		assert zero(R);

		calc {
			c;
			mul(full_words,32)+extra_bits;
			mul(0,32)+0;
				{ lemma_mul_basics(32); }
			0;
		}

		calc {
			I(R);
			< 1;
				{ lemma_power2_0_is_1(); }
			power2(0);
			power2(c);
		}
	}
	else
	{
		var thirty_twos:nat := full_words;
		var ones:nat;
		if (extra_bits==0)
		{
			ones := 32;
			thirty_twos := full_words-1;
			calc {
				mul(32,thirty_twos)+ones;
				mul(32,full_words-1)+32;
					{ lemma_mul_basics(32); }
				mul(32,full_words-1)+mul(32,1);
					{ lemma_mul_is_distributive_add_forall(); }
				mul(32,full_words-1+1);
				mul(32,full_words)+extra_bits;
					{ lemma_mul_is_commutative_forall(); }
				mul(full_words,32)+extra_bits;
				c;
			}
		}
		else
		{
			ones := extra_bits;
			calc {
				mul(32,thirty_twos)+ones;
				mul(32,full_words)+ones;
				mul(32,full_words)+extra_bits;
					{ lemma_mul_is_commutative_forall(); }
				mul(full_words,32)+extra_bits;
				c;
			}
		}
		assert mul(32,thirty_twos)+ones == c;
	
		var UBound:BigNat := MakePower2Minus1(thirty_twos,ones);
		assert I(UBound) < power2(c);
		if (|R.words| < word_count)
		{
			lemma_cmp_inequal_length(R, UBound);
			assert I(R) <= I(UBound);
		}
		else
		{
			lemma_le_equal_length(R, UBound);
			assert I(R) <= I(UBound);
		}
		assert I(R) < power2(c);
	}
}

method BigNatRandomFromInclusiveRange(L:BigNat, H:BigNat) returns (R:BigNat)
	requires WellformedBigNat(L);
	requires ModestBigNatWords(H);
	requires I(L) <= I(H);
	ensures WellformedBigNat(R);
	ensures I(L) <= I(R) <= I(H);
{
	var c:nat := BigNatCountBits(H);
	var lobound:bool := false;
	var hibound:bool := false;

	R := BigNatRandomPower2(c);
	lobound := BigNatLe(L, R);
	hibound := BigNatLe(R, H);

	while (!(lobound && hibound))
		decreases *;	// Possibly doesn't terminate.
		invariant WellformedBigNat(R);
		invariant lobound == (I(L)<=I(R));
		invariant hibound == (I(R)<=I(H));
	{
		R := BigNatRandomPower2(c);
		lobound := BigNatLe(L, R);
		hibound := BigNatLe(R, H);
	}
}


