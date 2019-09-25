include "BigNatSub.dfy"
include "BigNatMul.dfy"
include "BigNatBitCount.dfy"

method fill_sequence(value:nat, copies:nat) returns (vs:seq<int>)
	ensures forall v :: v in vs ==> v == value;
	ensures |vs|==copies;
{
	if (copies==0)
	{
		vs := [];
	}
	else
	{
		var sub_vs:seq<int> := fill_sequence(value, copies-1);
		vs := sub_vs + [value];
	}
}

lemma lemma_MakePower2(S:BigNat)
	decreases |S.words|;
	requires WellformedBigNat(S);
	requires !zero(S);
	requires forall i:int :: 0<=i<|S.words|-1 ==> S.words[i]==0;
	ensures 0 <= INTERNAL_mul(32, |S.words|-1);
	ensures I(S) == INTERNAL_mul(power2(INTERNAL_mul(32, |S.words|-1)), S.words[|S.words|-1]);
{
	lemma_mul_nonnegative(32,|S.words|-1);
	if (|S.words|==1)
	{
		calc {
			I(S);
				{
					selectively_reveal_I(S);
				}
			INTERNAL_mul(I(BigNat_ctor(S.words[1..])),Width())+S.words[0];
				{
					selectively_reveal_I(BigNat_ctor([]));
				}
			INTERNAL_mul(0,Width())+S.words[0];
				{
					lemma_mul_basics_forall();
				}
			S.words[0];
				{ lemma_mul_identity(S.words[|S.words|-1]); }
			INTERNAL_mul(1, S.words[|S.words|-1]);
				{
					lemma_mul_annihilate(32);
					lemma_power2_0_is_1();
				}
			INTERNAL_mul(power2(INTERNAL_mul(32, 0)), S.words[|S.words|-1]);
			INTERNAL_mul(power2(INTERNAL_mul(32, |S.words|-1)), S.words[|S.words|-1]);
		}
	}
	else
	{
		var top:nat := S.words[|S.words|-1];
		var sub_S := BigNat_ctor(S.words[1..]);
		calc {
			I(S);
				{ selectively_reveal_I(S); }
			INTERNAL_mul(I(sub_S),Width())+S.words[0];
			INTERNAL_mul(I(sub_S),Width());
			INTERNAL_mul(I(sub_S),Width());
				{
					lemma_MakePower2(sub_S);
					assert sub_S.words[|sub_S.words|-1] == top;
				}
			INTERNAL_mul(INTERNAL_mul(power2(INTERNAL_mul(32, |sub_S.words|-1)), top),Width());
			INTERNAL_mul(INTERNAL_mul(power2(INTERNAL_mul(32, |sub_S.words|-1)), top),power2(32));
				{ lemma_mul_commutative(top, power2(INTERNAL_mul(32, |sub_S.words|-1))); }
			INTERNAL_mul(INTERNAL_mul(top, power2(INTERNAL_mul(32, |sub_S.words|-1))),power2(32));
				{ lemma_mul_associative(top, power2(INTERNAL_mul(32, |sub_S.words|-1)), power2(32)); }
			INTERNAL_mul(top, INTERNAL_mul(power2(INTERNAL_mul(32, |sub_S.words|-1)),power2(32)));
				{ lemma_exponentiation(INTERNAL_mul(32, |sub_S.words|-1), 32); }
			INTERNAL_mul(top, power2(INTERNAL_mul(32, |sub_S.words|-1)+32));
				{ lemma_mul_identity(32); }
			INTERNAL_mul(top, power2(INTERNAL_mul(32, |sub_S.words|-1)+INTERNAL_mul(32,1)));
				{ lemma_mul_distributive(32, |sub_S.words|-1, 1); }
			INTERNAL_mul(top, power2(INTERNAL_mul(32, |sub_S.words|-1+1)));
				// definition sub_S
			INTERNAL_mul(top, power2(INTERNAL_mul(32, |S.words|-1)));
				{ lemma_mul_commutative(power2(INTERNAL_mul(32, |S.words|-1)), top); }
			INTERNAL_mul(power2(INTERNAL_mul(32, |S.words|-1)), top);
			INTERNAL_mul(power2(INTERNAL_mul(32, |S.words|-1)), S.words[|S.words|-1]);
		}
	}
}

method MakePower2(thirtytwos:nat,ones:nat) returns (S:BigNat)
	requires 0<=ones<32;
	ensures WellformedBigNat(S);
	ensures |S.words| == thirtytwos + 1;
	ensures 0 <= INTERNAL_mul(32,thirtytwos);
	ensures I(S) == power2(INTERNAL_mul(32,thirtytwos)+ones);
	ensures forall i::0<=i<|S.words|-1 ==> S.words[i]==0;
	ensures S.words[|S.words|-1] == power2(ones);
{
	var vs:seq<int> := fill_sequence(0,thirtytwos);
	var small_power_2 := MakePower2Word32(ones);
	S := BigNat_ctor(vs + [small_power_2]);

	assert WellformedBigNat(S);
	assert !zero(S);
	assert forall i:int :: 0<=i<|S.words|-1 ==> S.words[i]==0;

	lemma_MakePower2(S);
	calc {
		I(S);
		INTERNAL_mul(power2(INTERNAL_mul(32, |S.words|-1)), S.words[|S.words|-1]);
		INTERNAL_mul(power2(INTERNAL_mul(32, |S.words|-1)), power2(ones));
			{ lemma_exponentiation(INTERNAL_mul(32, |S.words|-1), ones); }
		power2(INTERNAL_mul(32, |S.words|-1) + ones);
		power2(INTERNAL_mul(32,thirtytwos) + ones);
	}
}

method MakePower2Simple(exp:nat) returns (S:BigNat)
	requires Word32(exp);
	ensures WellformedBigNat(S);
	ensures I(S) == power2(exp);
{
	lemma_2to32();
	var thirtytwos,ones := Divide32(exp, 32);
	assert INTERNAL_mul(thirtytwos,32)+ones == exp;
//	if (ones==0)
//	{
//		var new_thirtytwos := thirtytwos - 1;
//		var new_ones := 32;
//		calc {
//			INTERNAL_mul(new_thirtytwos,32)+new_ones;
//			INTERNAL_mul(thirtytwos - 1,32)+32;
//				{ lemma_mul_basics_forall(); }
//			INTERNAL_mul(thirtytwos - 1,32)+INTERNAL_mul(32,1);
//				{ lemma_mul_is_commutative_forall(); }
//			INTERNAL_mul(32,thirtytwos - 1)+INTERNAL_mul(32,1);
//				{ lemma_mul_is_distributive_add_forall(); }
//			INTERNAL_mul(32,thirtytwos);
//			INTERNAL_mul(32,thirtytwos)+ones;
//				{ lemma_mul_is_commutative_forall(); }
//			INTERNAL_mul(thirtytwos,32)+ones;
//			exp;
//		}
//		thirtytwos := new_thirtytwos;
//		ones := new_ones;
//		assert INTERNAL_mul(thirtytwos,32)+ones == exp;
//	}
	S := MakePower2(thirtytwos,ones);
	calc {
		I(S);
		power2(INTERNAL_mul(32,thirtytwos)+ones);
			{ lemma_mul_is_commutative_forall(); }
		power2(INTERNAL_mul(thirtytwos,32)+ones);
		power2(exp);
	}
}

lemma lemma_BigNatWordShift_(A:BigNat, R:BigNat, w:nat)
	decreases w;
	requires WellformedBigNat(A);
	requires nonzero(A);
	requires WellformedBigNat(R);
	requires |R.words| == |A.words|+w;
	requires forall i :: 0<=i<w ==> R.words[i] == 0;
	requires forall i :: 0<=i<|A.words| ==> A.words[i] == R.words[w+i];
	ensures 0<=INTERNAL_mul(32,w);
	ensures I(R) == INTERNAL_mul(I(A), power2(INTERNAL_mul(32,w)));
{
	lemma_mul_nonnegative(32,w);
	if (w==0)
	{
		calc {
			I(R);
				{ assert R.words == A.words; }
			I(A);
				{ lemma_mul_identity(I(A)); }
			INTERNAL_mul(I(A), 1);
				{ lemma_power2_0_is_1(); }
			INTERNAL_mul(I(A), power2(0));
				{ lemma_mul_annihilate(32); }
			INTERNAL_mul(I(A), power2(INTERNAL_mul(32,0)));
			INTERNAL_mul(I(A), power2(INTERNAL_mul(32,w)));
		}
	}
	else
	{
		var sub_A:BigNat := BigNat_ctor([0]+A.words);
		assert sub_A.words[|sub_A.words|-1] == A.words[|A.words|-1] > 0;
		assert WellformedBigNat(sub_A);
		forall (i | 0<=i<|sub_A.words|)
			ensures sub_A.words[i] == R.words[w-1+i];
		{
			if (i==0)
			{
				assert sub_A.words[i] == 0 == R.words[w-1+i];
			}
			else
			{
				calc {
					sub_A.words[i];
					A.words[i-1];
					R.words[w+i-1];
				}
			}
		}
		calc {
			I(R);
				{ lemma_BigNatWordShift_(sub_A, R, w-1); }
			INTERNAL_mul(I(sub_A), power2(INTERNAL_mul(32,w-1)));
				{ selectively_reveal_I(sub_A); }
			INTERNAL_mul(INTERNAL_mul(I(BigNat_ctor(sub_A.words[1..])),Width()), power2(INTERNAL_mul(32,w-1)));
			INTERNAL_mul(INTERNAL_mul(I(A),Width()), power2(INTERNAL_mul(32,w-1)));
			INTERNAL_mul(INTERNAL_mul(I(A),power2(32)), power2(INTERNAL_mul(32,w-1)));
				{ lemma_mul_associative(I(A),power2(32),power2(INTERNAL_mul(32,w-1))); }
			INTERNAL_mul(I(A),INTERNAL_mul(power2(32), power2(INTERNAL_mul(32,w-1))));
				{ lemma_exponentiation(32, INTERNAL_mul(32,w-1)); }
			INTERNAL_mul(I(A),power2(32+INTERNAL_mul(32,w-1)));
				{ lemma_mul_identity(32); }
			INTERNAL_mul(I(A),power2(INTERNAL_mul(32,1)+INTERNAL_mul(32,w-1)));
				{ lemma_mul_distributive(32,1,w-1); }
			INTERNAL_mul(I(A),power2(INTERNAL_mul(32,w)));
		}
	}
}

method BigNatWordShift_(A:BigNat, ghost ac:nat, w:nat) returns (R:BigNat, ghost rc:nat)
	requires WellformedBigNat(A);
	requires nonzero(A);
	requires BitCount(A,ac);
	requires ac+INTERNAL_mul(32,w) < Width();
	ensures 0<=INTERNAL_mul(32,w);
	ensures WellformedBigNat(R);
	ensures I(R) == INTERNAL_mul(I(A), power2(INTERNAL_mul(32,w)));
	ensures BitCount(R,rc);
	ensures rc == ac+INTERNAL_mul(32,w);
{
	lemma_mul_nonnegative(32,w);
	var vs:seq<int> := fill_sequence(0,w);
	R := BigNat_ctor(vs + A.words);
	rc := ac + INTERNAL_mul(32,w);
	assert WellformedBigNat(R);
	lemma_BigNatWordShift_(A, R, w);

	calc ==> {
		!zero(A);
			{ lemma_zero_bits(A,ac); }
		ac>0;
	}

	assert rc>0;
	assert !(rc==0) && !zero(R);
	assert rc==0 <==> zero(R);

	if (0 == w)
	{
		assert |vs|==0;
		assert R.words == vs + A.words == A.words;
		assert R==A;
		lemma_mul_annihilate(32);
		assert rc == ac;
	}
	else
	{
		lemma_mul_strictly_positive_forall();
		assert 0 < INTERNAL_mul(32,w);
		calc ==> {
			power2(ac-1) <= I(A) < power2(ac);
				{
					lemma_mul_left_inequality(power2(INTERNAL_mul(32,w)), power2(ac-1), I(A));
					lemma_mul_left_inequality(power2(INTERNAL_mul(32,w)), I(A), power2(ac));
				}
			INTERNAL_mul(power2(INTERNAL_mul(32,w)), power2(ac-1)) <= INTERNAL_mul(power2(INTERNAL_mul(32,w)), I(A)) < INTERNAL_mul(power2(INTERNAL_mul(32,w)), power2(ac));
				{
					lemma_exponentiation(INTERNAL_mul(32,w), ac-1);
					lemma_mul_commutative(power2(INTERNAL_mul(32,w)), I(A));
					lemma_exponentiation(INTERNAL_mul(32,w), ac);
				}
			power2(INTERNAL_mul(32,w)+ac-1) <= INTERNAL_mul(I(A), power2(INTERNAL_mul(32,w))) < power2(ac+INTERNAL_mul(32,w));
				// defn rc
			power2(rc-1) <= INTERNAL_mul(I(A), power2(INTERNAL_mul(32,w))) < power2(rc);
				// lemma_BigNatWordShift_ ensures
			power2(rc-1) <= I(R) < power2(rc);
			BitCount(R,rc);
		}
	}
}

//function IsBit(a:int)
//	{ a==0 || a==1 }
//
//function IsBitSeq(bs:seq<int>)
//	{ forall b in bs :: IsBit(b) }
//
//function BitsFor(A:BigNat, ac:nat, bits:seq<int>)
//	requires WellformedBigNat(A);
//	requires BitCount(A,ac);
//	requires IsBitSeq(bits);
//	{ forall i:int :: 0<=i<ac :: BigNatSelectBit(A, i) == bits[i]; }

function zero_seq(w:nat) : seq<int>
	decreases w;
	ensures w == |zero_seq(w)|;
	ensures forall i :: 0<=i<w ==> zero_seq(w)[i]==0;
{
	if (w==0) then [] else zero_seq(w-1)+[0]
}

method BigNatSmallBitShift_(A:BigNat, ghost ac:nat, s:nat) returns (R:BigNat, ghost rc:nat)
	requires WellformedBigNat(A);
	requires !zero(A);
	requires s < 32;
	requires BitCount(A,ac);
	requires ac+s < Width();
	ensures WellformedBigNat(R);
	ensures |R.words| <= |A.words|+1;
	ensures I(R) == INTERNAL_mul(I(A), power2(s));
	ensures BitCount(R,rc);
	ensures rc == ac+s;
{
	// This is a silly implementation -- we construct 2^s and call BigNatMul -- but
	// it has the benefit that we don't have to reason about shift operators, which is
	// a big ball of wax. TODO come back here and get rid of this quadratic operation!

	var S:BigNat := MakePower2(0, s);
	lemma_mul_annihilate(32);
	assert I(S) == power2(s);

	R := BigNatMul(A,S);
	rc := ac + s;
	calc {
		I(R);
		INTERNAL_mul(I(A), I(S));
		INTERNAL_mul(I(A), power2(INTERNAL_mul(32,0)+s));
			{ lemma_mul_annihilate(32); }
		INTERNAL_mul(I(A), power2(s));
	}

	calc ==> {
		I(A) < power2(ac);
			{ lemma_mul_left_inequality(I(S), I(A), power2(ac)); }
		INTERNAL_mul(I(S), I(A)) < INTERNAL_mul(I(S), power2(ac));
			{ lemma_mul_commutative(I(A), I(S)); }
		INTERNAL_mul(I(A), I(S)) < INTERNAL_mul(I(S), power2(ac));
		INTERNAL_mul(I(A), I(S)) < INTERNAL_mul(power2(s), power2(ac));
			{ lemma_exponentiation(s,ac); }
		INTERNAL_mul(I(A), I(S)) < power2(s+ac);
		I(R) < power2(rc);
	}
	
	if (rc>0)
	{
		calc ==> {
			power2(ac-1) <= I(A);
				{ lemma_mul_left_inequality(I(S), power2(ac-1), I(A)); }
			INTERNAL_mul(I(S), power2(ac-1)) <= INTERNAL_mul(I(S), I(A));
				{ lemma_mul_commutative(I(A), I(S)); }
			INTERNAL_mul(I(S), power2(ac-1)) <= INTERNAL_mul(I(A), I(S));
			INTERNAL_mul(power2(s), power2(ac-1)) <= INTERNAL_mul(I(A), I(S));
				{ lemma_exponentiation(s,ac-1); }
			power2(s+ac-1) <= INTERNAL_mul(I(A), I(S));
			power2(rc-1) <= I(R);
		}
	}
	assert BitCount(R,rc);

	calc ==> {
		true;
			{ lemma_word_bound(A); }
		I(A) < power2(INTERNAL_mul(32,|A.words|));
			{ lemma_mul_left_inequality(power2(s), I(A), power2(INTERNAL_mul(32,|A.words|))); }
		INTERNAL_mul(power2(s), I(A)) < INTERNAL_mul(power2(s), power2(INTERNAL_mul(32,|A.words|)));
			{
				lemma_mul_commutative(power2(s), I(A));
				assert I(R) == INTERNAL_mul(power2(s), I(A));
			}
		I(R) < INTERNAL_mul(power2(s), power2(INTERNAL_mul(32,|A.words|)));
			{ lemma_exponentiation(s, INTERNAL_mul(32,|A.words|)); }
		I(R) < power2(INTERNAL_mul(32,|A.words|)+s);
			{
				calc ==> {
					s < 32;
					INTERNAL_mul(32,|A.words|) + s < INTERNAL_mul(32,|A.words|) + 32;
						{ lemma_power2_strictly_increases(INTERNAL_mul(32,|A.words|) + s, INTERNAL_mul(32,|A.words|) + 32); }
					power2(INTERNAL_mul(32,|A.words|) + s) < power2(INTERNAL_mul(32,|A.words|) + 32);
					I(R) < power2(INTERNAL_mul(32,|A.words|) + 32);
						{ lemma_mul_identity(32); }
					I(R) < power2(INTERNAL_mul(32,|A.words|) + INTERNAL_mul(32,1));
						{ lemma_mul_distributive(32, |A.words|, 1); }
					I(R) < power2(INTERNAL_mul(32,|A.words| + 1));
				}
				lemma_mul_positive_forall();
				assert 0<=INTERNAL_mul(32,|A.words|+1);
			}
		I(R) < power2(INTERNAL_mul(32,|A.words|+1));
	}

	calc ==> {
		true;
			{ lemma_word_bound(R); }
		power2(INTERNAL_mul(32,|R.words|-1)) <= I(R);
			// by calc above
			{
				lemma_mul_positive_forall();
				assert 0<=INTERNAL_mul(32,|A.words|+1);
			}
		power2(INTERNAL_mul(32,|R.words|-1)) < power2(INTERNAL_mul(32,|A.words|+1));
			{ lemma_power2_monotonic_inverse(INTERNAL_mul(32,|R.words|-1), INTERNAL_mul(32,|A.words|+1)); }
		INTERNAL_mul(32,|R.words|-1) < INTERNAL_mul(32,|A.words|+1);
			{ lemma_mul_is_commutative_forall(); }
		INTERNAL_mul(|R.words|-1,32) < INTERNAL_mul(|A.words|+1,32);
			{ lemma_mul_strict_inequality_converse(|R.words|-1,|A.words|+1,32); }
		|R.words|-1 < |A.words|+1;
		|R.words| <= |A.words|+1;
	}
}

lemma thirty_two_isnt_so_big_after_all()
	ensures Word32(32);
{ reveal_power2(); }

method BigNatBitShift_(A:BigNat, ghost ac:nat, s:nat) returns (R:BigNat, ghost rc:nat)
	requires WellformedBigNat(A);
	requires nonzero(A);
	requires s < Width();
	requires BitCount(A,ac);
	requires ac+s < Width();
	ensures WellformedBigNat(R);
	ensures I(R) == INTERNAL_mul(power2(s), I(A));
	ensures BitCount(R,rc);
	ensures rc == ac+s;
{
	thirty_two_isnt_so_big_after_all();
	var thirtytwos:nat,ones:nat := Divide32(s,32);
	// Ensures INTERNAL_mul(thirtytwos,32) + ones == s;
	calc ==> {
			// requires
		ac + s < Width();
		ac + INTERNAL_mul(thirtytwos,32) + ones < Width();
			{ lemma_mul_nonnegative(thirtytwos,32); }
		ac + ones < Width();
	}
	var R_ones:BigNat,r1c:nat := BigNatSmallBitShift_(A, ac, ones);

	calc ==> {
		ac + INTERNAL_mul(thirtytwos,32) + ones < Width();
			// BigNatSmallBitShift_ ensures r1c == ac+ones;
		ac + INTERNAL_mul(thirtytwos,32) + r1c - ac < Width();
			{ lemma_mul_commutative(thirtytwos,32); }
			// and + math
		r1c + INTERNAL_mul(32,thirtytwos) < Width();
	}
	R,rc := BigNatWordShift_(R_ones, r1c, thirtytwos);

	calc {
		rc;
			// BigNatWordShift_ ensures
		r1c+INTERNAL_mul(32,thirtytwos);
			// BigNatSmallBitShift_ ensures
		ac+ones+INTERNAL_mul(32,thirtytwos);
			// Divide32 ensures
			{ lemma_mul_commutative(thirtytwos,32); }
		ac+s;
	}

	calc {
		I(R);
			// BigNatWordShift_ ensures
		INTERNAL_mul(I(R_ones), power2(INTERNAL_mul(32,thirtytwos)));
			// BigNatSmallBitShift_ ensures
		INTERNAL_mul(INTERNAL_mul(I(A), power2(ones)), power2(INTERNAL_mul(32,thirtytwos)));
			{ lemma_mul_associative(I(A), power2(ones), power2(INTERNAL_mul(32,thirtytwos))); }
		INTERNAL_mul(I(A), INTERNAL_mul(power2(ones), power2(INTERNAL_mul(32,thirtytwos))));
			{ lemma_exponentiation(ones,INTERNAL_mul(32,thirtytwos)); }
		INTERNAL_mul(I(A), power2(ones+INTERNAL_mul(32,thirtytwos)));
			{ lemma_mul_commutative(thirtytwos,32); }
		INTERNAL_mul(I(A), power2(INTERNAL_mul(thirtytwos,32)+ones));
			// Divide32 ensures
		INTERNAL_mul(I(A), power2(s));
			{ lemma_mul_commutative(I(A), power2(s)); }
		INTERNAL_mul(power2(s), I(A));
	}
}

lemma lemma_modesty_preservation(A:BigNat, ac:nat, B:BigNat, bc:nat)
	requires WellformedBigNat(A);
	requires BitCount(A,ac);
	requires ModestBigNatBits(B,bc);
	requires I(A) <= I(B);
	ensures ModestBigNatWords(A);
{
	calc ==> {
		ModestBigNatBits(B,bc);
			{ lemma_modesty_bit_value_equivalence(B,bc); }
		ModestBigNatValue(B);
		I(B) < KindaBigNat();
		I(A) < KindaBigNat();
		ModestBigNatValue(A);
			{ lemma_modesty_word_value_equivalence(A); }
		ModestBigNatWords(A);
	}
}

static lemma lemma_power2_monotonic_inverse(a:nat,b:nat)
	decreases a;
	requires power2(a)<=power2(b);
	ensures a<=b;
{
	if (a>b)
	{
		lemma_power2_strictly_increases(b,a);
		assert power2(a) > power2(b);
		assert false;
	}
	assert a<=b;
}

lemma lemma_ModestBigNatNremainder(N:BigNat, ghost nc:nat, D:BigNat, N_remainder:BigNat)
	requires ModestBigNatBits(N,nc);
	requires WellformedBigNat(D);
	requires WellformedBigNat(N_remainder);
	requires I(N)-I(D) == I(N_remainder);
	ensures ModestBigNatWords(N_remainder);
{
	calc ==> {
		true;
			{ lemma_modesty_bit_value_equivalence(N,nc); }
		I(N) < KindaBigNat();
			{ assert I(N_remainder) <= I(N); } // BigNatSub ensures
		I(N_remainder) < KindaBigNat();
		ModestBigNatValue(N_remainder);
			{ lemma_modesty_word_value_equivalence(N_remainder); }
		ModestBigNatWords(N_remainder);
	}
}

method bignum_one() returns (one:BigNat)
	ensures WellformedBigNat(one);
	ensures BitCount(one,1);
	ensures I(one)==1;
{
	reveal_I();
	one := BigNat_ctor([1]);
	lemma_2to32();

	selectively_reveal_I(one);
	selectively_reveal_I(BigNat_ctor([]));
	assert 0 == I(BigNat_ctor([]));
	lemma_mul_annihilate(Width());
	assert 1 == I(one);
	lemma_power2_0_is_1();
	assert power2(1-1) == 1;
	assert 1 <= 1;
	assert power2(1-1) <= I(one);
	lemma_power2_1_is_2();
	assert I(one) == 1 < 2 == power2(1);
	assert I(one) < power2(1);
}

method BigNatDivInductiveStep(N:BigNat, ghost nc:nat, D:BigNat, ghost dc:nat, s:nat, DS:BigNat) returns (Q:BigNat, R:BigNat)
	decreases I(N),false;
	requires ModestBigNatBits(N,nc);
	requires ModestBigNatBits(D,dc);
	requires nonzero(D);
	requires WellformedBigNat(DS);
	requires 0 < I(DS) <= I(N);
	requires I(DS) == INTERNAL_mul(power2(s), I(D));
	requires s+1<Width();
	ensures WellformedBigNat(Q);
	ensures WellformedBigNat(R);
	ensures I(R) < I(D);
	ensures INTERNAL_mul(I(Q),I(D)) + I(R) == I(N);
{
	// lemma here
	var subQ:BigNat;
	var N_remainder:BigNat := BigNatSub(N,DS);
	lemma_mul_positive_forall();

	lemma_ModestBigNatNremainder(N,nc,DS,N_remainder);
	lemma_modesty_bit_value_equivalence(D,dc);
	lemma_modesty_word_value_equivalence(D);

	subQ,R := BigNatDiv(N_remainder, D);
	var one:BigNat := bignum_one();

	assert 1+s < Width();

	var my_q:BigNat,qc:nat := BigNatBitShift_(one, 1, s);
	Q := BigNatAdd(subQ, my_q);
	calc
	{
			// mutual induction hypothesis:
		INTERNAL_mul(I(subQ),I(D)) + I(R) == I(N_remainder);
		INTERNAL_mul(I(subQ),I(D)) + I(R) == I(N) - I(DS);
		INTERNAL_mul(I(Q) - I(my_q),I(D)) + I(R) == I(N) - I(DS);
			{
				selectively_reveal_I(BigNat_ctor(one.words[1..]));
				lemma_mul_annihilate(Width());
				lemma_mul_identity(power2(s));
			}
		INTERNAL_mul(I(Q) - power2(s),I(D)) + I(R) == I(N) - I(DS);
		INTERNAL_mul(I(Q) - power2(s),I(D)) + I(R) == I(N) - INTERNAL_mul(power2(s),I(D));
			{ lemma_mul_commutative(I(D), I(Q) - power2(s)); }
		INTERNAL_mul(I(D), I(Q) - power2(s)) + I(R) == I(N) - INTERNAL_mul(power2(s),I(D));
			{ lemma_mul_distributive(I(D), I(Q), power2(s)); }
		INTERNAL_mul(I(D), I(Q)) - INTERNAL_mul(I(D),power2(s)) + I(R) == I(N) - INTERNAL_mul(power2(s),I(D));
			{ lemma_mul_commutative(I(D), power2(s)); }
		INTERNAL_mul(I(D), I(Q)) - INTERNAL_mul(I(D),power2(s)) + I(R) == I(N) - INTERNAL_mul(I(D),power2(s));
		INTERNAL_mul(I(D), I(Q)) + I(R) == I(N);
			{ lemma_mul_commutative(I(D), I(Q)); }
		INTERNAL_mul(I(Q), I(D)) + I(R) == I(N);
	}
}

lemma lemma_nbits(N:BigNat, D:BigNat, nc:nat, dc:nat)
	requires WellformedBigNat(N);
	requires WellformedBigNat(D);
	requires nonzero(N);
	requires nonzero(D);
	requires I(N) < power2(nc);
	requires dc>0 ==> power2(dc-1) <= I(D);
	requires nc < dc;
	ensures I(N) < I(D);
{
	lemma_power2_increases(nc,dc-1);
}

method BigNatDivBaseCase(N:BigNat, D:BigNat) returns (Q:BigNat, R:BigNat)
	requires WellformedBigNat(N);
	requires WellformedBigNat(D);
	requires I(N) < I(D);
	ensures WellformedBigNat(Q);
	ensures WellformedBigNat(R);
	ensures I(R) < I(D);
	ensures INTERNAL_mul(I(Q),I(D)) + I(R) == I(N);
{
	R := N;
	Q := BigNatZero();
	assert(I(Q)==0);

	calc
	{
		INTERNAL_mul(I(Q),I(D)) + I(R);
		INTERNAL_mul(0,I(D)) + I(R);
			{ lemma_mul_annihilate(I(D)); }
		0 + I(R);
		I(R);
		I(N);
	}
}

method BigNatDiv(N:BigNat, D:BigNat) returns (Q:BigNat, R:BigNat)
	decreases I(N),true;
	requires ModestBigNatWords(N);
	requires ModestBigNatWords(D);
	requires nonzero(D);
	ensures WellformedBigNat(Q);
	ensures WellformedBigNat(R);
	ensures I(R) < I(D);
	ensures INTERNAL_mul(I(Q),I(D)) + I(R) == I(N);
{
	lemma_mul_positive_forall();
	if (zero(N))
	{
		Q:=BigNatZero();
		R:=BigNatZero();
		lemma_mul_annihilate(I(D));
	}
	else
	{
		var nc:nat :=BigNatCountBits(N);

		lemma_modesty_word_value_equivalence(N);
		lemma_modesty_bit_value_equivalence(N,nc);
		assert ModestBigNatBits(N,nc);
		
		var dc:nat :=BigNatCountBits(D);

		lemma_modesty_word_value_equivalence(D);
		lemma_modesty_bit_value_equivalence(D,dc);
		assert ModestBigNatBits(D,dc);

		if (nc < dc)
		{
			lemma_nbits(N,D,nc,dc);
			assert I(N) < I(D);
			Q,R := BigNatDivBaseCase(N,D);
		}
		else
		{
			var s:nat := nc - dc;
			assert s+1<Width();

			var DS:BigNat,dsc:nat := BigNatBitShift_(D,dc,s);
			var ds_too_big:bool := BigNatLt(N,DS);
			if (ds_too_big)
			{
				assert (I(N) < I(DS));	// Defn BigNatLt
				if (s==0) {
					lemma_power2_0_is_1();
					assert power2(s)==1;
					lemma_mul_identity(I(D));
					assert I(DS)==I(D);
					assert(I(N) < I(DS) <= I(D));
					Q,R := BigNatDivBaseCase(N,D);
				}
				else
				{
					DS,dsc := BigNatBitShift_(D,dc,s-1);

					calc {
						I(DS);
						INTERNAL_mul(power2(s-1), I(D));
						<=	{ lemma_mul_left_inequality(power2(s-1), I(D), power2(dc)-1); }
						INTERNAL_mul(power2(s-1), power2(dc)-1);
							{ lemma_mul_distributive(power2(s-1), power2(dc), 1); }
						INTERNAL_mul(power2(s-1), power2(dc)) - INTERNAL_mul(power2(s-1), 1);
							{ lemma_exponentiation(s-1, dc); }
						power2((s-1)+dc) - INTERNAL_mul(power2(s-1), 1);
							// additive arithmetic on assignment of s
						power2(nc-dc-1+dc) - INTERNAL_mul(power2(s-1), 1);
						power2(nc-1) - INTERNAL_mul(power2(s-1), 1);
						<= power2(nc-1);
						<= I(N);
					}

					Q,R := BigNatDivInductiveStep(N,nc,D,dc,s-1,DS);
				}
			}
			else
			{
				Q,R := BigNatDivInductiveStep(N,nc,D,dc,s,DS);
			}
		}
	}
}
