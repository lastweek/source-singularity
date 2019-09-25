include "../../../Trusted/Spec/Assembly.dfy"
include "BigNatCore.dfy"

//////////////////////////////////////////////////////////////////////////////
// Ah, the V() machinery. I()'s evil twin, that doesn't require
// Wellformedness (leading zeros are okay). And we don't pack/unpack into
// the BigNat datatype. It's certainly conceivable that I could redefine I to
// not require the leading-nonzero-word part of wellformedness, and use I
// instead of V in this group of lemmas.
//////////////////////////////////////////////////////////////////////////////

static function {:hidden} V(vs:seq<int>) : int
{
	if (|vs|==0) then
		0
	else
		INTERNAL_mul(Width(), V(vs[1..])) + vs[0]
}

static lemma selectively_reveal_V(vs:seq<int>)
	ensures V(vs) ==
		if (|vs|==0) then
			0
		else
			INTERNAL_mul(Width(), V(vs[1..]))+vs[0];
{
	reveal_V();
}

static lemma lemma_V_I(A:BigNat)
	decreases |A.words|;
	requires WellformedBigNat(A);
	ensures I(A) == V(A.words);
{
	if (zero(A))
	{
		reveal_V();
		assert I(A) == 0 == V(A.words);
	}
	else
	{
		lemma_V_I(hi(A));
		reveal_V();
		reveal_V();
		calc {
			I(A);
				{ reveal_I(); }
			INTERNAL_mul(I(hi(A)),Width()) + lo(A);
				{ lemma_mul_is_commutative(I(hi(A)), Width()); }
			INTERNAL_mul(Width(), I(hi(A))) + lo(A);
			INTERNAL_mul(Width(), V(hi(A).words)) + lo(A);
			V(A.words);
		}
	}
}

static lemma lemma_V_power(ls:seq<int>, hs:seq<int>)
	decreases |ls|;
	ensures INTERNAL_mul(32,|ls|) >= 0;
	ensures V(ls+hs) == INTERNAL_mul(power2(INTERNAL_mul(32,|ls|)), V(hs)) + V(ls);
{
	lemma_mul_left_inequality(32,0,|ls|);
	lemma_mul_basics(32);

	if (|ls|==0)
	{
		assert ls+hs == hs;
		calc {
			INTERNAL_mul(power2(INTERNAL_mul(32,|ls|)), V(hs)) + V(ls);
			INTERNAL_mul(power2(INTERNAL_mul(32,0)), V(hs)) + V(ls);
				{ lemma_mul_basics(32); }
			INTERNAL_mul(power2(0), V(hs)) + V(ls);
				{ lemma_power2_0_is_1(); }
			INTERNAL_mul(1, V(hs)) + V(ls);
				{ lemma_mul_basics(V(hs)); }
			V(hs) + V(ls);
				{ reveal_V(); }
			V(hs);
			V(ls+hs);
		}
	}
	else
	{
		lemma_V_power(ls[1..], hs);
		assert V(ls[1..]+hs) == INTERNAL_mul(power2(INTERNAL_mul(32,|ls|-1)), V(hs)) + V(ls[1..]);

		calc {
			true;
				{ selectively_reveal_V(ls+hs); }
			V(ls+hs) == INTERNAL_mul(Width(), V((ls+hs)[1..])) + (ls+hs)[0];
				{ assert (ls+hs)[1..] == ls[1..]+hs; }
			V(ls+hs) == INTERNAL_mul(Width(), V(ls[1..]+hs)) + (ls+hs)[0];
				{ assert (ls+hs)[0] == ls[0]; }
			V(ls+hs) == INTERNAL_mul(Width(), V(ls[1..]+hs)) + ls[0];
			V(ls+hs) == INTERNAL_mul(Width(), INTERNAL_mul(power2(INTERNAL_mul(32,|ls|-1)), V(hs)) + V(ls[1..])) + ls[0];
			V(ls+hs) == INTERNAL_mul(power2(32), INTERNAL_mul(power2(INTERNAL_mul(32,|ls|-1)), V(hs)) + V(ls[1..])) + ls[0];
				{ lemma_mul_is_distributive_add(power2(32), INTERNAL_mul(power2(INTERNAL_mul(32,|ls|-1)), V(hs)),V(ls[1..])); }
			V(ls+hs) == INTERNAL_mul(power2(32), INTERNAL_mul(power2(INTERNAL_mul(32,|ls|-1)), V(hs)))
					+ INTERNAL_mul(power2(32), V(ls[1..])) + ls[0];
				{ lemma_mul_is_associative(power2(32), power2(INTERNAL_mul(32,|ls|-1)), V(hs)); }
			V(ls+hs) == INTERNAL_mul(INTERNAL_mul(power2(32), power2(INTERNAL_mul(32,|ls|-1))), V(hs))
					+ INTERNAL_mul(power2(32), V(ls[1..])) + ls[0];
				{ lemma_power2_adds(32, INTERNAL_mul(32,|ls|-1)); }
			V(ls+hs) == INTERNAL_mul(power2(32+INTERNAL_mul(32,|ls|-1)), V(hs)) + INTERNAL_mul(power2(32), V(ls[1..])) + ls[0];
				{ lemma_mul_basics(32); }
			V(ls+hs) == INTERNAL_mul(power2(INTERNAL_mul(32,1)+INTERNAL_mul(32,|ls|-1)), V(hs)) + INTERNAL_mul(power2(32), V(ls[1..])) + ls[0];
				{ lemma_mul_is_distributive_add(32,1,|ls|-1); }
			V(ls+hs) == INTERNAL_mul(power2(INTERNAL_mul(32,|ls|)), V(hs)) + INTERNAL_mul(power2(32), V(ls[1..])) + ls[0];
				{ reveal_V(); }
			V(ls+hs) == INTERNAL_mul(power2(INTERNAL_mul(32,|ls|)), V(hs)) + V(ls);
		}
	}
}

static lemma lemma_V_singleton(s:seq<int>)
	requires |s|==1;
	ensures V(s) == s[0];
{
	reveal_V();
	lemma_mul_basics(Width());
}

static lemma lemma_V_upper_bound(s:seq<int>)
	decreases |s|;
	requires WordSeq(s);
	ensures INTERNAL_mul(32,|s|) >= 0;
	ensures V(s) <= power2(INTERNAL_mul(32,|s|))-1;
{
	reveal_V();
	if (|s|==0)
	{
		lemma_power2_0_is_1();
		lemma_mul_basics(32);
	}
	else
	{
		lemma_mul_positive_forall();
		calc {
			V(s);
			==	{ selectively_reveal_V(s); }
			INTERNAL_mul(Width(), V(s[1..])) + s[0];
			<=  {
				lemma_V_upper_bound(s[1..]);
				assert V(s[1..]) <= power2(INTERNAL_mul(32,|s|-1))-1;
				lemma_mul_left_inequality(Width(), V(s[1..]), power2(INTERNAL_mul(32,|s|-1))-1);
				}
			INTERNAL_mul(Width(), power2(INTERNAL_mul(32,|s|-1))-1) + s[0];
			<=
			INTERNAL_mul(Width(), power2(INTERNAL_mul(32,|s|-1))-1) + power2(32) - 1;
			INTERNAL_mul(Width(), power2(INTERNAL_mul(32,|s|-1))-1) + Width() - 1;
				{ lemma_mul_basics(Width()); }
			INTERNAL_mul(Width(), power2(INTERNAL_mul(32,|s|-1))-1) + INTERNAL_mul(Width(),1) - 1;
				{ lemma_mul_is_distributive_add(Width(), power2(INTERNAL_mul(32,|s|-1))-1, 1); }
			INTERNAL_mul(Width(), power2(INTERNAL_mul(32,|s|-1))-1+1) - 1;
			INTERNAL_mul(Width(), power2(INTERNAL_mul(32,|s|-1))) - 1;
			INTERNAL_mul(power2(32), power2(INTERNAL_mul(32,|s|-1))) - 1;
				{ lemma_power2_adds(32, INTERNAL_mul(32,|s|-1)); }
			power2(32 + INTERNAL_mul(32,|s|-1)) - 1;
				{ lemma_mul_basics(32); }
			power2(INTERNAL_mul(32,1) + INTERNAL_mul(32,|s|-1)) - 1;
				{ lemma_mul_is_distributive_add(32, 1, |s|-1); }
			power2(INTERNAL_mul(32,|s|)) - 1;
		}
	}
}

static lemma lemma_V_lower_bound(s:seq<int>)
	requires WordSeq(s);
	ensures 0 <= V(s);
{
	reveal_V();
	if (|s|==0)
	{ }
	else
	{
		lemma_V_lower_bound(s[1..]);
		reveal_V();
		lemma_mul_left_inequality(Width(), 0, V(s[1..]));
		lemma_mul_basics(Width());
	}
}

static lemma lemma_V_high_zeros(s:seq<int>)
	requires |s|>0;
	requires s[|s|-1]==0;
	ensures V(s) == V(s[..|s|-1]);
{
	if (|s|==1)
	{
		calc {
			V(s);
				{ selectively_reveal_V(s); }
			INTERNAL_mul(Width(), V(s[1..]))+s[0];
				{ assert s[1..] == []; }
			INTERNAL_mul(Width(), V([]))+s[0];
				{ selectively_reveal_V([]); }
			INTERNAL_mul(Width(), 0)+s[0];
				{ lemma_mul_basics_forall(); }
			s[0];
			s[|s|-1];
			0;
				{ selectively_reveal_V([]); }
			V([]);
				{ assert s[..|s|-1] == []; }
			V(s[..|s|-1]);
		}
	}
	else
	{
		var hi_s := s[1..];
		var trunc_s := s[..|s|-1];

		calc {
			// 2,3,0,0
			V(s);
				{ selectively_reveal_V(s); }
			// 3,0,0*w + 2
			INTERNAL_mul(Width(), V(hi_s))+s[0];
				{ lemma_V_high_zeros(hi_s); }
			// 3,0*w + 2
			INTERNAL_mul(Width(), V(hi_s[..|hi_s|-1]))+s[0];
				calc {
					hi_s[..|hi_s|-1];
					s[1..][..|s[1..]|-1];
					s[1..][..|s|-2];
					s[1..|s|-1];
					s[..|s|-1][1..];
					trunc_s[1..];
				}
			INTERNAL_mul(Width(), V(trunc_s[1..])) + s[0];
			INTERNAL_mul(Width(), V(trunc_s[1..])) + trunc_s[0];
			// 2,3,0
				{ selectively_reveal_V(trunc_s); }
			V(trunc_s);
			V(s[..|s|-1]);
		}
	}
}

static function {:hidden} TruncatingBigNatCtor_def(ss:seq<int>) : BigNat
	decreases |ss|;
	requires WordSeq(ss);
{
	if (|ss|==0) then
		BigNat_ctor([])
	else if (ss[|ss|-1] > 0) then
		BigNat_ctor(ss)
	else
		TruncatingBigNatCtor_def(ss[..|ss|-1])
}

static function TruncatingBigNatCtor(ss:seq<int>) : BigNat
	requires WordSeq(ss);
	ensures WellformedBigNat(TruncatingBigNatCtor(ss));
	ensures V(ss) == I(TruncatingBigNatCtor(ss));
	ensures |TruncatingBigNatCtor(ss).words| <= |ss|;
{
	lemma_TruncatingBigNatCtor(ss,TruncatingBigNatCtor_def(ss));
	TruncatingBigNatCtor_def(ss)
}

static method TruncatingBigNatCtor_impl(ss:seq<int>) returns(N:BigNat)
    requires WordSeq(ss);
    ensures N == TruncatingBigNatCtor(ss);
{
    reveal_TruncatingBigNatCtor_def();
    var k := |ss|;
    assert ss == ss[..k];
    while (k > 0)
        invariant 0 <= k <= |ss|;
        invariant TruncatingBigNatCtor_def(ss) == TruncatingBigNatCtor_def(ss[..k]);
        invariant WordSeq(ss[..k]);
    {
        k := k - 1;
        if (ss[k] > 0)
        {
            N := BigNat_ctor(ss[..k+1]);
            return;
        }
        assert ss[..k+1][..k] == ss[..k];
    }
    N := BigNat_ctor([]);
}

static lemma lemma_TruncatingBigNatCtor(ss:seq<int>,N:BigNat)
	decreases |ss|;
	requires WordSeq(ss);
	requires N == TruncatingBigNatCtor_def(ss);
	ensures WellformedBigNat(N);
	ensures V(ss) == I(N);
	ensures |N.words| <= |ss|;
{
	reveal_TruncatingBigNatCtor_def();

	if (|ss|==0)
	{
		assert N == BigNat_ctor([]);
		calc {
			I(N);
				{ reveal_I(); }
			0;
				{ reveal_V(); }
			V(ss);
		}
	}
	else if (ss[|ss|-1] > 0)
	{
		assert N == BigNat_ctor(ss);
		lemma_V_I(N);
	}
	else
	{
		assert N == TruncatingBigNatCtor_def(ss[..|ss|-1]);
		lemma_TruncatingBigNatCtor(ss[..|ss|-1],N);
		calc {
			I(N);
			V(ss[..|ss|-1]);
				{ lemma_V_high_zeros(ss); }
			V(ss);
		}
	}
}

static lemma lemma_TruncatingBigNat_alignment(ss:seq<int>,N:BigNat)
	decreases |ss|;
	requires WordSeq(ss);
	requires N == TruncatingBigNatCtor(ss);
	ensures forall i :: 0<=i<|N.words| ==> N.words[i] == ss[i];
	ensures forall i :: |N.words|<=i<|ss| ==> ss[i] == 0;
{
	reveal_TruncatingBigNatCtor_def();

	if (|ss|==0)
	{
		selectively_reveal_V(ss);
		assert V(ss) == 0;
		assert I(N) == 0;
		assert zero(N);
	}
	else if (ss[|ss|-1] > 0)
	{
		assert N == BigNat_ctor(ss);
		assert |N.words| == |ss|;
	}
	else
	{
		assert N == TruncatingBigNatCtor(ss[..|ss|-1]);
		forall (i | 0<=i<|N.words|)
			ensures N.words[i] == ss[i];
		{
			calc {
				N.words[i];
					{ lemma_TruncatingBigNat_alignment(ss[..|ss|-1], N); }
				ss[..|ss|-1][i];
				ss[i];
			}
		}
		forall (i | |N.words|<=i<|ss|)
			ensures ss[i] == 0;
		{
			if (i<|ss|-1)
			{
				calc {
					ss[i];
					ss[..|ss|-1][i];
						{ lemma_TruncatingBigNat_alignment(ss[..|ss|-1], N); }
					0;
				}
			}
		}
	}
}

static lemma lemma_TruncatingBigNat_hilo(ss:seq<int>)
	requires WordSeq(ss);
	requires |ss|>0;
	ensures I(TruncatingBigNatCtor(ss)) == I(TruncatingBigNatCtor(ss[1..]))*Width() + ss[0];
{
	calc {
		I(TruncatingBigNatCtor(ss));
		V(ss);
			{
				reveal_V();
				lemma_mul_is_commutative_forall();
			}
		V(ss[1..])*Width() + ss[0];
		I(TruncatingBigNatCtor(ss[1..]))*Width() + ss[0];
	}
}
