include "BigNatAdd.dfy"
include "BigNatCompare.dfy"

static lemma lemma_mul_zero()
	ensures forall x,y :: x==0 || y==0 ==> INTERNAL_mul(x,y) == 0;
{
	forall (x:int, y:int | x==0 || y==0)
		ensures INTERNAL_mul(x,y)==0;
	{
		if (x==0)
		{
			lemma_mul_basics(y);
			assert INTERNAL_mul(x,y) == 0;
		}
		else
		{
			assert y==0;
			lemma_mul_basics(x);
			lemma_mul_is_commutative(x,y);
			assert INTERNAL_mul(x,y) == 0;
		}
	}
}

lemma lemma_mul_monotonic(x:int, y:int)
	ensures (1 < x && 0 < y) ==> (y < INTERNAL_mul(x,y));
{ lemma_mul_properties(); }


//////////////////////////////////////////////////////////////////////////////

method SmallMul_(a:nat, b:nat) returns (s:BigNat)
	requires Word32(a);
	requires Word32(b);
	ensures WellformedBigNat(s);
	ensures I(s) == INTERNAL_mul(a,b);
{

	var l,h := Product32(a,b);
	if (l==0 && h==0)
	{
		lemma_mul_zero();
		s := BigNat_ctor([]);
		reveal_I();
	}
	else if (h==0)
	{
		s := BigNat_ctor([l]);
		reveal_I();
	}
	else
	{
		s := BigNat_ctor([l,h]);
		calc {
			I(s);
				{ reveal_I(); }
			INTERNAL_mul(I(BigNat_ctor(s.words[1..])), Width()) + l;
				{ reveal_I(); lemma_mul_zero(); }
			INTERNAL_mul(h, Width()) + l;
				// Product32 ensures
			INTERNAL_mul(a,b);
		}
	}
}

method BigNatLeftShift_(A:BigNat) returns (R:BigNat)
	requires WellformedBigNat(A);
	ensures WellformedBigNat(R);
	ensures I(R) == INTERNAL_mul(I(A), Width());
{
	if (zero(A))
	{
		lemma_mul_zero();
		R := A;
	}
	else
	{
		R := BigNat_ctor([0] + A.words);
		reveal_I();
	}
}

ghost method lemma_step1(b:int, ihiAW:int, loA:int)
	ensures INTERNAL_mul(b, ihiAW) + INTERNAL_mul(b,loA) == INTERNAL_mul(b, ihiAW + loA);
{
	lemma_mul_distributive(b, ihiAW, loA);
}

method BigNatSingleMul_(A:BigNat, b:nat) returns (R:BigNat)
	decreases |A.words|;
	requires WellformedBigNat(A);
	requires Word32(b);
	ensures WellformedBigNat(R);
	ensures INTERNAL_mul(I(A),b) == I(R);
{
	R := BigNatZero();
	calc {
		INTERNAL_mul(I(BigNatZero()),b);
		INTERNAL_mul(0,b);
			{ lemma_mul_zero(); }
		0;
		I(R);
	}
	var n := |A.words|;
	assert A.words[n..] == [];
	while (n > 0)
		invariant 0 <= n <= |A.words|;
		invariant WellformedBigNat(R);
		invariant I(R) == INTERNAL_mul(I(BigNat_ctor(A.words[n..])), b);	// induction hypothesis
	{
		ghost var hi_A := BigNat_ctor(A.words[n..]);
		ghost var ugly_expression := INTERNAL_mul(I(hi_A), Width());
    n := n - 1;
		ghost var hilo_A := BigNat_ctor(A.words[n..]);
		assert hi_A.words == hi(hilo_A).words;
		var sub_R := R;
		var parent:BigNat := BigNatLeftShift_(sub_R);
		var child:BigNat := SmallMul_(A.words[n], b);
		R := BigNatAdd(parent, child);

		calc {
			I(R);
			I(parent) + I(child);
			I(parent) + INTERNAL_mul(A.words[n],b);
			INTERNAL_mul(I(sub_R), Width()) + INTERNAL_mul(A.words[n],b);
			INTERNAL_mul(INTERNAL_mul(I(hi_A),b), Width()) + INTERNAL_mul(A.words[n],b);
				{ lemma_mul_commutative(I(hi_A),b); }
			INTERNAL_mul(INTERNAL_mul(b,I(hi_A)), Width()) + INTERNAL_mul(A.words[n],b);
				{ lemma_mul_associative(b, I(hi_A), Width()); }
			INTERNAL_mul(b,INTERNAL_mul(I(hi_A), Width())) + INTERNAL_mul(A.words[n],b);
				{ lemma_mul_commutative(b,A.words[n]); }
			INTERNAL_mul(b,ugly_expression) + INTERNAL_mul(b,A.words[n]);
				{ lemma_step1(b, ugly_expression, A.words[n]); }
			INTERNAL_mul(b,ugly_expression + A.words[n]);
				{ lemma_hilo(hilo_A); }
			INTERNAL_mul(b,I(hilo_A));
				{ lemma_mul_commutative(b,I(hilo_A)); }
			INTERNAL_mul(I(hilo_A),b);
		}
	}
	assert A.words[0..] == A.words;
}

method BigNatMul(A:BigNat, B:BigNat) returns (R:BigNat)
	decreases |B.words|;
	requires WellformedBigNat(A);
	requires WellformedBigNat(B);
	ensures WellformedBigNat(R);
	ensures INTERNAL_mul(I(A),I(B)) == I(R);
{
	if (zero(A))
	{
		lemma_mul_zero();
		R := A;
		return;
	}
	R := BigNatZero();
	var n := |B.words|;
	assert B.words[n..] == [];
	lemma_mul_zero();
	while (n > 0)
		invariant 0 <= n <= |B.words|;
		invariant WellformedBigNat(R);
		invariant I(R) == INTERNAL_mul(I(A), I(BigNat_ctor(B.words[n..])));	// induction hypothesis
	{
		ghost var hi_B := BigNat_ctor(B.words[n..]);
    n := n - 1;
		ghost var hilo_B := BigNat_ctor(B.words[n..]);
		assert hi_B.words == hi(hilo_B).words;
		var sub_R := R;
		var parent:BigNat := BigNatLeftShift_(sub_R);
		var child:BigNat := BigNatSingleMul_(A, B.words[n]);
		R := BigNatAdd(parent, child);

		calc
		{
			I(R);
			I(parent) + I(child);
			INTERNAL_mul(I(sub_R), Width()) + I(child);
			INTERNAL_mul(I(sub_R), Width()) + INTERNAL_mul(I(A), B.words[n]);
			INTERNAL_mul(INTERNAL_mul(I(A), I(hi_B)), Width()) + INTERNAL_mul(I(A), B.words[n]);
				{ lemma_mul_associative(I(A), I(hi_B), Width()); }
			INTERNAL_mul(I(A), INTERNAL_mul(I(hi_B), Width())) + INTERNAL_mul(I(A), B.words[n]);
				{ lemma_mul_distributive(I(A), INTERNAL_mul(I(hi_B), Width()), B.words[n]); }
			INTERNAL_mul(I(A), INTERNAL_mul(I(hi_B), Width()) + B.words[n]);
				{ lemma_hilo(hilo_B); }
			INTERNAL_mul(I(A), I(hilo_B));
		}
	}
	assert B.words[0..] == B.words;
}
