include "BigNatDiv.dfy"

datatype BigNum = BigNum_ctor(
	negate : bool,
	value : BigNat);

static function WellformedBigNum(A:BigNum) : bool
{
	WellformedBigNat(A.value)
		// disallow redundant zero (-0)
	&& (zero(A.value) ==> !A.negate)
}

static function BV(A:BigNum) : int
	requires WellformedBigNum(A);
	ensures (BV(A) < 0) <==> A.negate;
{
	if (A.negate) then
		-I(A.value)
	else
		I(A.value)
}

function method BigNumNegate(A:BigNum) : BigNum
	requires WellformedBigNum(A);
	ensures WellformedBigNum(BigNumNegate(A));
	ensures BV(BigNumNegate(A)) == -BV(A);
{
	if (zero(A.value)) then
		A
	else
		BigNum_ctor(!A.negate, A.value)
}

method BigNumAdd(A:BigNum, B:BigNum) returns (R:BigNum)
	decreases A.negate,B.negate;
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures WellformedBigNum(R);
	ensures BV(A)+BV(B) == BV(R);
{
	if (A.negate == B.negate)
	{
		var value:BigNat := BigNatAdd(A.value, B.value);
		assert I(value) == I(A.value) + I(B.value);
		R := BigNum_ctor(A.negate, value);
		if (A.negate)
		{
			assert B.negate;
			calc {
				BV(R);
				-I(R.value);
				-(I(A.value)+I(B.value));
				-I(A.value)-I(B.value);
				BV(A)+BV(B);
			}
		}
		else
		{
			assert !B.negate;
			calc {
				BV(R);
				I(R.value);
				I(A.value)+I(B.value);
				BV(A)+BV(B);
			}
		}
	}
	else if (A.negate)
	{
		assert !B.negate;
		R := BigNumAdd(B,A);
		calc {
			BV(R);
			BV(B) + BV(A);
			BV(A) + BV(B);
		}
	}
	else
	{
		// A - B
		R := BigNumSub(A,BigNumNegate(B));
		calc {
			BV(R);
			BV(A)-BV(BigNumNegate(B));
			BV(A)-(-BV(B));
			BV(A)+BV(B);
		}
	}
}

method BigNumSub(A:BigNum, B:BigNum) returns (R:BigNum)
	decreases A.negate,B.negate;
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures WellformedBigNum(R);
	ensures BV(A)-BV(B) == BV(R);
{
	if (B.negate)
	{
		// -A - -B == -A + B
		// A - -B == A + B
		R := BigNumAdd(A, BigNumNegate(B));
		calc {
			BV(R);
			BV(A) + BV(BigNumNegate(B));
			BV(A) + -BV(B);
			BV(A) - BV(B);
		}
	}
	else if (A.negate)
	{
		assert !B.negate;
		// -A - B == - (A + B)
		var value:BigNat := BigNatAdd(A.value, B.value);
		R := BigNum_ctor(true, value);
		calc {
			BV(R);
			-I(value);
			-(I(A.value) + I(B.value));
			-I(A.value) - I(B.value);
			BV(A) - BV(B);
		}
	}
	else
	{
		// A - B ==> this is the interesting case
		var negate:bool := BigNatLt(A.value,B.value);
		if (negate)
		{
			assert I(B.value) > I(A.value);
			var value:BigNat := BigNatSub(B.value, A.value);
			R := BigNum_ctor(negate, value);
			calc {
				BV(R);
				-I(value);
				-(I(B.value)-I(A.value));
				I(A.value)-I(B.value);
				BV(A) - BV(B);
			}
		}
		else
		{
			assert I(B.value) <= I(A.value);
			var value:BigNat := BigNatSub(A.value, B.value);
			R := BigNum_ctor(negate, value);
			calc {
				BV(R);
				I(value);
				I(A.value)-I(B.value);
				BV(A) - BV(B);
			}
		}
	}
}

method BigNumCmp(A:BigNum, B:BigNum) returns (c:Cmp)
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures (c==CmpLt) <==> (BV(A)  < BV(B));
	ensures (c==CmpEq) <==> (BV(A) == BV(B));
	ensures (c==CmpGt) <==> (BV(A)  > BV(B));
{
	if (A.negate)
	{
		if (!B.negate)
		{	// -A, B
			c := CmpLt;
			assert BV(A) < 0 <= BV(B);
		}
		else
		{	// -A,-B
			var nc := BigNatCmp(A.value,B.value);
			if (nc==CmpEq)
			{
				c := CmpEq;
				assert BV(A)==-I(A.value)==-I(B.value)==BV(B);
			}
			else if (nc==CmpLt)
			{
				c := CmpGt;
				assert BV(A)==-I(A.value) > -I(B.value)==BV(B);
			}
			else
			{
				c := CmpLt;
				assert BV(A)==-I(A.value) < -I(B.value)==BV(B);
			}
		}
	}
	else
	{
		if (B.negate)
		{	// A, -B
			c := CmpGt;
			assert BV(A) >= 0 > BV(B);
		}
		else
		{	// A, B
			c := BigNatCmp(A.value,B.value);
			if (c==CmpEq)
			{
				assert BV(A)==I(A.value)==I(B.value)==BV(B);
			}
			else if (c==CmpLt)
			{
				assert BV(A)==I(A.value)<I(B.value)==BV(B);
			}
			else
			{
				assert c==CmpGt;
				assert BV(A)==I(A.value)>I(B.value)==BV(B);
			}
		}
	}
}

method BigNumLt(A:BigNum, B:BigNum) returns (r:bool)
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures r <==> BV(A)<BV(B);
{
	var c := BigNumCmp(A,B);
	r := (c==CmpLt);
}

method BigNumLe(A:BigNum, B:BigNum) returns (r:bool)
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures r <==> BV(A)<=BV(B);
{
	var c := BigNumCmp(A,B);
	r := (c==CmpLt) || (c==CmpEq);
}

method BigNumEq(A:BigNum, B:BigNum) returns (r:bool)
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures r <==> BV(A)==BV(B);
{
	var c := BigNumCmp(A,B);
	r := (c==CmpEq);
}

method BigNumGe(A:BigNum, B:BigNum) returns (r:bool)
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures r <==> BV(A)>=BV(B);
{
	var c := BigNumCmp(A,B);
	r := (c==CmpGt) || (c==CmpEq);
}

method BigNumGt(A:BigNum, B:BigNum) returns (r:bool)
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures r <==> BV(A)>BV(B);
{
	var c := BigNumCmp(A,B);
	r := (c==CmpGt);
}

lemma lemma_mul_cancels_negatives(a:int, b:int)
	ensures a*b == (-a)*(-b);
{
	lemma_mul_properties();
}

method BigNumMul(A:BigNum, B:BigNum) returns (R:BigNum)
	requires WellformedBigNum(A);
	requires WellformedBigNum(B);
	ensures WellformedBigNum(R);
	ensures BV(A)*BV(B) == BV(R);
{
	if ((A.negate && B.negate)
		|| (!A.negate && !B.negate))
	{
		var value:BigNat := BigNatMul(A.value, B.value);
		R := BigNum_ctor(false, value);
		
		if (A.negate)
		{
			calc {
				BV(R);
				I(value);
				I(A.value) * I(B.value);
					{ lemma_mul_cancels_negatives(I(A.value), I(B.value)); }
				(-I(A.value)) * (-I(B.value));
				BV(A) * BV(B);
			}
		}
		else
		{
			calc {
				BV(R);
				I(value);
				I(A.value) * I(B.value);
				BV(A) * BV(B);
			}
		}
	}
	else if ((!A.negate && B.negate) || (A.negate && !B.negate))
	{
		if ((B.negate && zero(A.value))
			|| (A.negate && zero(B.value)))
		{
			// Hah! -7 * 0 --> can't return -0! Nice catch, Dafny.
			R := BigNum_ctor(false, BigNatZero());
			if (zero(A.value))
			{
				assert I(A.value)==0;
				calc {
					BV(A) * BV(B);
					I(A.value) * -I(B.value);
					INTERNAL_mul(I(A.value), -I(B.value));
					INTERNAL_mul(0, -I(B.value));
						{ lemma_mul_basics_forall(); }
					0;
					I(BigNatZero());
					BV(R);
				}
			}
			else
			{
				assert I(B.value)==0;
				calc {
					BV(A) * BV(B);
					(-I(A.value)) * I(B.value);
					INTERNAL_mul(-I(A.value), I(B.value));
					INTERNAL_mul(-I(A.value), 0);
						{ lemma_mul_basics_forall(); }
					0;
					I(BigNatZero());
					BV(R);
				}
			}
		}
		else
		{
			var value:BigNat := BigNatMul(A.value, B.value);
			R := BigNum_ctor(true, value);

			calc ==> {
				!zero(A.value) && !zero(B.value);
				I(A.value)!=0 && I(B.value)!=0;
					{ lemma_mul_nonzero_forall(); }
				I(A.value)*I(B.value) != 0;
				I(value) != 0;
				!zero(value);
				WellformedBigNum(R);
			}

			if (A.negate)
			{
				calc {
					BV(R);
					-I(value);
					-(I(A.value) * I(B.value));
						{ lemma_mul_properties(); }
					(-I(A.value)) * I(B.value);
					BV(A) * BV(B);
				}
			}
			else
			{
				calc {
					BV(R);
					-I(value);
					-(I(A.value) * I(B.value));
						{ lemma_mul_properties(); }
					I(A.value) * (-(I(B.value)));
					BV(A) * BV(B);
				}
			}
		}
	}
}

predicate ModestBigNumWords(A:BigNum)
{
	WellformedBigNum(A)
	&& ModestBigNatWords(A.value)
}

method BigNumDiv(N:BigNum, D:BigNum) returns (Q:BigNum, R:BigNum)
	requires ModestBigNumWords(N);
	requires ModestBigNumWords(D);
	requires nonzero(D.value);
// TODO BigNumDiv should cope with negative D, N, matching /,% semantics
	requires BV(N) >= 0;
	requires BV(D) >= 0;
	ensures WellformedBigNum(Q);
	ensures WellformedBigNum(R);
	ensures 0 <= BV(R) < BV(D);	// negative D inverts this condition.
	ensures BV(Q)*BV(D) + BV(R) == BV(N);
// TODO might be nice to tie to /, %.
//	ensures BV(N) / BV(D) == BV(Q);
//	ensures BV(N) % BV(D) == BV(R);
{

//	if (D.negate)
//	{
//		var q:BigNat,r:BigNat := BigNatDiv(N, BigNumNegate(D));
//		Q := BigNum_ctor(true, q);
//		R := BigNum_ctor(false, r);
//	}

	var q:BigNat,r:BigNat := BigNatDiv(N.value, D.value);
	Q := BigNum_ctor(false, q);
	R := BigNum_ctor(false, r);

	calc ==> {
		0 <= I(r) < I(D.value);
		0 <= BV(R) < BV(D);
	}
	calc ==> {
		I(q)*I(D.value) + I(r) == I(N.value);
		BV(Q)*BV(D) + BV(R) == BV(N);
	}
}

function method MakeSmallLiteralBigNum_def(x:nat) : BigNum
	requires x < Width();
	ensures WellformedBigNum(MakeSmallLiteralBigNum_def(x));
{
	if (x==0) then
		BigNum_ctor(false, BigNat_ctor([]))
	else
		BigNum_ctor(false, BigNat_ctor([x]))
}

lemma lemma_MakeSmallLiteralBigNum(x:nat)
	requires x < Width();
	ensures BV(MakeSmallLiteralBigNum_def(x)) == x;
{
	var R:BigNum := MakeSmallLiteralBigNum_def(x);
	assert WellformedBigNum(R);
	assert WellformedBigNat(R.value);
	if (x==0)
	{
		assert zero(R.value);
		assert BV(R) == 0;
	}
	else
	{
		assert R.value.words == [x];
		calc {
			I(R.value);
				{ reveal_I(); }
			INTERNAL_mul(I(BigNat_ctor(R.value.words[1..])),Width())+R.value.words[0];
			INTERNAL_mul(I(BigNat_ctor([])),Width())+R.value.words[0];
				{
					reveal_I();
					lemma_mul_basics_forall();
				}
			R.value.words[0];
			x;
		}
		assert I(R.value) == x;
		assert BV(R) == x;
	}
}

function method MakeSmallLiteralBigNum(x:nat) : BigNum
	requires x < Width();
	ensures WellformedBigNum(MakeSmallLiteralBigNum(x));
	ensures BV(MakeSmallLiteralBigNum(x))==x;
{
	lemma_MakeSmallLiteralBigNum(x);
	MakeSmallLiteralBigNum_def(x)
}
