include "../../BigNum/BigNatDiv.dfy"
include "../../BigNum/BigNum.dfy"
include "division.dfy"

predicate opposing_signs(x:int, y:int)
{
	x==0
	|| y==0
	|| (x<0 <==> y>=0)
}

method extended_gcd(A:BigNat, B:BigNat) returns (X:BigNum, Y:BigNum)
	decreases I(A);
	requires ModestBigNatWords(A);
	requires ModestBigNatWords(B);
	requires 1<=I(A);
	requires I(B) < I(A);
	ensures WellformedBigNum(X);
	ensures ModestBigNatWords(X.value);
	ensures WellformedBigNum(Y);
	ensures ModestBigNatWords(Y.value);
	ensures 0 <= I(A)*BV(X) + I(B)*BV(Y);
	ensures is_gcd(I(A), I(B), I(A)*BV(X) + I(B)*BV(Y));

	// These size constraints are used to show downstream modesty,
	// but also to show that the solution for 'd' is within a phi of [0,phi).
	ensures (BV(X)==1 && BV(Y)==0) || -I(B) <= BV(X) <= I(B);
	ensures -I(A) <= BV(Y) <= I(A);
	ensures opposing_signs(BV(X), BV(Y));
	ensures BV(X)!=0 || BV(Y)!=0;
{
	if (zero(B))
	{
		X := MakeSmallLiteralBigNum(1);
		Y := MakeSmallLiteralBigNum(0);

		ghost var gcd := I(A);
		lemma_anything_divides_itself(gcd);
		lemma_anything_divides_zero(gcd);
		
		calc {
			I(A)*BV(X) + I(B)*BV(Y);
			mul(I(A),1) + mul(I(B),0);
				{ lemma_mul_basics_forall(); }
			I(A);
			gcd;
		}
		// wikipedia proves cd, but not g!
		lemma_nothing_bigger_divides(I(A));
		assert is_gcd(I(A), I(B), gcd);
	}
	else
	{
		var Q:BigNat,R:BigNat := BigNatDiv(A,B);
		assert I(R) < I(B);
		lemma_modesty_word_value_equivalence(B);
		lemma_modesty_word_value_equivalence(R);
		var S:BigNum,T:BigNum := extended_gcd(B, R);

		X := T;
		var QT:BigNum := BigNumMul(BigNum_ctor(false, Q),T);
		Y := BigNumSub(S, QT);

		// translation into parallel variable names
//		assert sub_a*
//		var sub_A := B;
//		var sub_B := R;
//		var sub_X := S;
//		var sub_Y := T;
//		assert gcd(I(sub_A), I(sub_B), I(sub_A)*I(sub_X) + I(sub_B)*I(sub_Y));
		// wts gcd(I(A), I(B), I(A)*BV(X) + I(B)*BV(Y))

		assert BV(X) == BV(T) <= I(B) < I(A);
		// need Y <= I(A)

		ghost var bsrt:int := I(B)*BV(S)+I(R)*BV(T);
		// induction hypothesis
		assert 0 <= bsrt;
		assert divides(bsrt, I(B));
		assert divides(bsrt, I(R));

		// The gcd we're returning can be written BS+RT:
		ghost var gcd := I(A)*BV(X) + I(B)*BV(Y);
		calc {
			gcd;
			I(A)*BV(X) + I(B)*BV(Y);
			I(A)*BV(T) + I(B)*(BV(S) - I(Q)*BV(T));
				{ lemma_mul_is_distributive_forall(); }
			I(A)*BV(T) + I(B)*BV(S) - I(B)*(I(Q)*BV(T));
				{ lemma_mul_is_associative_forall(); }
			I(B)*BV(S) + I(A)*BV(T) - (I(B)*I(Q))*BV(T);
				{ lemma_mul_is_distributive_forall(); }
			I(B)*BV(S) + (I(A)-I(B)*I(Q))*BV(T);
				{
					assert I(A) == I(Q)*I(B)+I(R);
					lemma_mul_is_commutative_forall();
					assert I(A) - I(B)*I(Q) == I(R);
				}
			I(B)*BV(S) + I(R)*BV(T);
			bsrt;
		}

		// BS+RT divides R and BQ (induction hypothesis),
		// so it divides R+BQ, which we also know as A.
		calc ==> {
			divides(bsrt, I(B));
				{
					lemma_mul_positive_forall();
					lemma_divides_multiple(bsrt, I(B), I(Q));
				}
			divides(bsrt, I(B)*I(Q));
				{ lemma_divides_sum(bsrt, I(R), I(B)*I(Q)); }
			divides(bsrt, I(R)+I(B)*I(Q));
				{ lemma_mul_is_commutative_forall(); }
			divides(bsrt, I(R)+I(Q)*I(B));
			divides(bsrt, I(A));
		}

		// pieces of is_gcd:
		assert gcd!=0;
		assert divides(gcd,I(A));	// from calc above
		assert divides(gcd,I(B));	// from induction hypothesis
		// The tricky bit is showing that gcd is indeed greatest;
		// that requires algebraing back to show that any greater
		// gcd for A,B is also greater for the inductive call with B,R.
		forall (x | gcd<x)
			ensures !(divides(x,I(A)) && divides(x,I(B)));
		{
			if (divides(x,I(A)) && divides(x,I(B)))
			{
				assert divides(x,I(B));	// That was easy.
				calc ==> {
					divides(x,I(A));
						{ lemma_divides_multiple(x,I(B),(-I(Q))); }
					divides(x,I(B)*(-I(Q)));
						{ lemma_mul_is_commutative_forall(); }
					divides(x,(-I(Q))*I(B));
						{ lemma_divides_sum(x, I(A), (-I(Q))*I(B)); }
					divides(x,I(A) + (-I(Q))*I(B));
						{ lemma_mul_unary_negation(I(Q),I(B)); }
					divides(x,I(A) + (-(I(Q)*I(B))));
					divides(x,I(A) - I(Q)*I(B));
					divides(x,I(R));
				}
				// But now x divides B and R, which violates
				// the inductive hypothesis.
				assert false;	// contradicts induction hypothesis
			}
		}
		assert is_gcd(I(A), I(B), gcd);

		ghost var a := I(A);
		ghost var b := I(B);
		ghost var q := I(Q);
		ghost var r := I(R);
		ghost var x := BV(X);
		ghost var y := BV(Y);
		ghost var s := BV(S);
		ghost var t := BV(T);

		// Maintain the invariant that we're selecting the X,Y parameters
		// close to zero, not one of the infinite other choices.
		// ensures I(B) <= BV(X) <= I(B);
		if (s > 0)
		{
			if (s==1 && t==0)
			{
				calc {
					y;
					s - q*t;
						{ lemma_mul_is_mul_boogie(q, t); }
					s - q*0;
						{ lemma_mul_basics_forall(); }
					s;
					1;
				}
				assert -I(A) <= BV(Y) <= I(A);
			}
			else
			{
				assert 0 < s <= r;
				assert -b <= t <= 0;
				assert 0 <= -t <= b;
				calc {
					0;
					< s;
					<=	{ lemma_mul_nonnegative(q,-t); }
					s + q*(-t);
						{ lemma_mul_unary_negation(q,t); }
					s - q*t;
					y;
				}
				if (q==0)
				{
					calc {
						s-r;
						<= 0;
							{ lemma_mul_basics_forall(); }
						0 * (b-(-t));
							{ lemma_mul_is_mul_boogie(q, b-(-t)); }
						q * (b-(-t));
					}
				}
				else if (b==-t)
				{
					calc {
						s-r;
						<= 0;
							{ lemma_mul_basics_forall(); }
						q * 0;
							{ lemma_mul_is_mul_boogie(q, b-(-t)); }
						q * (b-(-t));
					}
				}
				else
				{
					calc {
						s-r;
						<= 0;
						<= b-(-t);
						<=	{ lemma_mul_increases(q,b-(-t)); }
						q*(b-(-t));
					}
				}

				calc ==> {
					s-r <= q*(b-(-t));
						{ lemma_mul_is_distributive_forall(); }
					s-r <= q*b - q*(-t);
				}
				calc {
					y;
					s-q*t;
						{ lemma_mul_unary_negation(q,t); }
					s+q*(-t);
					<= q*b + r;
					a;
				}
				assert 0 < BV(Y) <= I(A);
			}
			assert opposing_signs(BV(X), BV(Y));
			assert -I(A) <= BV(Y) <= I(A);
			assert x!=0 || y!=0;
		}
		else if (s==0)
		{
			assert -b <= t <= b;
			calc {
				y;
				s - q*t;
				s + (- (q*t));
					{ lemma_mul_unary_negation(q,t); }
				s + q*(-t);
				q*(-t);
			}
			if (q==0)
			{
				calc {
					y;
					s - q*t;
						{ lemma_mul_is_mul_boogie(q,t); }
					s - 0*t;
						{ lemma_mul_basics_forall(); }
					s - 0;
					0;
				}
				assert -I(A) <= BV(Y) <= I(A);
			}
			else
			{
				calc ==> {
					true;
					-b <= -t <= b;
						{
							lemma_mul_left_inequality(q,-b,-t);
							lemma_mul_left_inequality(q,-t,b);
						}
					q*(-b) <= q*(-t) <= q*b;
					q*(-b) <= y <= q*b;
					q*(-b) - r <= y <= q*b + r;
						{ lemma_mul_unary_negation(q,b); }
					-(q*b) - r <= y <= q*b + r;
					-(q*b + r) <= y <= q*b + r;
					-a <= y <= a;
				}
				assert -I(A) <= BV(Y) <= I(A);
			}
			if (t==0)
			{
				assert false;
			}
			else if (t>0)
			{
				if (q==0)
				{
					calc {
						a;
						q*b+r;
							{ lemma_mul_is_mul_boogie(q, b); }
						0*b+r;
							{ lemma_mul_basics_forall(); }
						r;
						< b;
					}
					assert false;
				}
				calc {
					y;
					s-q*t;
					-(q*t);
					<	{
							assert 0<q;
							assert 0<t;
							lemma_mul_strictly_positive(q,t);
							assert 0<q*t;
						}
					0;
				}
			}
			else
			{
				calc {
					0;
					<=	{
							assert 0<=q;
							assert 0<=-t;
							lemma_mul_nonnegative(q,-t);
						}
					q*(-t);
						{ lemma_mul_unary_negation(q,t); }
					-(q*t);
					s-q*t;
					y;
				}
			}
			assert opposing_signs(BV(X), BV(Y));
			assert x!=0 || y!=0;
		}
		else
		{
			assert -r <= s < 0;
			assert 0 < -s <= r;
			assert 0 <= t <= b;
			calc {
				y;
				s - q*t;
				< 0 - q*t;
				<= { lemma_mul_nonnegative(q,t); }
				0;
			}

			if (q==0)
			{
				calc {
					-s-r;
					<= 0;
						{ lemma_mul_basics_forall(); }
					0*b-0*t;
						{
							lemma_mul_is_mul_boogie(q, b);
							lemma_mul_is_mul_boogie(q, t);
						}
					q*b-q*t;
				}
			}
			else if (b==t)
			{
				calc {
					-s-r;
					<= 0;
						{ lemma_mul_basics_forall(); }
					q * 0;
						{ lemma_mul_is_mul_boogie(q, b-t); }
					q * (b-t);
						{ lemma_mul_is_distributive_forall(); }
					q*b-q*t;
				}
			}
			else
			{
				calc {
					-s-r;
					<= 0;
					<= b-t;
					<=	{ lemma_mul_increases(q,b-t); }
					q*(b-t);
						{ lemma_mul_is_distributive_forall(); }
					q*b-q*t;
				}
			}
			assert -s+q*t <= q*b+r;

			calc {
				-y;
				-s+q*t;
				<= q*b+r;
				a;
			}

			assert -y <= a;
			assert -a <= y;
			assert -I(A) <= BV(Y) < 0;
			assert opposing_signs(BV(X), BV(Y));
			assert x!=0 || y!=0;
		}
		assert -I(A) <= BV(Y) <= I(A);
		assert -I(B) <= BV(X) <= I(B);

		lemma_modesty_word_value_equivalence(A);
		assert ModestBigNatValue(A);
		assert I(X.value) <= I(A);
		assert ModestBigNatValue(X.value);
		lemma_modesty_word_value_equivalence(X.value);
		assert I(Y.value) <= I(A);
		assert ModestBigNatValue(Y.value);
		lemma_modesty_word_value_equivalence(Y.value);
	}
}

//lemma {:axiom} axiom_all_big_nats_are_modest(A:BigNat)
//	ensures FrumpyBigNat(A);
//	ensures ModestBigNatValue(A);
