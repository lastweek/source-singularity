include "BigNatDiv.dfy"
include "BigNatBitCount.dfy"
include "../Math/power.dfy"

method BigNatModulo(N:BigNat, M:BigNat) returns (R:BigNat)
	requires ModestBigNatWords(N);
	requires ModestBigNatWords(M);
	requires 0 <= I(N);
	requires 0 < I(M);
	ensures WellformedBigNat(R);
	ensures I(N) % I(M) == I(R);
	ensures I(R) < I(M);
	ensures ModestBigNatWords(R);
{
	var Q:BigNat;
	Q,R := BigNatDiv(N,M);

	lemma_fundamental_div_mod_converse(I(N), I(M), I(Q), I(R));

	assert I(R)<I(M);
	lemma_modesty_word_value_equivalence(M);
	lemma_modesty_word_value_equivalence(R);
	assert ModestBigNatWords(R);
}


method BigNatModExp_(B:BigNat, E:BigNat, bp2:nat, M:BigNat) returns (R:BigNat,Bp:BigNat)
	decreases bp2;
	requires FrumpyBigNat(B);
	requires FrumpyBigNat(E);
	requires FrumpyBigNat(M);
	requires !zero(B);
	requires !zero(M);
	requires 1 < I(M);
	requires I(E) < power2(bp2+1);
	requires bp2 < Width()-1;
	ensures WellformedBigNat(R);
	ensures power(I(B),I(E)) % I(M) == I(R);
	ensures I(R) < I(M);
	ensures FrumpyBigNat(R);
	ensures WellformedBigNat(Bp);
	ensures I(Bp) == power(I(B),power2(bp2)) % I(M);
{
	if (bp2==0)
	{
		lemma_power2_1_is_2();

		lemma_frumpy_is_modest(B);
		lemma_frumpy_is_modest(M);
		Bp := BigNatModulo(B, M);
		calc {
			I(Bp);
			I(B) % I(M);
				{ lemma_power_1(I(B)); }
			power(I(B),1) % I(M);
				{ lemma_power2_0_is_1(); }
			power(I(B),power2(bp2)) % I(M);
		}

		assert I(E) < 2;
		if (TestEqSmallLiteralBigNat(1,E))
		{
			assert I(E)==1;
			R := Bp;
			calc {
				I(R);
				power(I(B),power2(bp2)) % I(M);
					{ lemma_power2_0_is_1(); }
				power(I(B),1) % I(M);
				power(I(B),I(E)) % I(M);
			}
		}
		else
		{
			assert I(E)==0;
			R := MakeSmallLiteralBigNat(1);
			calc {
				I(R);
				1;
					{ lemma_small_mod(1, I(M)); }
				mod(1, I(M));
					{ lemma_power_0(I(B)); }
				power(I(B), 0) % I(M);
				power(I(B), I(E)) % I(M);
			}
		}
	}
	else
	{

//bm(B,21,m):
//bm_(B,21,4,m) --> r = B^21, bp = B^16
//	bp = bp_sub^2; r = r_sub*bp
//	e=21>=e_sub=2^bp=16 -> mul in bp
//bm_(B,5,3,m) --> r = B^5, bp = B^8
//	bp = bp_sub^2; r = r_sub
//	e=5 < e_sub=2^bp=8 -> no mul bp
//bm_(B,5,2,m) --> r = B^5, bp = B^4
//	bp = bp_sub^2; r = r_sub*bp
//	e=5>=e_sub=2^bp=4 -> mul in bp
//bm_(B,1,1,m) --> r = B^1, bp = B^2
//	bp = bp_sub^2; r = r_sub
//	e=1 < e_sub=2^bp=2 -> no mul bp
//bm_(B,1,0,m) --> r = B^1, bp = B^1
//	base

//		we'll expect Bp_sub == power(B,power2(bp2-1))

		var one:BigNat := MakeSmallLiteralBigNat(1);
		lemma_power2_0_is_1();
		lemma_power2_1_is_2();
		assert BitCount(one, 1);

		var E2:BigNat,oc:nat := BigNatBitShift_(one, 1, bp2);
		calc {
			I(E2);
			mul(power2(bp2),I(one));
			mul(power2(bp2),1);
				{ lemma_mul_basics_forall(); }
			power2(bp2);
		}

		var E_sub:BigNat;
		var use_this_square:bool := BigNatGe(E, E2);
		if (use_this_square)
		{
			E_sub := BigNatSub(E, E2);

			assert I(E_sub) <= I(E);
			assert FrumpyBigNat(E_sub);

			calc {
				I(E_sub);
				I(E) - I(E2);
				I(E) - power2(bp2);
				<
				power2(bp2+1) - power2(bp2);
					{ reveal_power2(); }
				2*power2(bp2) - power2(bp2);
				power2(bp2);
			}
		}
		else
		{
			E_sub := E;
			assert I(E_sub) <= I(E);

			calc {
				I(E_sub);
				I(E);
				< I(E2);
				power2(bp2);
			}
		}
		assert 0<=I(E_sub);
		assert I(E_sub) < power2(bp2);

		lemma_power_positive(I(B),power2(bp2-1));
		lemma_power_positive(I(B),power2(bp2));

		var R_sub:BigNat,Bp_sub:BigNat := BigNatModExp_(B, E_sub, bp2-1, M);
		lemma_mod_pos_bound(power(I(B),power2(bp2-1)), I(M));
		assert I(Bp_sub) < I(M) < Frump();

		var Bp_sub_squared:BigNat := BigNatMul(Bp_sub, Bp_sub);
		lemma_frumpy_squared_is_modest(Bp_sub, Bp_sub_squared);
		lemma_frumpy_is_modest(M);
		Bp := BigNatModulo(Bp_sub_squared, M);
		
		calc {
			I(Bp);
			I(Bp_sub_squared) % I(M);
			(I(Bp_sub)*I(Bp_sub)) % I(M);
			((power(I(B),power2(bp2-1))%I(M)) * (power(I(B),power2(bp2-1))%I(M))) % I(M);
				{ lemma_mul_mod_noop(power(I(B),power2(bp2-1)), power(I(B),power2(bp2-1)), I(M)); }
			(power(I(B),power2(bp2-1)) * power(I(B),power2(bp2-1))) % I(M);
				{ lemma_power_adds(I(B), power2(bp2-1), power2(bp2-1)); }
			(power(I(B),power2(bp2-1)+power2(bp2-1))) % I(M);
			(power(I(B),2 * power2(bp2-1))) % I(M);
				{ lemma_mul_is_mul_boogie(2, power2(bp2-1)); }
			(power(I(B),mul(2, power2(bp2-1)))) % I(M);
				{
					lemma_mul_is_mul_boogie(2, power2(bp2-1));
					reveal_power2();
				}
			(power(I(B),power2(bp2))) % I(M);
		}

		if (use_this_square)
		{
			var R_big:BigNat := BigNatMul(R_sub, Bp);
			lemma_frumpy_product_is_modest(R_sub, Bp, R_big);
			R := BigNatModulo(R_big, M);
			calc {
				I(R);
				I(R_big) % I(M);
				mul(I(R_sub), I(Bp)) % I(M);
				mul(power(I(B),I(E_sub)) % I(M), power(I(B),power2(bp2)) % I(M)) % I(M);
					{
						assert 0<=I(E_sub);
						assert 0<=power2(bp2);
						lemma_power_positive(I(B),I(E_sub));
						lemma_power_positive(I(B),power2(bp2));
						lemma_mul_mod_noop(
							power(I(B),I(E_sub)),
							power(I(B),power2(bp2)),
							I(M));
					}
				mul(power(I(B),I(E_sub)), power(I(B),power2(bp2))) % I(M);
					{ lemma_power_adds(I(B), I(E_sub), power2(bp2)); }
				power(I(B),I(E_sub)+power2(bp2)) % I(M);
				power(I(B),I(E)-I(E2)+power2(bp2)) % I(M);
				power(I(B),I(E)-power2(bp2)+power2(bp2)) % I(M);
				power(I(B),I(E)) % I(M);
			}
		}
		else
		{
			R := R_sub;
			calc {
				I(R);
				I(R_sub);
				power(I(B),I(E_sub)) % I(M);
				power(I(B),I(E)) % I(M);
			}
		}
	}
}

method BigNatModExp(B:BigNat, E:BigNat, M:BigNat) returns (R:BigNat)
	requires FrumpyBigNat(B);
	requires FrumpyBigNat(E);
	requires FrumpyBigNat(M);
	requires !zero(B);
	requires !zero(M);
	requires 1 < I(M);
	ensures WellformedBigNat(R);
	ensures power(I(B),I(E)) % I(M) == I(R);
	ensures I(R) < I(M);
{
	if (zero(E))
	{
		R := MakeSmallLiteralBigNat(1);
		calc {
			power(I(B),I(E)) % I(M);
			power(I(B),0) % I(M);
				{ lemma_power_0(I(B)); }
			mod(1, I(M));
				{ lemma_small_mod(1, I(M)); }
			1;
			I(R);
		}
	}
	else
	{
		lemma_frumpy_is_modest(E);
		var ec:nat := BigNatCountBits(E);
		var bp2:nat := ec - 1;

		calc {
			I(E);
			< power2(ec);
			power2(bp2+1);
		}

		calc {
			power2(bp2);
			power2(ec-1);
			<= I(E);
			< Frump();
			power2(power2(30));
		}
		calc {
			bp2;
			<	{ lemma_power2_strictly_increases_converse(bp2,power2(30)); }
			power2(30);
			<	{ lemma_power2_strictly_increases(30, 32); }
			Width();
		}

		var dummy_Bp:BigNat;
		R,dummy_Bp := BigNatModExp_(B, E, bp2, M);
	}
}
