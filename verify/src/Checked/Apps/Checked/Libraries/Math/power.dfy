include "../../../Trusted/Spec/Libraries/Math/power.dfy"
include "mul.dfy"

//lemma lemma_mul_passes_harmlessly_through_mod(
//	ensures mul(x,y) % m == mul(x

static lemma lemma_power_0(b:int)
	ensures power(b,0) == 1;
{
	reveal_power();
}

static lemma lemma_power_1(b:int)
	ensures power(b,1) == b;
{
	calc {
		power(b,1);
			{ reveal_power(); }
		b*power(b,0);
			{ lemma_power_0(b); }
		INTERNAL_mul(b,1);
			{ lemma_mul_basics_forall(); }
		b;
	}
}

static lemma lemma_power_adds(b:int, e1:nat, e2:nat)
	decreases e1;
	ensures power(b,e1)*power(b,e2) == power(b,e1+e2);
{
	if (e1==0)
	{
		calc {
			power(b,e1)*power(b,e2);
				{ lemma_power_0(b); }
			INTERNAL_mul(1,power(b,e2));
				{ lemma_mul_basics_forall(); }
			power(b,0+e2);
		}
	}
	else
	{
		calc {
			power(b,e1)*power(b,e2);
				{ reveal_power(); }
			(b*power(b,e1-1))*power(b,e2);
				{ lemma_mul_is_associative_forall(); }
			b*(power(b,e1-1)*power(b,e2));
				{ lemma_power_adds(b, e1-1, e2); }
			b*power(b,e1-1+e2);
				{ reveal_power(); }
			power(b,e1+e2);
		}
	}
}

static lemma lemma_power_positive(b:int, e:nat)
	decreases e;
	requires 0<b;
	ensures 0<power(b,e);
{
	if (e==0)
	{
		reveal_power();
	}
	else
	{
		calc {
			power(b,e);
				{ reveal_power(); }
			b*power(b,e-1);
			>	{
					lemma_power_positive(b,e-1);
					lemma_mul_strictly_positive_forall();
				}
			0;
		}
	}
}

static lemma lemma_square_is_power_2(x:nat)
	ensures power(x,2) == x*x;
{
	calc {
		power(x,2);
			{ reveal_power(); }
		x*power(x,1);
			{ reveal_power(); }
		x*(x*power(x,0));
			{ reveal_power(); }
		x*INTERNAL_mul(x,1);
			{ lemma_mul_basics_forall(); }
		x*x;
	}
}
