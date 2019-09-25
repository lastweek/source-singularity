include "../../Math/div.dfy"

static function divides(d:nat, n:int) : bool
	requires d != 0;
{
	(n % d) == 0
}

static lemma lemma_anything_divides_itself(a:nat)
	requires a != 0;
	ensures divides(a, a);
{
	lemma_mod_properties();
	assert a % a == 0;
}

static lemma lemma_anything_divides_zero(a:nat)
	requires a != 0;
	ensures divides(a, 0);
{
	reveal_mod_recursive();
	assert 0 % a == 0;
}

static lemma lemma_nothing_bigger_divides(a:nat)
	requires 0<a;
	ensures forall x :: a<x ==> !divides(x,a);
{
	forall (x | a<x)
		ensures !divides(x,a);
	{
		if (divides(x,a))
		{
			assert a % x == 0;
			reveal_INTERNAL_div_recursive();
			assert a / x == 0;

			lemma_fundamental_div_mod(a, x);
			calc {
				a;
				x * (a/x) + (a%x);
				x * (a/x);
				mul(x, 0);
					{ lemma_mul_basics_forall(); }
				0;
			}
			assert false;
		}
	}
}

static lemma lemma_divides_multiple(d:nat, a:int, b:int)
	requires d!=0;
	requires divides(d,a);
	ensures divides(d,a*b);
{
	assert a%d == 0;
	lemma_fundamental_div_mod(a,d);
	assert a == d * (a/d) + (a%d);
	assert a == d * (a/d);

	calc {
		a*b;
		(d * (a/d))*b;
			{ lemma_mul_is_associative_forall(); }
		d * ((a/d)*b);
			{ lemma_mul_is_commutative_forall(); }
		((a/d)*b)*d;
	}
	lemma_fundamental_div_mod_converse(a*b, d, ((a/d)*b), 0);
	assert 0 == (a*b) % d;
}

static lemma lemma_divides_sum(d:nat, a:int, b:int)
	requires d!=0;
	requires divides(d,a);
	requires divides(d,b);
	ensures divides(d,a+b);
{
	lemma_fundamental_div_mod(a,d);
	assert a == d * (a/d);
	lemma_fundamental_div_mod(b,d);
	assert b == d * (b/d);

	calc {
		a+b;
		d * (a/d) + d * (b/d);
			{ lemma_mul_is_distributive_forall(); }
		d * ((a/d) + (b/d));
			{ lemma_mul_is_commutative_forall(); }
		((a/d) + (b/d))*d;
	}
	lemma_fundamental_div_mod_converse(a+b, d, ((a/d) + (b/d)), 0);
	assert 0 == (a+b) % d;
}

static predicate is_gcd(a:nat, b:nat, gcd:nat)
{
	gcd != 0
	&& divides(gcd,a)
	&& divides(gcd,b)
	&& forall x:int :: gcd<x ==> !(divides(x,a) && divides(x,b))
}

