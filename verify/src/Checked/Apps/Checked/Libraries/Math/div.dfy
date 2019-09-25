include "mul.dfy"

// Specs/implements mathematical div and mod, not the C version.
// This may produce "surprising" results for negative values
// For example, -3 div 5 is -1 and -3 mod 5 is 2.  
// Note this is consistent: -3 * -1 + 2 == 5
/*
static function mod(x:int, m:int) : int	
	requires m > 0;
	decreases if x < 0 then (m - x) else x;
{
	if x < 0 then
		mod(m + x, m)
	else if x < m then
		x
	else
		mod(x - m, m)		
}

static function INTERNAL_div_recursive(x:int, d:int) : int
	requires d != 0;
{
	if d > 0 then
		INTERNAL_div_pos(x, d)
	else
		-1 * INTERNAL_div_pos(x, -1*d)
}

static function {:hidden} INTERNAL_div_pos(x:int, d:int) : int
	//requires d >  0;
	decreases if x < 0 then (d - x) else x;
{
	var r:int :| true;
	if d <= 0 then
		r
	else if x < 0 then
		-1 + INTERNAL_div_pos(x+d, d)
	else if x < d then
		0
	else 
		1 + INTERNAL_div_pos(x-d, d)
}
*/

static function div(x:int, d:int) : int
{
	INTERNAL_div(x,d)
}

static function mod(x:int, d:int) : int
{
	INTERNAL_mod(x,d)
}

static function div_recursive(x:int, d:int) : int
{ INTERNAL_div_recursive(x,d) }

static function mod_recursive(x:int, d:int) : int
{ INTERNAL_mod_recursive(x,d) }

static function mod_boogie(x:int, y:int) : int
{ INTERNAL_mod_boogie(x,y) }

static function div_boogie(x:int, y:int) : int
{ INTERNAL_div_boogie(x,y) }

static lemma reveal_mod_recursive()
	ensures forall x:int,y:int :: mod(x,y)==mod_recursive(x,y);
  ensures forall x, y :: INTERNAL_mod(x, y) == INTERNAL_mod_recursive(x, y);
{ reveal_INTERNAL_mod_recursive(); }

static lemma reveal_div_recursive()
  ensures forall x, y :: div(x, y) == div_recursive(x, y);
  ensures forall x, y :: INTERNAL_div(x, y) == INTERNAL_div_recursive(x, y);
{ reveal_INTERNAL_div_recursive(); }

static ghost method test() 
{
	assert -3 % 5 == 2;
	assert 10 % -5 == 0;
	assert 1 % -5 == 1;
	assert -3 / 5 == -1;
}

//////////////////////////////////////////////////////////////////////////////
//
// Core lemmas, with named arguments.
//
//////////////////////////////////////////////////////////////////////////////

static lemma lemma_div_by_one_is_identity(x:int)
  ensures INTERNAL_div(x, 1) == x;
  decreases if x > 0 then x else -x;
{
  reveal_INTERNAL_div_recursive();
  if x > 0
  {
    lemma_div_by_one_is_identity(x-1);
  }
  else if x < 0
  {
    lemma_div_by_one_is_identity(x+1);
  }
}

static lemma lemma_div_basics(x:int)
  ensures x != 0 ==> INTERNAL_div(0, x) == 0;
  ensures INTERNAL_div(x, 1) == x;
{
  reveal_INTERNAL_div_recursive();
  lemma_div_by_one_is_identity(x);
}

static lemma lemma_small_div()
  ensures forall x, d :: 0 <= x < d && d > 0 ==> x / d == 0;
{
	reveal_div_recursive();
}

static lemma lemma_div_pos_is_pos(x:int, divisor:int)
	requires 0 <= x;
	requires 0 < divisor;
	ensures INTERNAL_div(x, divisor) >= 0;
{
	if (x < divisor) {
		lemma_small_div();
	} else {
		calc {
			div(x, divisor);
			{ reveal_div_recursive(); }
			1 + div(x - divisor, divisor);
			>= { lemma_div_pos_is_pos(x-divisor, divisor); }
			0;
		}
	}

}

static lemma lemma_div_is_ordered(x:int, y:int, z:int)
	requires 0 <= x <= y;
	requires z > 0;
	ensures INTERNAL_div(x, z) <= INTERNAL_div(y, z); 
{
	if (x < z) {
		lemma_small_div();
		lemma_div_pos_is_pos(y, z);		
	} else {
		calc <= {
			div(x, z);
			{ reveal_div_recursive(); }
			1 + div(x-z, z);
			{ lemma_div_is_ordered(x-z, y-z, z); }
			1 + div(y-z, z);
			{ reveal_div_recursive(); }
			div(y, z);
		}
	}
}

static lemma lemma_div_is_ordered_by_denominator(x:int, y:int, z:int)
	requires x >= 0;
	requires 1 <= y <= z;
	ensures INTERNAL_div(x, y) >= INTERNAL_div(x, z);
    decreases x;
{
    reveal_INTERNAL_div_recursive();

    if (x < z)
    {
        lemma_div_is_ordered(0, x, y);
    }
    else
    {
        lemma_div_is_ordered(x-z, x-y, y);
        lemma_div_is_ordered_by_denominator(x-z, y, z);
    }
}

//////////////////////////////////////////////////////////////////////////////
//
// Forall lemmas: these restate the core lemmas with foralls,
// so callers needn't name the specific expressions to manipulate.
//
// These are all boilerplate transformations of args/requires/ensures
// into forall args :: requires ==> ensures, with a correpsonding
// mechanically generated forall proof that invokes the core lemma.
// So don't bother reading them.
//
//////////////////////////////////////////////////////////////////////////////

static lemma lemma_div_basics_forall()
	ensures forall x :: x != 0 ==> INTERNAL_div(0, x) == 0;
	ensures forall x :: INTERNAL_div(x, 1) == x;
    ensures forall x, y :: x >= 0 && y > 0 ==> INTERNAL_div(x,y) >= 0;
    ensures forall x, y :: x >= 0 && y > 0 ==> INTERNAL_div(x,y) <= x;
{
	forall (x:int)
		ensures x != 0 ==> INTERNAL_div(0, x) == 0;
		ensures INTERNAL_div(x, 1) == x;
	{
		lemma_div_basics(x);
	}
    forall x:int, y:int | x >= 0 && y > 0
        ensures INTERNAL_div(x, y) >= 0;
        ensures INTERNAL_div(x, y) <= x;
    {
        lemma_div_pos_is_pos(x, y);
        lemma_div_is_ordered_by_denominator(x, 1, y);
    }
}

static lemma lemma_some_things_boogie_knows_about_division(x:int)
	ensures -1 + INTERNAL_div_boogie(x+2, 2) == INTERNAL_div_boogie(x, 2);
	ensures 1 + INTERNAL_div_boogie(x-2, 2) == INTERNAL_div_boogie(x, 2);
{
}

static lemma lemma_div_is_div_boogie_at_least_for_2(x:int)
	decreases if x < 0 then (2 - 1 - x) else x;
	ensures INTERNAL_div(x, 2) == INTERNAL_div_boogie(x,2);
{
	if (x < 0) {
		calc {
			INTERNAL_div(x,2);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,2);
			INTERNAL_div_pos(x,2);
			-1 + INTERNAL_div_pos(x+2, 2);
			-1 + INTERNAL_div_recursive(x+2, 2);
				{ reveal_INTERNAL_div_recursive(); }
			-1 + INTERNAL_div(x+2, 2);
				{ lemma_div_is_div_boogie_at_least_for_2(x+2); }
			-1 + INTERNAL_div_boogie(x+2, 2);
				{ lemma_some_things_boogie_knows_about_division(x); }
			INTERNAL_div_boogie(x, 2);
		}
	} else if (x < 2) {
		calc {
			INTERNAL_div(x,2);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,2);
			INTERNAL_div_pos(x,2);
			0;
			INTERNAL_div_boogie(x, 2);
		}
	} else {
		calc {
			INTERNAL_div(x,2);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,2);
			INTERNAL_div_pos(x,2);
			1 + INTERNAL_div_pos(x-2, 2);
			1 + INTERNAL_div_recursive(x-2, 2);
				{ reveal_INTERNAL_div_recursive(); }
			1 + INTERNAL_div(x-2, 2);
				{ lemma_div_is_div_boogie_at_least_for_2(x-2); }
			1 + INTERNAL_div_boogie(x-2, 2);
				{ lemma_some_things_boogie_knows_about_division(x); }
			INTERNAL_div_boogie(x, 2);
		}
	}
}

// Copy-pasta from lemma_div_is_div_boogie_at_least_for_2
static lemma lemma_div_is_div_boogie_for_8_which_is_also_a_number(x:int)
	decreases if x < 0 then (8 - 1 - x) else x;
	ensures INTERNAL_div(x, 8) == INTERNAL_div_boogie(x,8);
{
	if (x < 0) {
		calc {
			INTERNAL_div(x,8);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,8);
			INTERNAL_div_pos(x,8);
			-1 + INTERNAL_div_pos(x+8, 8);
			-1 + INTERNAL_div_recursive(x+8, 8);
				{ reveal_INTERNAL_div_recursive(); }
			-1 + INTERNAL_div(x+8, 8);
				{ lemma_div_is_div_boogie_for_8_which_is_also_a_number(x+8); }
			-1 + INTERNAL_div_boogie(x+8, 8);
				{ lemma_some_things_boogie_knows_about_division(x); }
			INTERNAL_div_boogie(x, 8);
		}
	} else if (x < 8) {
		calc {
			INTERNAL_div(x,8);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,8);
			INTERNAL_div_pos(x,8);
			0;
			INTERNAL_div_boogie(x, 8);
		}
	} else {
		calc {
			INTERNAL_div(x,8);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,8);
			INTERNAL_div_pos(x,8);
			1 + INTERNAL_div_pos(x-8, 8);
			1 + INTERNAL_div_recursive(x-8, 8);
				{ reveal_INTERNAL_div_recursive(); }
			1 + INTERNAL_div(x-8, 8);
				{ lemma_div_is_div_boogie_for_8_which_is_also_a_number(x-8); }
			1 + INTERNAL_div_boogie(x-8, 8);
				{ lemma_some_things_boogie_knows_about_division(x); }
			INTERNAL_div_boogie(x, 8);
		}
	}
}

// Copy-pasta from lemma_div_is_div_boogie_at_least_for_2
static lemma lemma_div_is_div_boogie_for_256_which_is_also_a_number(x:int)
	decreases if x < 0 then (256 - 1 - x) else x;
	ensures INTERNAL_div(x, 256) == INTERNAL_div_boogie(x,256);
{
	if (x < 0) {
		calc {
			INTERNAL_div(x,256);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,256);
			INTERNAL_div_pos(x,256);
			-1 + INTERNAL_div_pos(x+256, 256);
			-1 + INTERNAL_div_recursive(x+256, 256);
				{ reveal_INTERNAL_div_recursive(); }
			-1 + INTERNAL_div(x+256, 256);
				{ lemma_div_is_div_boogie_for_256_which_is_also_a_number(x+256); }
			-1 + INTERNAL_div_boogie(x+256, 256);
				{ lemma_some_things_boogie_knows_about_division(x); }
			INTERNAL_div_boogie(x, 256);
		}
	} else if (x < 256) {
		calc {
			INTERNAL_div(x,256);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,256);
			INTERNAL_div_pos(x,256);
			0;
			INTERNAL_div_boogie(x, 256);
		}
	} else {
		calc {
			INTERNAL_div(x,256);
				{ reveal_INTERNAL_div_recursive(); }
			INTERNAL_div_recursive(x,256);
			INTERNAL_div_pos(x,256);
			1 + INTERNAL_div_pos(x-256, 256);
			1 + INTERNAL_div_recursive(x-256, 256);
				{ reveal_INTERNAL_div_recursive(); }
			1 + INTERNAL_div(x-256, 256);
				{ lemma_div_is_div_boogie_for_256_which_is_also_a_number(x-256); }
			1 + INTERNAL_div_boogie(x-256, 256);
				{ lemma_some_things_boogie_knows_about_division(x); }
			INTERNAL_div_boogie(x, 256);
		}
	}
}

static lemma lemma_mod_is_mod_boogie_for_2_which_is_also_a_number(x:int)
	decreases if x < 0 then (2 - 1 - x) else x;
	ensures INTERNAL_mod(x, 2) == INTERNAL_mod_boogie(x,2);
{
	if (x < 0)
	{
		calc {
			mod(x,2);
				{ reveal_mod_recursive(); }
			INTERNAL_mod_recursive(x,2);
			INTERNAL_mod_recursive(x+2,2);
				{ reveal_mod_recursive(); }
			mod(x+2,2);
				{ lemma_mod_is_mod_boogie_for_2_which_is_also_a_number(x+2); }
			INTERNAL_mod_boogie(x+2,2);
			INTERNAL_mod_boogie(x,2);
		}
	}
	else if (x < 2)
	{
		calc {
			mod(x,2);
				{ reveal_mod_recursive(); }
			INTERNAL_mod_recursive(x,2);
			x;
			INTERNAL_mod_boogie(x,2);
		}
	}
	else
	{
		calc {
			mod(x,2);
				{ reveal_mod_recursive(); }
			INTERNAL_mod_recursive(x,2);
			INTERNAL_mod_recursive(x - 2, 2);
				{ reveal_mod_recursive(); }
			mod(x - 2, 2);
				{ lemma_mod_is_mod_boogie_for_2_which_is_also_a_number(x-2); }
			INTERNAL_mod_boogie(x-2,2);
			INTERNAL_mod_boogie(x,2);
		}
	}
}

static lemma lemma_mod_is_mod_boogie_for_256_which_is_also_a_number(x:int)
	decreases if x < 0 then (256 - 1 - x) else x;
	ensures INTERNAL_mod(x, 256) == INTERNAL_mod_boogie(x,256);
{
	if (x < 0)
	{
		calc {
			mod(x,256);
				{ reveal_mod_recursive(); }
			INTERNAL_mod_recursive(x,256);
			INTERNAL_mod_recursive(x+256,256);
				{ reveal_mod_recursive(); }
			mod(x+256,256);
				{ lemma_mod_is_mod_boogie_for_256_which_is_also_a_number(x+256); }
			INTERNAL_mod_boogie(x+256,256);
			INTERNAL_mod_boogie(x,256);
		}
	}
	else if (x < 256)
	{
		calc {
			mod(x,256);
				{ reveal_mod_recursive(); }
			INTERNAL_mod_recursive(x,256);
			x;
			INTERNAL_mod_boogie(x,256);
		}
	}
	else
	{
		calc {
			mod(x,256);
				{ reveal_mod_recursive(); }
			INTERNAL_mod_recursive(x,256);
			INTERNAL_mod_recursive(x - 256, 256);
				{ reveal_mod_recursive(); }
			mod(x - 256, 256);
				{ lemma_mod_is_mod_boogie_for_256_which_is_also_a_number(x-256); }
			INTERNAL_mod_boogie(x-256,256);
			INTERNAL_mod_boogie(x,256);
		}
	}
}

/******************************************
 *  Useful lemmas relating div and mod    *   
 ******************************************/

static lemma lemma_fundamental_div_mod(x:int, d:int)
	decreases if x > 0 then d + x else -x;
	requires 0<d;
	ensures x == d * (x/d) + (x%d);
{
	if (x<0)
	{
		if (x+d < 0)
		{
			calc {
				x;
					{ lemma_fundamental_div_mod(x+d,d); }
				d * ((x+d)/d) + ((x+d)%d) - d;
				d * ((x+d)/d-1+1) + ((x+d)%d) - d;
					{ reveal_div_recursive(); }
					{
						calc {
							x/d;
								{ reveal_div_recursive(); }
							-1 + INTERNAL_div_pos(x+d,d);
							-1 + (x+d)/d;
						}
					}
				d *  (x/d+1)+ ((x+d)%d) - d;
					{ reveal_mod_recursive(); }
				d *  (x/d+1)+ (x%d) - d;
					{ lemma_mul_is_distributive_forall(); }
				d *(x/d) +mul(d,1)+ (x%d) - d;
					{ lemma_mul_basics_forall(); }
				d *(x/d) +d+ (x%d) - d;
				d *(x/d) + (x%d);
			}
		}
		else
		{
			calc {
				x/d;
					{ reveal_div_recursive(); }
				-1 + (x+d)/d;
					{ reveal_div_recursive(); }
				-1 + 0;
				-1;
			}
			calc {
				x%d;
					{ reveal_mod_recursive(); }
				(x+d)%d;
					{ reveal_mod_recursive(); }
				x+d;
			}
			calc {
				d * (x/d) + (x%d);
				d * (-1) + x + d;
					{ lemma_mul_is_mul_boogie(d,-1); }
				-d + x + d;
				x;
			}
		}
	}
	else if (x==0)
	{
		calc {
			d * (x/d) + (x%d);
				{ reveal_div_recursive(); }
			mul(d,0) + (x%d);
				{ lemma_mul_basics_forall(); }
			(x%d);
				{ reveal_mod_recursive(); }
			0;
			x;
		}
	}
	else
	{
		calc {
			x;
				{ lemma_fundamental_div_mod(x-d,d); }
			d * ((x-d)/d) + ((x-d)%d) + d;
			d * ((x-d)/d+1-1) + ((x-d)%d) + d;
				{ reveal_div_recursive(); }
			d *  (x/d-1)+ ((x-d)%d) + d;
				{ reveal_mod_recursive(); }
			d *  (x/d-1)+ (x%d) + d;
				{ lemma_mul_is_distributive_forall(); }
			d *(x/d) -mul(d,1)+ (x%d) + d;
				{ lemma_mul_basics_forall(); }
			d *(x/d) -d+ (x%d) + d;
			d *(x/d) + (x%d);
		}
	}
}

//////////////////////////////////////////////////////////////////////////////
//
// I'm not sure how useful these are. I wrote them to try to bring
// negative numerators to the positive side for trying to prove
// the negative half of lemma_fundamental_div_mod. That turned out
// to be the wrong idea, so maybe these are just useless.

static lemma lemma_div_neg_neg(x:int, d:int)
	requires d > 0;
	ensures x/d == -((-x+d-1)/d);
	decreases if x > 0 then x + 1 else -x;
{
	if (x<0) {
		calc {
			x/d;
				{ reveal_INTERNAL_div_recursive(); }
			-1 + INTERNAL_div_pos(x+d, d);
				{ reveal_INTERNAL_div_recursive(); }
			-1 + INTERNAL_div(x+d,d);
				{
					if (x < -d)
					{
						lemma_div_neg_neg(x+d,d);
					}
					else
					{
						//assert 0 <= x+d < d;
						//assert 0 <= -(x+d)+d-1 < d;
						calc {
							(x+d)/d;
								{ reveal_div_recursive(); }
							0;
								{ reveal_div_recursive(); }
//								{ reveal_INTERNAL_div_recursive(); }
//div(x, y) == div_recursive(x, y)
//== INTERNAL_div_recursive(x,y)
							-((-(x+d)+d-1)/d);
						}
					}
				}
			-1 + -((-(x+d)+d-1)/d);
				{ lemma_mul_is_mul_boogie(-1, (-(x+d)+d-1)/d);
					assert -((-(x+d)+d-1)/d) == mul(-1, (-(x+d)+d-1)/d);
				}
			-1 + mul(-1, (-(x+d)+d-1)/d);
				{ lemma_mul_is_mul_boogie(-1, x+d); }
			-1 + mul(-1,(mul(-1,x+d)+d-1)/d);
				{ lemma_mul_basics_forall(); }
			mul(-1,1) + mul(-1,(mul(-1,x+d)+d-1)/d);
				{ lemma_mul_is_distributive_forall(); }
			mul(-1, 1 + (mul(-1,x+d)+d-1)/d);
				{ lemma_mul_is_distributive_forall(); }
			mul(-1, 1 + (mul(-1,x)+mul(-1,d)+d-1)/d);
			mul(-1, 1 + (mul(-1,x)+d-1+mul(-1,d))/d);
				{ lemma_mul_is_mul_boogie(-1, d); }
			mul(-1, 1 + (mul(-1,x)+d-1-d)/d);
				{ reveal_div_recursive(); }
			mul(-1, (mul(-1,x)+d-1)/d);
				{
					lemma_mul_is_mul_boogie(-1,x);
					lemma_mul_is_mul_boogie(-1,(-x+d-1)/d);
				}
			-((-x+d-1)/d);
		}
	} else if (x<d) {
		calc {
			x/d;
				{ reveal_div_recursive(); }
			0;
			-(0);
				{ reveal_div_recursive(); }
			-((-x+d-1)/d);
		}
	} else {
		calc {
			-((-x+d-1)/d);
				{ lemma_div_neg_neg(-x+d-1, d); }
			-(-((-(-x+d-1)+d-1)/d));
			-(-(((x-d+1)+d-1)/d));
			-(-((x-d+1+d-1)/d));
			-(-(x/d));
			x/d;
		}
	}
}

static lemma lemma_mod_neg_neg(x:int, d:int)
	requires d > 0;
	ensures x%d == (x*(1-d))%d;
{
	calc {
		(x*(1-d)) % d;
			{ lemma_mul_is_distributive_forall(); }
		(mul(x,1)-mul(x,d)) % d;
			{ lemma_mul_basics_forall(); }
		(x - x*d) % d;
			{ lemma_mul_is_mul_boogie(-1,x*d); }
		(x + mul(-1,x*d)) % d;
			{ lemma_mul_is_associative_forall(); lemma_mul_is_commutative_forall(); }
		(x + mul(-1,x)*d) % d;
			{ lemma_mul_is_mul_boogie(-1,x); }
		(x + (-x)*d) % d;
			{ lemma_mul_is_commutative(-x,d); }
		(d*(-x) + x) % d;
			{ lemma_mod_multiples_vanish(-x, x, d); }
		x % d;
	}
}

//
//////////////////////////////////////////////////////////////////////////////

/*******************************
 *  Useful lemmas about div    *   
 *******************************/

static lemma lemma_basic_div(d:int)
  requires d > 0;
  ensures forall x :: 0 <= x < d ==> div(x, d) == 0;
{
	reveal_div_recursive();
}

/*
static lemma lemma_even_div(d:int) 
	requires d >= 0;
	requires d % 2 == 0;
	ensures 2 * div(d, 2) == d;
{
	var k := INTERNAL_div_pos(d, 2);
	var r := d -  mul(k, 2);
	lemma_remainder(d, 2);		
	assert 0 <= r < 2;
	assert r == 0;
	calc {
		2 * INTERNAL_div_pos(d, 2);
		2 * INTERNAL_div_pos(2*k, 2);
		{ lemma_div_by_multiple(k, 2); }
		2 * k;
		d;
	}
}
*/
static lemma lemma_odd_div(d:int) 
	requires d >= 0;
	requires d % 2 == 1;
	ensures 2 * INTERNAL_div_pos(d, 2) + 1 == d;
{
	reveal_div_recursive();
    if (d >= 2)
    {
        lemma_odd_div(d - 2);
    }
}


static lemma lemma_div_by_multiple_is_strongly_ordered(x:int, y:int, m:int, z:int)
	requires 0 < m;
	requires 0 <= x < y;
	requires y == m * z;
	requires z > 0;	
	ensures	 INTERNAL_div(x, z) < INTERNAL_div(y, z);
{
	reveal_div_recursive();

	lemma_div_by_multiple(m, z);
	assert(div(y, z) == m);

	var k := INTERNAL_div(x, z);
	var r := x - INTERNAL_div(x, z) * z;
	lemma_remainder(x, z);	
	lemma_div_pos_is_pos(x, z);

	assert r >= 0;
	assert k*z <= k*z + r < m*z;
	lemma_div_by_multiple(k, z);
	assert div(k*z, z) == k;

	lemma_mul_properties();

	calc {
		div(x,z);
		k;
		<	{ lemma_mul_strict_inequality_converse(k,m,z); }
		m;
		div(y,z);
	}
}

static lemma lemma_remainder(x:int, divisor:int)
	requires 0 <= x;
	requires 0 < divisor;
	ensures  0 <= x - INTERNAL_div(x, divisor) * divisor < divisor;
{
	lemma_remainder_upper(x, divisor);
	lemma_remainder_lower(x, divisor);
}

static lemma lemma_remainder_upper(x:int, divisor:int)
	requires 0 <= x;
	requires 0 < divisor;
	ensures   x - divisor < INTERNAL_div(x, divisor) * divisor;
{
	if (x < divisor) {
		lemma_mul_properties();
		lemma_small_div();
	} else {
		calc {
			div(x, divisor) * divisor;
			{ reveal_div_recursive(); }
			(1 + div(x-divisor, divisor)) * divisor;
			{ lemma_mul_properties(); }
			INTERNAL_mul(1, divisor) + INTERNAL_div(x-divisor, divisor) * divisor;
			> { lemma_remainder_upper(x-divisor, divisor); }
			INTERNAL_mul(1, divisor) + ((x - divisor) - divisor);
			{ lemma_mul_properties(); }
			x-divisor;
		}
	}
}

static lemma lemma_remainder_lower(x:int, divisor:int)
	requires 0 <= x;
	requires 0 < divisor;
	ensures  x >= INTERNAL_div(x, divisor) * divisor;
{		
	
	if (x < divisor) {	
		lemma_mul_properties();
		lemma_small_div();
	} else {
		calc {
			div(x, divisor) * divisor;
			{ reveal_div_recursive(); }
			(1 + div(x-divisor, divisor)) * divisor;
			{ lemma_mul_properties(); }
			INTERNAL_mul(1, divisor) + INTERNAL_div(x-divisor, divisor) * divisor;
			<= { lemma_remainder_lower(x-divisor, divisor); }
			INTERNAL_mul(1, divisor) + x - divisor;
			{ lemma_mul_properties(); }
			x;
		}
	}
}



static lemma lemma_div_by_multiple(b:int, d:int)
	requires 0 <= b;
	requires 0 < d;
	ensures  INTERNAL_div(b*d, d) == b;
{
	if (b == 0) {
		lemma_mul_properties();
		assert b*d == 0*d == 0;
		lemma_small_div();
	} else {
		calc {
			div(b*d, d);
			{ reveal_div_recursive(); }
			1 + div(b*d-d, d);
			{ lemma_mul_properties(); }
			1 + INTERNAL_div(b*d-INTERNAL_mul(1,d), d);
			{ lemma_mul_properties(); }
			1 + div((b-1)*d, d);			
			{ lemma_div_by_multiple(b - 1, d); }			
			b;
		}			
	}
}

/*******************************
 *  Useful lemmas about mod    *   
 *******************************/

static lemma lemma_mod_remainder()
	ensures forall x:int, m:int :: m > 0 ==> 0 <= mod(x,m) < m;
{
	lemma_mod_remainder_pos();
	lemma_mod_remainder_neg();
}
	
static lemma lemma_small_mod(x:nat, m:nat)
	requires x<m;
	requires 0<m;
	ensures x % m == x;
{
	reveal_mod_recursive();
}

static lemma lemma_mod_properties()
	ensures forall m:int :: m > 0 ==> m % m == 0;
	ensures forall x:int, m:int :: m > 0 ==> (x%m)% m == x%m;
	ensures forall x:int, m:int :: m > 0 ==> 0 <= x%m < m;
{
	lemma_mod_remainder();
	reveal_mod_recursive();
	forall (x,m | m>0)
		ensures (x%m)% m == x%m;
	{
		assert mod(x,m) < m;	// lemma_mod_remainder
		lemma_small_mod(x%m,m);
	}

	forall (x,m | m>0)
		ensures m > 0 ==> 0 <= x%m < m;
	{
		lemma_mod_remainder();
		assert mod(x,m) <m;
		assert x%m <m;
	}
}

////////////////////////////////////////////////
//  Simple properties of mod with constants
////////////////////////////////////////////////

static lemma lemma_mod_2(x:int)
	requires x % 2 == 1;
	ensures (x+1) % 2 == 0;
{
}

static lemma lemma_mod2_plus(x:int) 
    requires x >= 0;
    requires x % 2 == 1;
    ensures (x+1)%2 == 0;
{
}

static lemma lemma_mod2_plus2(x:int) 
    requires x % 2 == 1;
    ensures (x+2) % 2 == 1;
{
}

static lemma lemma_mod32(x:int)
    requires x >= 32;
    ensures (x-32) % 32 == x % 32;
{
}


static lemma lemma_mod_512_forall() 
	ensures forall x:int :: x >= 0 ==> x % 512 == mod(x, 512);
{
	forall (x | x >= 0)
		ensures x % 512 == mod(x, 512);
	{
		lemma_mod_512(x);
	}
}

static lemma lemma_mod_512(x:int)
	requires x >= 0;
	ensures x % 512 == mod(x, 512);
	decreases x;
{
	reveal_mod_recursive();
	if (x < 512) {
	} else {
		lemma_mod_512(x - 512);
	}
}

// Note to self: Prove mod_add first, which should be easier, then prove this.
/*
static lemma lemma_mod_mul(x:int, y:int, m:int)
	requires m > 0;
	requires x >= 0;
	requires y >= 0;
	ensures  mod(x * y, m) == mod(x,m)*mod(y,m);
{
	if (x == 0) {
		lemma_mul_properties();
		assert INTERNAL_mul(x, m) == INTERNAL_mul(0, m) == 0;
	} else {
		calc {
			mod(x * y, m);
			mod(x*m - m, m);
				{ lemma_mul_properties(); }
			mod(x*m - mul(1,m), m);
				{ lemma_mul_properties(); }
			mod((x-1)*m, m); 
				{ lemma_mod_multiples(x-1, m); }
			0;
		}		
	}
}
*/

static lemma lemma_mod_remainder_neg()
	ensures forall x:int, m:int :: m > 0 && x < 0 ==> 0 <= mod(x,m) < m;
{
	forall x:int, m:int | m > 0 && x < 0
        ensures 0 <= mod(x,m) < m;
    {
		lemma_mod_remainder_neg_specific(x,m);
	}		
}

static lemma lemma_mod_remainder_neg_specific(x:int, m:int)
	requires  m > 0 && x < 0;
	ensures  0 <= mod(x,m)  < m;
	decreases mul(-1,x);
{
	reveal_mod_recursive();
	assert mod(x,m) == mod(m + x,m);
	if (x + m >= 0) {
		lemma_mod_remainder_pos();
	} else {
		reveal_INTERNAL_mul_recursive();	
		lemma_mul_is_mul_boogie(-1,m+x);
		lemma_mul_is_mul_boogie(-1,x);
		lemma_mod_remainder_neg_specific(m+x, m);
	}
}

static lemma lemma_mod_remainder_pos()	
	ensures forall x, m :: m > 0 && x >= 0 ==> 0 <= mod(x, m)  < m;
{
	forall x, m | m > 0 && x >= 0
        ensures 0 <= mod(x, m) < m;
	{
		lemma_mod_remainder_pos_specific(x,m);
	}
}

static lemma lemma_mod_remainder_pos_specific(x:int, m:int)	
	requires m > 0 && x >= 0;	
	ensures 0 <= mod(x, m)  < m;
	//ensures 0 <= mod(x, m)  < m;
{
	reveal_mod_recursive();
	if x == 0 {
	} else if x < m {	
	} else {
		lemma_mod_remainder_pos_specific(x - m, m);
	}
}

static lemma lemma_mod_remainder_specific(x:int, m:int)
    requires m > 0;
    ensures 0 <= mod(x, m) < m;
{
    if (x < 0) {
        lemma_mod_remainder_neg_specific(x, m);
    }
    else {
        lemma_mod_remainder_pos_specific(x, m);
    }
}    

static lemma lemma_fundamental_div_mod_converse_pos(x:nat, d:nat, q:nat, r:nat)
	decreases q;
	requires 0 < d;
	requires r < d;
	requires x == q * d + r;
	ensures q == x/d;
	ensures r == x%d;
{
	if (q==0)
	{
		calc {
			x/d;
			(q*d + r) / d;
			(INTERNAL_mul(0,d) + r) / d;
				{ lemma_mul_basics_forall(); }
			(0+r) / d;
			r / d;
				{ reveal_INTERNAL_div_recursive(); }
			0;
			q;
		}
		calc {
			x%d;
			(q*d + r) % d;
			(INTERNAL_mul(0,d) + r) % d;
				{ lemma_mul_basics_forall(); }
			(0+r) % d;
			r % d;
				{ reveal_INTERNAL_mod_recursive(); }
			r;
		}
	}
	else
	{
		// prove we're in the recursive cases of reveal_INTERNAL_div, _mod
		calc {
			q*d + r;
			>=
			q*d;
			>= { lemma_mul_increases(q,d); }
			d;
		}

		var q_sub := q-1;
		var x_sub := q_sub * d + r;

		calc {
			x_sub;
			q_sub * d + r;
			>=	{ lemma_mul_nonnegative_forall(); }
			r;
			>= 0;
		}

		// div

		calc ==> {
			x_sub == q_sub * d + r;
				{ lemma_fundamental_div_mod_converse_pos(x_sub, d, q_sub, r); }
			q_sub == x_sub / d;
			q_sub == (q_sub * d + r) / d;
			q-1 == ((q-1) * d + r) / d;
			q == 1 + ((q-1) * d + r) / d;
		}

		calc {
			x/d;
			(q*d + r) / d;
				{ reveal_INTERNAL_div_recursive(); }
			1 + ((q*d + r)-d) / d;
			1 + (q*d + r - d) / d;
			1 + (q*d + r - d) / d;
				{
					lemma_mul_basics(d);
					lemma_mul_is_commutative_forall();
				}
			1 + (d*q + r - INTERNAL_mul(d,1)) / d;
				{ lemma_mul_is_distributive_sub_forall(); }
			1 + (d*(q-1) + r) / d;
				{ lemma_mul_is_commutative_forall(); }
			1 + ((q-1)*d + r) / d;
			q;
		}

		// mod

		calc ==> {
			x_sub == q_sub * d + r;
				{ lemma_fundamental_div_mod_converse_pos(x_sub, d, q_sub, r); }
			r == x_sub % d;
			r == (q_sub*d+r) % d;
			r == ((q-1)*d+r) % d;
		}

		calc {
			x%d;
			(q*d + r) % d;
				{ reveal_INTERNAL_mod_recursive(); }
			(q*d + r - d) % d;
				{
					lemma_mul_basics(d);
					lemma_mul_is_commutative_forall();
				}
			(d*q + r - INTERNAL_mul(d,1)) % d;
				{ lemma_mul_is_distributive_sub_forall(); }
			(d*(q-1) + r) % d;
				{ lemma_mul_is_commutative_forall(); }
			((q-1)*d + r) % d;
			r;
		}
	}
}

static lemma lemma_fundamental_div_mod_converse(x:int, d:nat, q:int, r:nat)
	decreases -q;
	requires 0 < d;
	requires r < d;
	requires x == q * d + r;
	ensures q == x/d;
	ensures r == x%d;
{
	if (q < 0)
	{
		calc {
			x == q * d + r;
			x + d == q * d + d + r;
				{ lemma_mul_basics_forall(); }
			x + d == q * d + mul(1,d) + r;
				{ lemma_mul_is_distributive_forall(); }
			x + d == (q+1)*d + r;
		}
		lemma_fundamental_div_mod_converse(x+d,d,q+1,r);
		calc {
			r;
			(x+d) % d;
				{ reveal_INTERNAL_mod_recursive(); }
			(x+d-d) % d;
			x % d;
		}
		calc ==> {
			q+1 == (x+d) / d;
				{ reveal_INTERNAL_div_recursive(); }
			q+1 == 1 + (x+d-d) / d;
			q == (x+d-d) / d;
		}
	}
	else
	{
		assert 0<=q;
		assert 0<=d;
		lemma_mul_positive_forall();
		calc {
			0;
			<= q*d;
			<= q*d+r;
			x;
		}
		lemma_fundamental_div_mod_converse_pos(x,d,q,r);
	}
}

static lemma lemma_mod_pos_bound(x:int, m:int)
	decreases x;
	requires 0 <= x;
	requires 0 < m;
	ensures  0 <= INTERNAL_mod(x,m) < m;
{
	if (x < m)
	{
		reveal_INTERNAL_mod_recursive();
		assert INTERNAL_mod(x,m) == x;
		assert 0 <= INTERNAL_mod(x,m) < m;
	}
	else
	{
		assert 0 <= x - m;
		reveal_INTERNAL_mod_recursive();
		assert INTERNAL_mod(x,m) == INTERNAL_mod(x - m, m);
			lemma_mod_pos_bound(x -m, m);
		assert INTERNAL_mod(x - m, m) < m;
	}
}

//////////////////////////////////////////////////////////////////////////////
//
// more probably-dead code

static lemma lemma_mod_multiples_basic(x:int, m:int)
	requires m > 0;
	requires x >= 0;
	ensures  mod(x * m, m) == 0;
	decreases if x > 0 then x else -x;
{
	reveal_mod_recursive();
	if (x < 0) {
		calc {
			(x * m) % m;
			(x * m + m) % m;
				{ lemma_mul_properties(); }
			(x * m + mul(1,m)) % m;
				{ lemma_mul_is_distributive_forall(); }
			((x+1)*m) % m;
				{ lemma_mod_multiples_basic(x+1, m); }
			0;
		}
	} else if (x == 0) {
		calc {
			mul(x,m);
			x*m;
				{ lemma_mul_is_mul_boogie(x,m); }
			0*m;
			0;
		}
		calc {
			mod(x*m, m);
				{
					assert x<m;
					lemma_small_mod(x,m);
				}
			x;
			0;
		}
	} else {
		calc {
			mod(x * m, m);
			mod(x*m - m, m);
			{ lemma_mul_properties(); }
			mod(x*m - mul(1,m), m);
			{ lemma_mul_properties(); }
			mod((x-1)*m, m); 
			{ lemma_mod_multiples_basic(x-1, m); }
			0;
		}		
	}
}

//
//////////////////////////////////////////////////////////////////////////////

static lemma lemma_mod_multiples_vanish(a:int, b:int, m:int)
	decreases if a>0 then a else -a;
	requires 0 < m;
	ensures (m*a + b) % m == b % m;
{
	if (0 == a)
	{
		calc {
			m*a + b;
			INTERNAL_mul(m,0) + b;
				{ lemma_mul_basics_forall(); }
			0 + b;
			b;
		}
		assert (m*a + b) % m == b % m;
	} else if (0 < a) {
		calc {
			(m*a + b) % m;
			(m*((a-1)+1) + b) % m;
				{ lemma_mul_is_distributive_forall(); }
			(m*(a-1)+mul(m,1) + b) % m;
				{ lemma_mul_basics_forall(); }
			(m*(a-1) + m + b) % m;
				{ lemma_mod_multiples_vanish(a-1,m+b,m); }
			(m + b) % m;
				{
					reveal_mod_recursive();
					if (b < 0)
					{
						assert b % m == (b + m) % m;
					} else if (m <= b + m) {
						assert (b + m) % m == (b + m - m) % m == b % m;
					} else {
					}
				}
			b % m;
		}
	} else {
		calc {
			(m*a + b) % m;
			(m*((a+1)-1) + b) % m;
				{ lemma_mul_is_distributive_forall(); }
			(m*(a+1)+mul(m,-1) + b) % m;
				{ lemma_mul_is_mul_boogie(m,-1); }
			(m*(a+1) - m + b) % m;
				{ lemma_mod_multiples_vanish(a+1,-m+b,m); }
			(- m + b) % m;
				{
					reveal_mod_recursive();
					if (b - m < 0)
					{
						assert (b - m) % m == (b - m + m) % m == b % m;
					} else if (m <= b) {
						assert b % m == (b - m) % m;
					} else {
					}
				}
			b % m;
		}
	}
}

static lemma lemma_mul_mod_noop(x:nat, y:nat, m:int)
	requires 0 <= x;
	requires 0 < m;
	ensures INTERNAL_mul(x % m, y % m) % m == INTERNAL_mul(x,y) % m;
{
	calc {
		(x*y) % m;
			{
				lemma_fundamental_div_mod(x,m);
				lemma_fundamental_div_mod(y,m);
			}
		((m*(x/m) + x%m) * (m*(y/m) + y%m)) % m;
			{ lemma_mul_is_distributive_add_forall(); }
		((m*(x/m) + x%m) * (m*(y/m)) +
			(m*(x/m) + x%m) * (y%m)) % m;
			{ lemma_mul_is_commutative_forall(); }
		((m*(y/m)) * (m*(x/m) + x%m) +
			(y%m) * (m*(x/m) + x%m)) % m;
			{ lemma_mul_is_distributive_add_forall(); }
		((m*(y/m)) * (m*(x/m)) + (m*(y/m)) * (x%m) +
			(y%m) * (m*(x/m)) + (y%m)*(x%m)) % m;
			{ lemma_mul_is_commutative_forall(); }
		((m*(y/m)) * (m*(x/m)) + (m*(y/m)) * (x%m) +
			(m*(x/m)) * (y%m) + (y%m)*(x%m)) % m;
			{ lemma_mul_is_associative_forall(); }
		(m*((y/m)*m*(x/m)) + m*((y/m)*(x%m)) +
			m*((x/m) * (y%m)) + (y%m)*(x%m)) % m;
			{ lemma_mul_is_distributive_add_forall(); }
		(m*((y/m)*m*(x/m) + (y/m)*(x%m) + (x/m) * (y%m)) +
			(y%m)*(x%m)) % m;
			{
				lemma_div_pos_is_pos(y,m);
				lemma_div_pos_is_pos(x,m);
				lemma_mod_pos_bound(x,m);
				lemma_mod_pos_bound(y,m);
				lemma_mul_nonnegative_forall();
				assert 0 <= ((y/m)*m*(x/m) + (y/m)*(x%m) + (x/m) * (y%m));
				assert 0 <= (y%m)*(x%m);
				lemma_mod_multiples_vanish(
					((y/m)*m*(x/m) + (y/m)*(x%m) + (x/m) * (y%m)),
					(y%m)*(x%m),
					m);
			}
		((y%m) * (x%m)) % m;
			{ lemma_mul_is_commutative_forall(); }
		((x%m) * (y%m)) % m;
	}
}

