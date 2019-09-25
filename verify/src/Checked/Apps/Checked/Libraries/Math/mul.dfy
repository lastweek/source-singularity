// The real definitions live in DafnyPrelude, but here's a
// commented copy for your perusal.
// 
// static function INTERNAL_mul_recursive(x:int, y:int) : int
// {
// 	if x >= 0 then INTERNAL_mul_pos(x, y)
// 	else -1*INTERNAL_mul_pos(-1*x, y)
// }
// 
// static function INTERNAL_mul_pos(x:int, y:int) : int
// 	requires x >= 0;
// {
// 	if x == 0 then 0
// 	else y + mul_pos(x - 1, y)
// }

static function mul(x:int, y:int) : int { INTERNAL_mul(x,y) }

//////////////////////////////////////////////////////////////////////////////
//
// Core lemmas, with named arguments.
//
//////////////////////////////////////////////////////////////////////////////

static lemma lemma_mul_basics(x:int)
	ensures INTERNAL_mul(0, x) == 0;
	ensures INTERNAL_mul(x, 0) == 0;
	ensures INTERNAL_mul(1, x) == x;
	ensures INTERNAL_mul(x, 1) == x;
{
	reveal_INTERNAL_mul_recursive();
	lemma_mul_is_commutative(0,x);
	lemma_mul_is_commutative(1,x);
}

static lemma lemma_mul_is_commutative(x:int, y:int)
	ensures INTERNAL_mul(x, y) == INTERNAL_mul(y, x);
{
	calc {
		INTERNAL_mul(x,y);
		{ lemma_mul_is_mul_boogie(x,y); }
		INTERNAL_mul_boogie(x,y);
		INTERNAL_mul_boogie(y,x);
		{ lemma_mul_is_mul_boogie(y,x); }
		INTERNAL_mul(y,x);
	}
}

static lemma lemma_mul_ordering(x:int, y:int, b:int)
	requires 0 < x;
	requires 0 < y;
	requires 0 <= INTERNAL_mul(x,y) < b;
	ensures x < b && y < b;
{
	lemma_mul_is_mul_boogie(x,y);
}

static lemma lemma_mul_ordering_general()
	ensures forall x:int, y:int, b:int :: (0 < x && 0 < y && 0 <= INTERNAL_mul(x,y) < b) ==> x < b && y < b;
{
	forall x:int, y:int, b:int | 0 < x && 0 < y && 0 <= INTERNAL_mul(x,y) < b
  	ensures x < b && y < b;
	{
			lemma_mul_ordering(x, y, b);
	}
}

static lemma lemma_mul_is_mul_boogie(x:int, y:int)
	ensures INTERNAL_mul(x, y) == INTERNAL_mul_boogie(x,y);
{
	reveal_INTERNAL_mul_recursive();
	if (x >= 0) {
		lemma_mul_pos_is_mul_boogie(x,y);
	} else {
	    lemma_mul_pos_is_mul_boogie(INTERNAL_mul_boogie(-1,x), y);
	}
}

static lemma lemma_mul_pos_is_mul_boogie(x:int, y:int)
	requires x >= 0;
	ensures INTERNAL_mul(x, y) == INTERNAL_mul_boogie(x,y);
{
	reveal_INTERNAL_mul_recursive();
	if (x == 0) {
	} else {
		lemma_mul_pos_is_mul_boogie(x-1,y);
		assert INTERNAL_mul(x - 1, y) == INTERNAL_mul_boogie((x-1),y);
	}
}

static lemma lemma_mul_strict_inequality(x:int, y:int, z:int)
	requires x < y;
	requires z > 0;
	ensures  INTERNAL_mul(x, z) < INTERNAL_mul(y, z);
{
	calc {
		INTERNAL_mul(x, z);
		== { lemma_mul_is_mul_boogie(x, z); }
		INTERNAL_mul_boogie(x, z);
		<
		INTERNAL_mul_boogie(y, z);
		== { lemma_mul_is_mul_boogie(y, z); }
		INTERNAL_mul(y,z);
	}
}	

static lemma lemma_mul_inequality(x:int, y:int, z:int)
	requires x <= y;
	requires z >= 0;
	ensures  INTERNAL_mul(x, z) <= INTERNAL_mul(y, z);
{
	calc {
		INTERNAL_mul(x, z);
		== { lemma_mul_is_mul_boogie(x, z); }
		INTERNAL_mul_boogie(x, z);
		<=
		INTERNAL_mul_boogie(y, z);
		== { lemma_mul_is_mul_boogie(y, z); }
		INTERNAL_mul(y,z);
	}
}	

static lemma lemma_mul_left_inequality(x:int, y:int, z:int)
	requires x > 0;
	ensures y <= z ==> INTERNAL_mul(x, y) <= INTERNAL_mul(x, z);
	ensures y < z ==> INTERNAL_mul(x, y) < INTERNAL_mul(x, z);
{
	lemma_mul_is_commutative_forall();
	lemma_mul_inequality_forall();
	lemma_mul_strict_inequality_forall();
}

static lemma lemma_mul_strict_inequality_converse(x:int, y:int, z:int)
	requires INTERNAL_mul(x, z) < INTERNAL_mul(y, z);
	requires z >= 0;
	ensures  x < y;
{
	if (x >= y)
	{
		lemma_mul_inequality(y, x, z);
		assert INTERNAL_mul(x, z) >= INTERNAL_mul(y, z);
		assert false;
	}
}	

static lemma lemma_mul_inequality_converse(x:int, y:int, z:int)
	requires INTERNAL_mul(x, z) <= INTERNAL_mul(y, z);
	requires z > 0;
	ensures  x <= y;
{
	if (x > y)
	{
		lemma_mul_strict_inequality(y, x, z);
		assert INTERNAL_mul(x, z) > INTERNAL_mul(y, z);
		assert false;
	}
}	

static lemma lemma_mul_is_distributive_add(x:int, y:int, z:int)
	ensures INTERNAL_mul(x, y + z) == INTERNAL_mul(x, y) + INTERNAL_mul(x, z);
	decreases if x >=0 then x else INTERNAL_mul_boogie(-1, x);
{
	reveal_INTERNAL_mul_recursive();
	if (x == 0) {
	} else if (x > 0) {
		lemma_mul_is_distributive_add(x - 1, y, z);
	} else {
		lemma_mul_is_distributive_add(x + 1, y, z);
	}
}

static lemma lemma_mul_is_distributive_sub(x:int, y:int, z:int)
	ensures INTERNAL_mul(x, y - z) == INTERNAL_mul(x, y) - INTERNAL_mul(x, z);
	decreases if x >=0 then x else INTERNAL_mul_boogie(-1, x);
{
	reveal_INTERNAL_mul_recursive();
	if (x == 0) {
	} else if (x > 0) {
		lemma_mul_is_distributive_sub(x - 1, y, z);
	} else {
		lemma_mul_is_distributive_sub(x + 1, y, z);
	}
}

static lemma lemma_mul_is_associative(x:int, y:int, z:int)
	ensures x * (y * z) == (x * y) * z;
{
	calc {
		INTERNAL_mul(x, INTERNAL_mul(y, z));
		{ lemma_mul_is_mul_boogie(y, z); }
		INTERNAL_mul(x, INTERNAL_mul_boogie(y, z));
		{ lemma_mul_is_mul_boogie(x, INTERNAL_mul_boogie(y, z)); }
		INTERNAL_mul_boogie(x, INTERNAL_mul_boogie(y, z));
		{ lemma_mul_is_mul_boogie(x, y); }
		INTERNAL_mul_boogie(INTERNAL_mul(x, y), z);
		{ lemma_mul_is_mul_boogie(INTERNAL_mul(x,y), z); }
		INTERNAL_mul(INTERNAL_mul(x, y), z);
	}
}

static lemma lemma_mul_commutes_with_2(x:int, y:int)
	ensures (x*y)*2 == x*(y*2);
{
	reveal_INTERNAL_mul_recursive();
	calc {
		(x*y)*2;
		{ reveal_INTERNAL_mul_recursive(); }
		INTERNAL_mul_recursive(x, y)*2;
		{ lemma_mul_is_mul_boogie(x, y); }
		INTERNAL_mul_boogie(x,y)*2;
		INTERNAL_mul_boogie(x, (y*2));
		{ lemma_mul_is_mul_boogie(x, y*2); }
		INTERNAL_mul_recursive(x, (y*2));
		{ reveal_INTERNAL_mul_recursive(); }
		x*(y*2);
	}
}

static lemma lemma_mul_nonzero(x:int, y:int)
	ensures INTERNAL_mul(x, y) != 0 <==> x != 0 && y != 0;
{
	lemma_mul_is_mul_boogie(x,y);
}

static lemma lemma_mul_nonnegative(x:int, y:int)
	ensures 0 <= x && 0 <= y ==> 0 <= INTERNAL_mul(x,y);
{
	lemma_mul_is_mul_boogie(x,y);
}

static lemma lemma_mul_strictly_increases(x:int, y:int)
	ensures (1 < x && 0 < y) ==> (y < INTERNAL_mul(x,y));
{
	if (1 < x && 0 < y)
	{
		lemma_mul_strict_inequality(1,x,y);
		lemma_mul_is_mul_boogie(1,y);
		assert y < INTERNAL_mul(x,y);
	}
}

static lemma lemma_mul_increases(x:int, y:int)
	ensures (0 < x && 0 < y) ==> (y <= INTERNAL_mul(x,y));
{
	if (0 < x && 0 < y)
	{
		lemma_mul_inequality(1,x,y);
		lemma_mul_is_mul_boogie(1,y);
		assert y <= INTERNAL_mul(x,y);
	}
}

static lemma lemma_mul_positive(x:int, y:int)
	ensures (0 <= x && 0 <= y) ==> (0 <= INTERNAL_mul(x,y));
{
	if (0 <= x && 0 <= y)
	{
		lemma_mul_is_mul_boogie(x,y);
		assert 0 <= INTERNAL_mul(x,y);
	}
}

static lemma lemma_mul_strictly_positive(x:int, y:int)
	ensures (0 < x && 0 < y) ==> (0 < INTERNAL_mul(x,y));
{
	if (0 < x && 0 < y)
	{
		lemma_mul_is_mul_boogie(x,y);
		assert 0 < INTERNAL_mul(x,y);
	}
}

static lemma lemma_mul_unary_negation(x:int, y:int)
	ensures (-x)*y == -(x*y) == x*(-y);
{
	calc {
		(-x)*y;
			{ lemma_mul_is_mul_boogie(-1,x); }
		INTERNAL_mul(-1,x)*y;
			{ lemma_mul_is_associative(-1,x,y); }
		INTERNAL_mul(-1,x*y);
			{ lemma_mul_is_mul_boogie(-1,x*y); }
		-(x*y);
	}
	calc {
		x*(-y);
			{ lemma_mul_is_commutative_forall(); }
		(-y)*x;
			{ lemma_mul_is_mul_boogie(-1,y); }
		INTERNAL_mul(-1,y)*x;
			{ lemma_mul_is_associative(-1,y,x); }
		INTERNAL_mul(-1,y*x);
			{ lemma_mul_is_mul_boogie(-1,y*x); }
		-(y*x);
			{ lemma_mul_is_commutative_forall(); }
		-(x*y);
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

static lemma lemma_mul_basics_forall()
	ensures forall x:int :: INTERNAL_mul(0, x) == 0;
	ensures forall x:int :: INTERNAL_mul(x, 0) == 0;
	ensures forall x:int :: INTERNAL_mul(1, x) == x;
	ensures forall x:int :: INTERNAL_mul(x, 1) == x;
{
	forall (x:int)
		ensures INTERNAL_mul(0, x) == 0;
		ensures INTERNAL_mul(x, 0) == 0;
		ensures INTERNAL_mul(1, x) == x;
		ensures INTERNAL_mul(x, 1) == x;
	{
		lemma_mul_basics(x);
	}
}

static lemma lemma_mul_is_commutative_forall()
	ensures forall x:int, y:int :: INTERNAL_mul(x, y) == INTERNAL_mul(y, x);
{
	forall (x:int, y:int)
		ensures INTERNAL_mul(x, y) == INTERNAL_mul(y, x);
	{
		lemma_mul_is_commutative(x, y);
	}
}

static lemma lemma_mul_ordering_forall()
	ensures forall x:int, y:int, b:int ::
		0 < x && 0 < y && 0 <= INTERNAL_mul(x,y) < b
		==> x < b && y < b;
{
	forall (x:int, y:int, b:int | 0 < x && 0 < y && 0 <= INTERNAL_mul(x,y) < b)
		ensures x < b && y < b;
	{
		lemma_mul_basics(b);
		lemma_mul_ordering(x,y,b);
	}
}

static lemma lemma_mul_strict_inequality_forall()
	ensures  forall x:int, y:int, z:int ::
		x < y && z>0 ==> INTERNAL_mul(x, z) < INTERNAL_mul(y, z);
{
	forall (x:int, y:int, z:int | x < y && z>0)
		ensures INTERNAL_mul(x, z) < INTERNAL_mul(y, z);
	{
		lemma_mul_strict_inequality(x, y, z);
	}
}

static lemma lemma_mul_inequality_forall()
	ensures  forall x:int, y:int, z:int ::
		x <= y && z>=0 ==> INTERNAL_mul(x, z) <= INTERNAL_mul(y, z);
{
	forall (x:int, y:int, z:int | x <= y && z>=0)
		ensures INTERNAL_mul(x, z) <= INTERNAL_mul(y, z);
	{
		lemma_mul_inequality(x, y, z);
	}
}

static lemma lemma_mul_strict_inequality_converse_forall()
	ensures  forall x:int, y:int, z:int ::
		INTERNAL_mul(x, z) < INTERNAL_mul(y, z) && z>=0 ==> x < y;
{
	forall (x:int, y:int, z:int | INTERNAL_mul(x,z) < INTERNAL_mul(y,z) && z>=0)
		ensures x < y;
	{
		lemma_mul_strict_inequality_converse(x,y,z);
	}
}

static lemma lemma_mul_inequality_converse_forall()
	ensures  forall x:int, y:int, z:int ::
		INTERNAL_mul(x, z) <= INTERNAL_mul(y, z) && z>0 ==> x <= y;
{
	forall (x:int, y:int, z:int | INTERNAL_mul(x,z) <= INTERNAL_mul(y,z) && z>0)
		ensures x <= y;
	{
		lemma_mul_inequality_converse(x,y,z);
	}
}

static lemma lemma_mul_is_distributive_add_forall()
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(x, y + z) == INTERNAL_mul(x, y) + INTERNAL_mul(x, z);
{
	forall (x:int, y:int, z:int)
		ensures INTERNAL_mul(x, y + z) == INTERNAL_mul(x, y) + INTERNAL_mul(x, z);
	{
		lemma_mul_is_distributive_add(x,y,z);
	}
}

static lemma lemma_mul_is_distributive_sub_forall()
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(x, y - z) == INTERNAL_mul(x, y) - INTERNAL_mul(x, z);
{
	forall (x:int, y:int, z:int)
		ensures INTERNAL_mul(x, y - z) == INTERNAL_mul(x, y) - INTERNAL_mul(x, z);
	{
		lemma_mul_is_distributive_sub(x,y,z);
	}
}

static lemma lemma_mul_is_distributive_forall()
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(x, y + z) == INTERNAL_mul(x, y) + INTERNAL_mul(x, z);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(x, y - z) == INTERNAL_mul(x, y) - INTERNAL_mul(x, z);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(y + z, x) == INTERNAL_mul(y, x) + INTERNAL_mul(z, x);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(y - z, x) == INTERNAL_mul(y, x) - INTERNAL_mul(z, x);
{
	lemma_mul_is_distributive_add_forall();
	lemma_mul_is_distributive_sub_forall();
	lemma_mul_is_commutative_forall();
}

static lemma lemma_mul_is_associative_forall()
	ensures forall x:int, y:int, z:int :: x * (y * z) == (x * y) * z;
{
	forall (x:int, y:int, z:int)
		ensures x * (y * z) == (x * y) * z;
	{
		lemma_mul_is_associative(x,y,z);
	}
}

static lemma lemma_mul_commutes_with_2_forall()
	ensures forall x:int, y:int :: (x*y)*2 == x*(y*2);
{
	forall (x:int, y:int)
		ensures (x*y)*2 == x*(y*2);
	{
		lemma_mul_commutes_with_2(x,y);
	}
}

static lemma lemma_mul_nonzero_forall()
	ensures forall x:int, y:int :: INTERNAL_mul(x, y) != 0 <==> x != 0 && y != 0;
{
	forall (x:int, y:int)
		ensures INTERNAL_mul(x, y) != 0 <==> x != 0 && y != 0;
	{
		lemma_mul_nonzero(x,y);
	}
}

static lemma lemma_mul_nonnegative_forall()
	ensures forall x:int, y:int :: 0 <= x && 0 <= y ==> 0 <= INTERNAL_mul(x,y);
{
	forall (x:int, y:int | 0 <= x && 0 <= y)
		ensures 0 <= INTERNAL_mul(x,y);
	{
		lemma_mul_nonnegative(x,y);
	}
}

static lemma lemma_mul_strictly_increases_forall()
	ensures forall x:int, y:int :: (1 < x && 0 < y) ==> (y < INTERNAL_mul(x,y));
{
	forall (x:int, y:int | 1 < x && 0 < y)
		ensures y < INTERNAL_mul(x,y);
	{
		lemma_mul_strictly_increases(x,y);
	}
}

static lemma lemma_mul_increases_forall()
	ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (y <= INTERNAL_mul(x,y));
{
	forall (x:int, y:int | 0 < x && 0 < y)
		ensures y <= INTERNAL_mul(x,y);
	{
		lemma_mul_increases(x,y);
	}
}

static lemma lemma_mul_positive_forall()
	ensures forall x:int, y:int :: (0 <= x && 0 <= y) ==> (0 <= INTERNAL_mul(x,y));
{
	forall (x:int, y:int | 0 <= x && 0 <= y)
		ensures 0 <= INTERNAL_mul(x,y);
	{
		lemma_mul_positive(x,y);
	}
}

static lemma lemma_mul_strictly_positive_forall()
	ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (0 < INTERNAL_mul(x,y));
{
	forall (x:int, y:int | 0 < x && 0 < y)
		ensures 0 < INTERNAL_mul(x,y);
	{
		lemma_mul_strictly_positive(x,y);
	}
}

//////////////////////////////////////////////////////////////////////////////
//
// The big properties bundle. This can be a little dangerous, because
// it may produce a trigger storm. Whether it does seems to depend on
// how complex the expressions being mul'ed are. If that happens,
// fall back on specifying an individiual _forall lemma.
//
//////////////////////////////////////////////////////////////////////////////

static lemma lemma_mul_properties()
	ensures forall x:int, y:int :: INTERNAL_mul(x, y) == INTERNAL_mul(y, x);
	ensures forall x:int :: INTERNAL_mul(x, 0) == INTERNAL_mul(0, x) == 0;
	ensures forall x:int :: INTERNAL_mul(x, 1) == INTERNAL_mul(1, x) == x;
	ensures forall x:int, y:int, z:int :: x < y && z > 0 ==> INTERNAL_mul(x, z) < INTERNAL_mul(y, z);
	ensures forall x:int, y:int, z:int :: x <= y && z >= 0 ==> INTERNAL_mul(x, z) <= INTERNAL_mul(y, z);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(x, y + z) == INTERNAL_mul(x, y) + INTERNAL_mul(x, z);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(x, y - z) == INTERNAL_mul(x, y) - INTERNAL_mul(x, z);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(y + z, x) == INTERNAL_mul(y, x) + INTERNAL_mul(z, x);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(y - z, x) == INTERNAL_mul(y, x) - INTERNAL_mul(z, x);
	ensures forall x:int, y:int, z:int :: INTERNAL_mul(x, INTERNAL_mul(y, z)) == INTERNAL_mul(INTERNAL_mul(x, y), z);
	ensures forall x:int, y:int :: INTERNAL_mul(x, y) != 0 <==> x != 0 && y != 0;
	ensures forall x:int, y:int :: 0 <= x && 0 <= y ==> 0 <= INTERNAL_mul(x,y);
	ensures forall x:int, y:int, b:int :: 0 < x && 0 < y && 0 <= INTERNAL_mul(x,y) < b ==> x < b && y < b;
	ensures forall x:int, y:int :: (1 < x && 0 < y) ==> (y < INTERNAL_mul(x,y));
	ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (y <= INTERNAL_mul(x,y));
	ensures forall x:int, y:int :: (0 < x && 0 < y) ==> (0 < INTERNAL_mul(x,y));
{
	lemma_mul_is_commutative_forall();
	lemma_mul_basics_forall();
	lemma_mul_strict_inequality_forall();
	lemma_mul_inequality_forall();
	lemma_mul_is_distributive_forall();
	lemma_mul_is_associative_forall();
	lemma_mul_ordering_forall();
	lemma_mul_nonzero_forall();
	lemma_mul_nonnegative_forall();
	lemma_mul_strictly_increases_forall();
	lemma_mul_increases_forall();
	lemma_mul_positive_forall();
}
