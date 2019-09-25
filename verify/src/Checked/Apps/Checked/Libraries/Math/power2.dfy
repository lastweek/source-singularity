include "..\DafnyCC\Base.dfy"
include "..\..\..\Trusted\Spec\Libraries\Math\power2.dfy"
include "..\..\..\Trusted\Spec\Libraries\Math\power.dfy"
include "mul.dfy"
include "div.dfy"

/*
 * Real definition in spec directory (included above);
 * but here's a commented copy for your edification.

static function {:hidden} power2(exp: nat) : nat 
    ensures power2(exp) > 0;
{
    if (exp==0) then
        1
    else
        2*power2(exp-1)
}
*/

static lemma lemma_power2_strictly_increases(e1: int, e2: int)
    requires 0 <= e1 < e2;
    ensures power2(e1) < power2(e2);
    decreases e2;
{
    if e1+1 == e2 {
		reveal_power2();
    } else {
		reveal_power2();
        lemma_power2_strictly_increases(e1, e2-1);
    }
}

static lemma lemma_power2_increases(e1: int, e2: int)
    requires 0 <= e1 <= e2;
    ensures power2(e1) <= power2(e2);
    decreases e2;
{
    if e2 == e1 {
    } else {
		    reveal_power2();
        lemma_power2_increases(e1, e2-1);
    }
}

static lemma lemma_power2_strictly_increases_converse(e1: int, e2: int)
	requires 0 <= e1;
	requires 0 < e2;
    requires power2(e1) < power2(e2);
    ensures e1 < e2;
{
    if (e1 >= e2)
	{ 
		lemma_power2_increases(e2, e1);
		assert false;
    }
}

static lemma lemma_power2_increases_converse(e1: int, e2: int)
	requires 0 < e1;
	requires 0 < e2;
    requires power2(e1) <= power2(e2);
    ensures e1 <= e2;
{
    if (e1 > e2) {
		lemma_power2_strictly_increases(e2, e1);
		assert false;
    }
}

static lemma lemma_power2_adds(e1:nat, e2:nat)
    decreases e2;
	ensures power2(e1 + e2) == power2(e1) * power2(e2);
{
	if e2 == 0 {
		lemma_mul_properties();
		reveal_power2();
	} else {
		var e2min1 := e2 - 1;
		calc {
			power2(e1 + e2);
			{ reveal_power2(); }
			power2(e1 + e2 - 1) * 2;
			power2(e1 + e2min1) * 2;
			{ lemma_power2_adds(e1, e2min1); }
			(power2(e1) * power2(e2min1)) * 2;
			{ lemma_mul_is_mul_boogie(power2(e1) * power2(e2min1), 2); }
			INTERNAL_mul(INTERNAL_mul(power2(e1), power2(e2min1)), 2);
			{ lemma_mul_is_associative(power2(e1), power2(e2min1), 2); }
			INTERNAL_mul(power2(e1), INTERNAL_mul(power2(e2min1), 2));
			{ lemma_mul_is_mul_boogie(power2(e2min1), 2); }
			power2(e1) * (power2(e2min1) * 2);
			{ reveal_power2(); }
			power2(e1) * power2(e2);
		}
		assert power2(e1 + e2) == power2(e1) * power2(e2);
	}
}

static lemma lemma_power2_div_is_sub(x:int, y:int)
	requires 0 <= x <= y;
	ensures power2(y - x) == power2(y) / power2(x) >= 0;
{
	calc {
		power2(y) / power2(x);
		{ lemma_power2_adds(y-x, x); }
		(power2(y-x)*power2(x)) / power2(x);
		{ lemma_div_by_multiple(power2(y-x), power2(x)); }
		power2(y-x);
	}
}

static lemma lemma_2toX()
	ensures power2(64) == 18446744073709551616;
	ensures power2(32) == 4294967296;
	ensures power2(24) == 16777216;
	ensures power2(19) == 524288;
	ensures power2(16) == 65536;
	ensures power2(8) ==  256;
{
  lemma_2to32();
  lemma_2to64();
}

static lemma lemma_2to32()
	ensures power2(32) == 4294967296;
	ensures power2(24) == 16777216;
	ensures power2(19) == 524288;
	ensures power2(16) == 65536;
	ensures power2(8)  == 256;
{
  assert unroll(1) && unroll(2) && unroll(3) && unroll(4) && unroll(5) && unroll(6) && unroll(7) && unroll(8) && unroll(9);
	reveal_power2();
  assert(32 == power2(5));
	assert(512 == power2(9));
  assert(4096 == power2(12));
	assert(262144 == power2(18));
	assert(268435456 == power2(28));
}

static lemma lemma_2to64()
	ensures power2(64) == 18446744073709551616;
{
  assert unroll(1) && unroll(2) && unroll(3) && unroll(4) && unroll(5) && unroll(6) && unroll(7) && unroll(8) && unroll(9);
	lemma_2to32();
	reveal_power2();
	assert power2(40) ==     0x10000000000;
	assert power2(48) ==   0x1000000000000;
	assert power2(56) == 0x100000000000000;
}

static lemma lemma_power2_0_is_1()
	ensures power2(0) == 1;
{
	reveal_power2();
}

static lemma lemma_power2_1_is_2()
	ensures power2(1) == 2;
{
	lemma_power2_0_is_1();
	reveal_power2();
}



static lemma lemma_div_power2toX()
	ensures forall x {:trigger INTERNAL_div(x, power2(24))} :: x >= 0 ==> x / power2(24) == x / 16777216;
	ensures forall x {:trigger INTERNAL_div(x, power2(16))} :: x >= 0 ==> x / power2(16) == x / 65536;
	ensures forall x {:trigger INTERNAL_div(x, power2(8))}  :: x >= 0 ==> x / power2(8)  == x / 256;
{
	lemma_2toX();
	reveal_power2();
	reveal_INTERNAL_div_recursive();
	forall x | x >= 0 
		ensures x / power2(24) == x / 16777216 && x / power2(16) == x / 65536 && x / power2(8)  == x / 256;
	{
		lemma_div_2_to_8(x);
		lemma_div_2_to_16(x);
		lemma_div_2_to_24(x);
	}
}

static lemma lemma_div_2_to_8(x:int)
	requires x >= 0;
	ensures x / power2(8) == x / 256;
{
	lemma_2toX();
	reveal_INTERNAL_div_recursive();	
	if (x < 256) {
	} else {
		lemma_div_2_to_8(x - 256);
	}
}

static lemma lemma_div_2_to_16(x:int)
	requires x >= 0;
	ensures x / power2(16) == x / 65536;
{
	lemma_2toX();
	reveal_INTERNAL_div_recursive();	
	if (x < 65536) {
	} else {
		lemma_div_2_to_16(x - 65536);
	}
}

static lemma lemma_div_2_to_24(x:int)
	requires x >= 0;
	ensures x / power2(24) == x / 16777216;
{
	lemma_2toX();
	reveal_INTERNAL_div_recursive();	
	if (x < 16777216) {
	} else {
		lemma_div_2_to_24(x - 16777216);
	}
}		

static lemma lemma_power2_is_power_2(x:nat)
	ensures power2(x) == power(2,x);
{
	if (x==0)
	{
		reveal_power2();
		reveal_power();
	}
	else
	{
		calc {
			power2(x);
				{ reveal_power2(); }
			2*power2(x-1);
				{ lemma_mul_is_mul_boogie(2,power2(x-1)); }
			INTERNAL_mul(2,power2(x-1));
				{ lemma_power2_is_power_2(x-1); }
			INTERNAL_mul(2,power(2,x-1));
				{ reveal_power(); }
			power(2,x);
		}
	}
}

lemma {:timeLimit 100} lemma_word_to_bytes_unique_specific_power2(a:int, b:int)
  requires a % 256 == b % 256;
  requires (a / power2(8)) % 256 == (b / power2(8)) % 256;
  requires (a / power2(16)) % 256 == (b / power2(16)) % 256;
  requires a / power2(24) == b / power2(24);
  requires 0 <= a;
  requires 0 <= b;
  ensures  a == b;
{
	lemma_div_power2toX();
}

