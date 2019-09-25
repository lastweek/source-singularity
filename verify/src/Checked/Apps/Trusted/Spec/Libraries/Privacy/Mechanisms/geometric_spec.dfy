module FixedMath {



/* Specification */

function method Power2(exp: nat): nat
    requires exp>=0;
    ensures Power2(exp) > 0;
    ensures exp>0 ==> Power2(exp) == 2*Power2(exp-1);
{
    if (exp==0) then
        1
    else
        2*Power2(exp-1)
}

predicate Lemma_TwoToTheFifteenIs() 
	ensures 32768 == Power2(15);
{
    assert(1 == Power2(0));
    assert(4 == Power2(2));
    assert(16 == Power2(4));
    assert(64 == Power2(6));
    assert(256 == Power2(8));
    assert(1024 == Power2(10));
    assert(4096 == Power2(12));
    assert(16384 == Power2(14));
	true	
}

predicate Lemma_TwoToTheThirtyTwoIs()
    ensures 4294967296 == Power2(32);
{
    assert(Lemma_TwoToTheFifteenIs());
    assert(65536 == Power2(16));
    assert(262144 == Power2(18));
    assert(1048576 == Power2(20));
    assert(4194304 == Power2(22));
    assert(16777216 == Power2(24));
    assert(67108864 == Power2(26));
    assert(268435456 == Power2(28));
    assert(1073741824 == Power2(30));
    true
}

predicate Lemma_TwoToTheSixtyFourIs()
	ensures 18446744073709551616 == Power2(64);
{
	assert(Lemma_TwoToTheThirtyTwoIs());
	assert(17179869184 == Power2(34));
	assert(68719476736 == Power2(36));
	assert(274877906944 == Power2(38));
	assert(1099511627776 == Power2(40));
	assert(4398046511104 == Power2(42));
	assert(17592186044416 == Power2(44));
	assert(70368744177664 == Power2(46));
	assert(281474976710656 == Power2(48));
	assert(1125899906842624 == Power2(50));
	assert(4503599627370496 == Power2(52));
	assert(18014398509481984 == Power2(54));
	assert(72057594037927936 == Power2(56));
	assert(288230376151711744 == Power2(58));
	assert(1152921504606846976 == Power2(60));
	assert(4611686018427387904 == Power2(62));
	true
}

/* Signed and unsigned 32 and 64 bit integers*/

function method int32(x:int) : bool
{
	(Power2(31) * (-1)) <= x < (Power2(31))
}

function int64(x:int) : bool
{
	(Power2(63) * (-1)) <= x < (Power2(63))
}

function method nat32(x:nat) : bool
{
	0 <= x < (Power2(32))
}

function nat64(x:nat) : bool
{
	0 <= x < Power2(64)
}

function method intToNat32(x :int) : nat
	requires int32(x);
	requires x >= 0;
	ensures nat32(intToNat32(x));
{
	var y :nat := x;
	// I'd really like to use Power2IsMonotonic(x:nat, y:nat)
	// but I wrote that as a ghost method. Can that not be used here?
	assert(Power2(15) < Power2(17));
	assert(Power2(17) < Power2(19));
	assert(Power2(19) < Power2(21));
	assert(Power2(21) < Power2(23));
	assert(Power2(23) < Power2(25));
	assert(Power2(25) < Power2(27));
	assert(Power2(27) < Power2(29));
	assert(Power2(29) < Power2(31));
	y
}

/* These predicatesare necessary as they allows for Z3 to recognize certain 
constants in programs without the tedious buildup of the Power2 ladder */

predicate GivenIntIsInt32(x:int)
	requires x < 2147483648;
	requires x >= -2147483648;
	ensures int32(x);
{
	assert Lemma_TwoToTheThirtyTwoIs();
	assert(2147483648 == Power2(31));
	assert(-2147483648 == (-1)* Power2(31));
	true
}

predicate GivenNatIsNat32(x:nat) 
	requires 0 <= x < 4294967296;
	ensures nat32(x);
{
	assert Lemma_TwoToTheThirtyTwoIs();
	assert (4294967296 == Power2(32));
	true
}

predicate GivenNatIsNat64(x:nat)
	requires 0 <= x < 18446744073709551616;
	ensures nat64(x);
{
	assert Lemma_TwoToTheSixtyFourIs();
	true
}

predicate AllAreNat32()
	ensures forall x :: (0 <= x < 4294967296) ==> nat32(x);
{
	assert Lemma_TwoToTheThirtyTwoIs();
	assert (4294967296 == Power2(32));
	true
}

predicate AllAreNat64()
	ensures forall x :: (0 <= x < 18446744073709551616) ==> nat64(x);
{
	assert Lemma_TwoToTheSixtyFourIs();
	assert (18446744073709551616 == Power2(64));
	true
}

predicate AllAreInt32()
	ensures forall x :: (-2147483648 <= x < 2147483648) ==> int32(x);
{
	assert Lemma_TwoToTheThirtyTwoIs();
	assert(-2147483648 == (-1) * Power2(31));
	assert (2147483648 == Power2(31));
	true
}

predicate CanWePleaseTalkAboutNumbers()
	ensures forall x :: (0 <= x < 4294967296) ==> nat32(x);
	ensures forall x :: (0 <= x < 18446744073709551616) ==> nat64(x);
	ensures forall x :: (-2147483648 <= x < 2147483648) ==> int32(x);
{
	assert(AllAreInt32());
	assert(AllAreNat64());
	assert(AllAreNat32());
	true
}	

/*
	Lemmas that are useful in verification
*/

ghost method Power2IsDistributive(x:nat, y:nat, z:nat)
	requires x + y == z;
	ensures (Power2(x) * Power2(y) == Power2(z));
{}

ghost method Power2Mult(x :nat, y :nat, z :nat)
	requires x < Power2(y);
	ensures x * Power2(z) <= Power2(y) * Power2(z);
{}

ghost method MultiplicationIsMonotonic(x :nat, y :nat, x' :nat, y':nat)
	requires x < x';
	requires y < y';
	ensures (x * y) < (x' * y');
{}

ghost method MultiplicationIsMonotonic2(x :nat, y :nat, x' :nat, y':nat)
	requires x <= x';
	requires y <= y';
	ensures (x * y) <= (x' * y');
{}

ghost method ThirtyTwoBitMultIs64Bit(x : nat, y :nat, z :nat)
	requires x < Power2(32);
	requires y < Power2(32);
	requires x * y == z;
	
	ensures z < Power2(64);
{
	assert AllAreNat64();
	Power2IsDistributive(32,32,64);
	assert Power2(32) * Power2(32) == Power2(64);
	MultiplicationIsMonotonic(x,y,Power2(32),Power2(32));
}

ghost method DivideBy2ToThe32 (x :nat, y :nat)
	requires x < Power2(64);
	requires y == x / Power2(32);

	ensures y < Power2(32);
{
	Power2IsDistributive(32,32,64);
	var x' := y * Power2(32);
	assert(x' <= x);
	assert(x' < Power2(64));
	assert(Power2(32) * Power2(32) == Power2(64));
	assert(y < Power2(32));
}

/* Integer version of Log2 */

function method Log2Nat(x : nat) : nat
	requires x > 0;
	ensures Log2Nat(x) >= 0;
	ensures Power2(Log2Nat(x)) <= x < Power2(1+Log2Nat(x));
{	
	
	if x == 1 then 
		assert(Power2(0) <= x < Power2(1 + 0));
		0
	else
		// How does it know this automatically!?
		1 + Log2Nat(x / 2)
}

predicate Lemma_Power2IsMonotonic(e1:nat, e2:nat)
    requires e1 <= e2;
    ensures Power2(e1) <= Power2(e2);
    ensures Lemma_Power2IsMonotonic(e1, e2);
    decreases e2;
{
    if e2 == e1 then
        true
    else
        Lemma_Power2IsMonotonic(e1, e2-1)
}

/*
	This takes a lot of time to prove
*/
predicate Lemma_Log2NatIsMonotonic(x:nat, y:nat)
	requires x > 0;
	requires y > 0;
	requires x <= y;
	ensures Log2Nat(x) <= Log2Nat(y);
	ensures Lemma_Log2NatIsMonotonic(x, y);
	decreases y-x;
/*{
	if (x == y) then
		assert(Log2Nat(x) == Log2Nat(y));
		true
	else if (x == y - 1) then
		assert(Lemma_Log2NatPlusOne(x,y));
		true
	else
		Lemma_Log2NatIsMonotonic(x, y-1)
}*/

predicate Log2Power2(x: nat)
	requires x > 0;
	//ensures Log2Nat(Power2(x)) == x ==> Log2Nat(Power2(x+1)) == x+1;
	ensures Log2Nat(Power2(x)) == x;
	ensures Log2Power2(x);
{
	if x == 1 then
		assert(Power2(x) == 2);
		assert(Log2Nat(Power2(x)) == 1);
		true
	else
		Log2Power2(x-1)
}

predicate Log4294967296()
	ensures nat32(Log2Nat(4294967296));
{
	assert(AllAreNat32());
	assert(Lemma_TwoToTheThirtyTwoIs);
	assert(Log2Power2(32));
	assert(Log2Nat(4294967296) == 32);
	true
}

ghost method Log2Nat32(x :nat)
	requires nat32(x);
	requires x > 0;
	ensures nat32(Log2Nat(x));
	ensures Log2Nat(x) <= 32;
{	
	assert(Lemma_TwoToTheThirtyTwoIs());
	assert(x < 4294967296);
	assert(Log4294967296());
	assert(Lemma_Log2NatIsMonotonic(x, 4294967296));
}

predicate Power2Log2(x: nat)
	requires x > 0;
	ensures Power2(Log2Nat(x)) <= x;
{
	true
}

/***********************************************************************
 Fixed Point Math Specification
************************************************************************/

predicate addFixedSpec(x :fixedpoint, y :fixedpoint, z :fixedpoint)
	requires noOverflow(x) && noOverflow(y) && noOverflow(z);
{
	liftFixed(x) + liftFixed(y) == liftFixed(z)
}

predicate negFixedSpec(x :fixedpoint, z :fixedpoint)
	requires noOverflow(x) && noOverflow(z);
{
	-liftFixed(x) == liftFixed(z)
}

predicate lessThanOrEqualToOne(f :fixedpoint)
	requires noOverflow(f);
{
	liftFixed(f) <= Power2(32)
}

predicate restricted_umulFixedSpec(x :fixedpoint, y :fixedpoint, z :fixedpoint)
	requires noOverflow(x) && noOverflow(y) && noOverflow(z);
	requires lessThanOrEqualToOne(x);
	requires lessThanOrEqualToOne(y);
{
	liftFixed(x) * liftFixed(y) == liftFixed(z)
}

/***********************************************************************
	Implmentation of fixedpoint point reals, including arithmetic operators
 ***********************************************************************/

datatype fixedpoint = Fixed(i: int, j: nat, o: bool); // optional overflow bit
datatype cnat = Cnat(n: nat, c: bool); // nats have an additional carry bit, the semantics of which are to read this as a 33-bit nat.
datatype oint = Oint(i: int, o: bool); // but oints can overflow

/* Shortcut constructor for 32 + 32 bit fixedpoint point number*/

function method F(i : int, j: nat) : fixedpoint
	requires int32(i);
	requires nat32(j);
	requires (i == -2147483648) ==> (j > 0); 
	// If we disallow the singular value F(-2147483648, 0) 
	// then negFixed can flip every isFixed64 safely and 
	// guarantee isFixed64 of the result
	ensures isFixed64(F(i,j));
{
	Fixed(i,j,false)
}

function method liftFixed(f : fixedpoint) : int
	requires noOverflow(f);
{
	(Power2(32) * f.i) + f.j
}

function method isFixed64(f : fixedpoint) : bool
{
	assert CanWePleaseTalkAboutNumbers();
	int32(f.i) && nat32(f.j) && (!f.o) && (f.i==-2147483648 ==> f.j > 0)
}

function method isFixed(f :fixedpoint) : bool
{
	f.o || (f.i==-2147483648 ==> f.j > 0)
}

function method noOverflow(f :fixedpoint) : bool
{
	!f.o
}

function method lt(x: fixedpoint, y: fixedpoint) : bool
	requires !x.o;
	requires !y.o;
{
	((x.i < y.i) || ((x.i == y.i) && (x.j < y.j)))
}

function method eq(x: fixedpoint, y: fixedpoint) : bool
	requires !x.o;
	requires !y.o;
{
	(x.i == y.i) && (x.j == y.j)
}

// TODO: Try and convert gt into !eq && !lt ???.
// TODO: you need a boolean overflow condition.

function method gt(x: fixedpoint, y: fixedpoint) : bool
	requires !x.o;
	requires !y.o;
{
	((x.i > y.i) || ((x.i == y.i) && (x.j > y.j)))
}

// TODO just push the overflow out into the requires here as well. two overflowed fixeds are not necessarily equal.


function method gte(x: fixedpoint, y: fixedpoint) : bool
	requires !x.o;
	requires !y.o;
{
	gt(x, y) || eq(x, y)
}

function method lte(x: fixedpoint, y: fixedpoint) : bool
	requires !x.o;
	requires !y.o;
{
	lt(x, y) || eq(x, y)
}

function method ceil(x : fixedpoint) : oint
	requires isFixed64(x);
	ensures int32(ceil(x).i) || ceil(x).o;
{
	if x.j == 0 then
		Oint(x.i, false)
	else
		add32(x.i, 1)
}

/*
Not used yet

function method eq_eps(x: fixedpoint, y: fixedpoint, z: nat) : bool
	requires nat32(z);
	requires isFixed64(x);
	requires isFixed64(y);
// equality within a certain epsilon tolerance on the fractional part
{
	var yplus := addFixed(y, F(0,z));
	var yminus := addFixed(y, negFixed(F(0,z)));

	if(lt(yminus, x) && lt(x, yplus)) then
		true
	else
		false
}
*/

function method abs(x :fixedpoint) : fixedpoint
	requires isFixed64(x);
	ensures isFixed64(abs(x));
	ensures gte(abs(x), F(0,0));
{
	if(gte(x, F(0,0))) then
		x
	else
		var n := negFixed(x);
		assert(isFixed64(n));
		assert(lt(x, F(0,0)) ==> gt(n, F(0,0)) || !isFixed64(n));
		assert(lt(x, F(0,0)) ==> gt(n, F(0,0)));
		assert(lt(x, F(0,0)));
		assert(gt(n, F(0,0)));
		n
}

/*********************************************************
 * EXTERN definitions                                    *
**********************************************************/
//extern 
function method getRandom32() : nat
	ensures nat32(getRandom32());
/* Wrapper for Intel "rdrand" random number generator. 
   Should be uniformly distributed over the 32 bit space */

//extern 
function method uadd32 (x:nat, y:nat) : cnat
	requires nat32(x);
	requires nat32(y);
	ensures nat32(uadd32(x,y).n);

	// If the result is a 32 bit number, then it is the 
	// sum of the two addends
	ensures (uadd32(x,y).c ==false) ==> 
		(uadd32(x,y).n == (x + y));

	// If the result is a 33 bit number, then it plus
	// 2^32 is the sum of the two addends
	ensures (uadd32(x,y).c==true) ==> 
		(uadd32(x,y).n  + Power2(32) == (x + y));

//extern 
function method add32 (x:int, y:int) : oint
	requires int32(x);
	requires int32(y);
	ensures int32(add32(x,y).i);

	// If the result is a 32 bit integer, then it is the sum
	// of the two addends
	ensures (!add32(x,y).o) ==> (add32(x,y).i == (x + y));
	
	// Certain special cases where we know for a fact that
	// the result will not overflow. Helpful in verification
	ensures (y==0) ==> !add32(x,y).o;
	ensures (x==0) ==> !add32(x,y).o;
	ensures (x > 0) && (y < 0) ==> !add32(x,y).o;
	ensures (x < 0) && (y > 0) ==> !add32(x,y).o;
	ensures (-2147483648 <= (x + y) < 2147483648) ==> !add32(x,y).o;
	ensures !add32(x,y).o ==> (add32(x,y).i == (x + y));

function method oadd32(x :oint, y :oint) : oint
	requires int32(x.i);
	requires int32(y.i);

	ensures int32(oadd32(x,y).i);
{
	if(x.o || y.o) then
		Oint(0, true)
	else
		add32(x.i, y.i)
}

//extern
function method negate (x: int) : oint
	requires int32(x);
	ensures int32(negate(x).i);
	ensures (x != -2147483648) ==> (!negate(x).o);
	ensures (!negate(x).o) ==> (add32(x, negate(x).i).i == 0);
	ensures x > 0 ==> !negate(x).o && (-2147483648 < negate(x).i < 0);
	ensures -2147483648 < x < 0 ==> !negate(x).o && (negate(x).i > 0);
	ensures x == 0 ==> !negate(x).o && (negate(x).i == 0);
	ensures x <= -2147483648 ==> negate(x).o;

/*
  Unfortunately dafny doesn't currently let function methods return
  multiple values so we split this into two functions instead of defining
  yet another single use datatype... although we could do that instead.
*/

//extern 
function method umull32 (x:nat, y: nat) : nat
	requires nat32(x);
	requires nat32(y);
	ensures nat32(umull32(x,y));
	ensures (umull32(x,0) == 0);			// zero, right
	ensures (umull32(0,y) == 0);			// zero, left
	//ensures (umull32(x,y) == umull32(y,x));	// commutativity, not used
	ensures (x > 0 && y > 0) ==> (umull32(x,y) >= 0);
	ensures umull32(x,y) == (x * y) / Power2(32);
	//ensures forall z :nat :: (x <= z) ==> umull32(x,y) < z;
	//ensures forall z :nat :: (y <= z) ==> umull32(x,y) < z;

//extern 
function method umulr32 (x:nat, y: nat) : nat
	requires nat32(x);
	requires nat32(y);
	ensures nat32(umulr32(x,y));
	ensures (umulr32(x,0) == 0);			// zero, right
	ensures (umulr32(0,x) == 0);			// zero, left
	//ensures (umulr32(x,y) == umulr32(y,x)); // commutativity
	ensures (x > 0 && y > 0) ==> (umulr32(x,y) > 0);
	ensures umulr32(x,y) == (x * y % Power2(32));


/*
	High bits are in l, low bits are in r. Unsigned multiplication.
*/

/*ghost method umul32IsCommutative(x: nat, y: nat)
	requires nat32(x);
	requires nat32(y);
	ensures (umull32(x,y) * Power2(32) + umulr32(x,y)) ==
			(umull32(y,x) * Power2(32) + umulr32(y,x));
*///TODO. Is this needed?

/*********************************************************
 * Fixed point operators                                 *
**********************************************************/

function method addFixed(x: fixedpoint, y: fixedpoint) : fixedpoint
	requires isFixed64(x);
	requires isFixed64(y);

	ensures isFixed(addFixed(x,y));
	//ensures lte(x, F(200,0)) && lte(y, F(200,0)) ==> isFixed64(addFixed(x,y));
{
	var frac :cnat := uadd32(x.j, y.j);
	var integral:oint := add32(x.i, y.i);
	
	var i :oint := if(frac.c) then oadd32(integral, Oint(1, false)) else integral;
	assert AllAreInt32();
	//assert lte(x, F(200,0)) && lte(y, F(200,0)) ==> int32(x.i + y.i);
	if i.o || (i.i == -2147483648 && frac.n == 0 ) then
		Fixed(i.i, frac.n, true)
	else
		F(i.i, frac.n)
}

function method negFixed (x: fixedpoint) : fixedpoint
	requires isFixed64(x);
	ensures isFixed64(negFixed(x));
	ensures gt(x, F(0,0)) ==> lt(negFixed(x), F(0,0));
	ensures eq(x, F(0,0)) ==> eq(negFixed(x), F(0,0));
	ensures lt(x, F(0,0)) ==> gt(negFixed(x), F(0,0));
	ensures liftFixed(x) == liftFixed(negFixed(x)) * -1;
{
	if(x.j == 0) then
		var iprime :oint := negate(x.i);
		Fixed(iprime.i, 0, false)
	else
		var j' :nat := (Power2(32) - x.j);
		assert(nat32(j'));
		// Easier to deal with the two sides separately, as overflow
		// conditions dictate that (-i-1) versus -(i+1) will have
		// intermediate overflows based on the sign of i.
		if(x.i >= 0) then
			// i>=0 means -i wont overflow, so we do -i-1.
			var t :oint := negate(x.i);
			var u := add32(t.i, -1);
			F(u.i,j')
		else // x.i < 0
			// i<0 means -(i+1) won't overflow. (notice -i could 
			// be -2147483648 so we cant negate first)
			assert(int32(x.i));
			assert Lemma_TwoToTheThirtyTwoIs();
			assert Power2(31) == 2147483648;
			assert -2147483648 <= x.i < 0;
			var t :oint := add32(x.i,1);
			assert -2147483648 < t.i <= 0;
			assert !t.o;
			var i :oint := negate(t.i);
			assert !i.o;
			assert i.i >= 0;
			assert i.i + x.i == -1;
			F(i.i, j')
}

// A positive only version of multiplication
function method umulFixedRoundDown(x: fixedpoint, y: fixedpoint) : fixedpoint
	requires isFixed64(x);
	requires isFixed64(y);
	requires gte(x, F(0,0));
	requires gte(y, F(0,0));

	ensures umulFixedRoundDown(x,y).o || gte(umulFixedRoundDown(x,y), F(0,0));
	ensures (lte(x, F(1,0)) && lte(y, F(1,0))) ==> isFixed64(umulFixedRoundDown(x,y));
	ensures (lte(x, F(1,0)) && lte(y, F(1,0))) ==> lte(umulFixedRoundDown(x,y), F(1,0));
	// Note we do not notify on underflow. You will lose some low bits
{

	var jjl :nat := umull32(x.j, y.j);
	var ijr :nat := umulr32(intToNat32(x.i), y.j);
	var jir :nat := umulr32(x.j, intToNat32(y.i));
	
	var fracoverflow :nat := 0; // max overflow is 2
	var frac1 :cnat := uadd32(ijr, jir);
	var frac1ov :nat := if frac1.c then 1 else 0;
	var frac2 :cnat := uadd32(frac1.n, jjl);
	var frac2ov :nat := if frac2.c then (frac1ov + 1) else frac1ov;
	var j := frac2.n;
	assert(frac2ov <= 2);

	var iil :nat := umull32(x.i, y.i); // This is to test for overflow
	var iir :nat := umulr32(x.i, y.i);
	var ijl :nat := umull32(x.i, y.j);
	var jil :nat := umull32(x.j, y.i);

	var int1 :cnat := uadd32(jil, ijl);
	var ov :bool := if int1.c then true else false;
	var int2 :cnat := uadd32(int1.n, iir);
	var int3 :cnat := uadd32(int2.n, frac2ov);
	var i := int3.n;
	var ov2 :bool :=if (int2.c || int3.c) then true else ov;
	var ov3 :bool :=if iil > 0 then true else ov2;

	//assert(AllAreNat32());
	if ov3 then
		Fixed(i,j,true)
	else
		Fixed(i,j,false)
}

// A positive only version of multiplication
function method umulFixedRoundUp(x: fixedpoint, y: fixedpoint) : fixedpoint
	requires isFixed64(x);
	requires isFixed64(y);
	requires gte(x, F(0,0));
	requires gte(y, F(0,0));

	ensures umulFixedRoundUp(x,y).o || gte(umulFixedRoundUp(x,y), F(0,0));
	ensures (lte(x, F(1,0)) && lte(y, F(1,0))) ==> isFixed64(umulFixedRoundUp(x,y));
	ensures (lte(x, F(1,0)) && lte(y, F(1,0))) ==> lte(umulFixedRoundUp(x,y), F(1,0));
	// Note we do not notify on underflow. You will lose some low bits
{
	
	var jjl :nat := umull32(x.j, y.j);
	var jjr :nat := umulr32(x.j, y.j);
	var ijr :nat := umulr32(intToNat32(x.i), y.j);
	var jir :nat := umulr32(x.j, intToNat32(y.i));
	
	var fracoverflow :nat := 0; // max overflow is 2
	var frac1 :cnat := uadd32(ijr, jir);
	var frac1ov :nat := if frac1.c then 1 else 0;
	var frac2 :cnat := uadd32(frac1.n, jjl);
	var frac2ov :nat := if frac2.c then (frac1ov + 1) else frac1ov;
	var frac3 :cnat := if jjr > 0 then uadd32(frac2.n, 1) else frac2; // Rounding up if there is underflow
	var frac3ov :nat := if frac3.c then (frac2ov + 1) else frac2ov;
	var j := frac3.n;
	assert(frac3ov <= 2);
	
	var iil :nat := umull32(x.i, y.i); // This is to test for overflow
	var iir :nat := umulr32(x.i, y.i);
	var ijl :nat := umull32(x.i, y.j);
	var jil :nat := umull32(x.j, y.i);

	var int1 :cnat := uadd32(jil, ijl);
	var ov :bool := if int1.c then true else false;
	var int2 :cnat := uadd32(int1.n, iir);
	var int3 :cnat := uadd32(int2.n, frac3ov);
	var i := int3.n;
	var ov2 :bool :=if (int2.c || int3.c) then true else ov;
	var ov3 :bool :=if iil > 0 then true else ov2;

	//assert(AllAreNat32());
	if ov3 then
		Fixed(i,j,true)
	else
		Fixed(i,j,false)
}



function method umulFixedNat (x :fixedpoint, y :nat) : fixedpoint
	requires isFixed64(x);
	requires nat32(y);
	requires gte(x, F(0,0));

	ensures umulFixedNat(x,y).o || gte(umulFixedNat(x,y), F(0,0));
	ensures (lt(x, F(1,0)) && y==1) ==> isFixed64(umulFixedNat(x,y));
	ensures (lt(x, F(1,0)) && y==1) ==> lt(umulFixedNat(x,y), F(1,0));
	ensures (!umulFixedNat(x,y).o) ==> ((umulFixedNat(x,y).i * Power2(32) + umulFixedNat(x,y).j) == ((x.i * Power2(32)) + x.j) * y);
{
	var x_nat := (Power2(32) * x.i) + x.j;

	var jr := umulr32(x.j, y);
	var jl := umull32(x.j, y);
	var xyj_nat := x.j * y;
	var xyi_nat := x.i * y;
	
	var xy_nat := (xyi_nat * Power2(32)) + xyj_nat;
	assert xy_nat == (x.i * y * Power2(32)) + (x.j * y);
	assert xy_nat == ((x.i * Power2(32)) + x.j) * y;

	var ir := umulr32(x.i, y);
	var il := umull32(x.i, y);

	//assert umulr32(x.i,y) == (x.i * y % Power2(32));
	//assert umull32(x.i,y) == (x.i * y) / Power2(32);
	assert umulr32(x.i,y) + (Power2(32) * umull32(x.i,y)) == (x.i * y);
	assert (il * Power2(32) + ir) == xyi_nat;

	assert umulr32(x.j,y) == (x.j * y % Power2(32));
	assert umull32(x.j,y) == (x.j * y) / Power2(32);
	assert umulr32(x.j,y) + (Power2(32) * umull32(x.j,y)) == (x.j * y);
	assert (jl * Power2(32) + jr) == xyj_nat;

	var inte :cnat := uadd32(jl, ir);

	if (inte.c || (il > 0)) then
		Fixed(inte.n, jr, true)
	else
		assert il == 0;
		assert xyi_nat == ir;
		var z_nat := (inte.n * Power2(32)) + jr;
		assert z_nat == (ir + jl) * Power2(32) + jr;
		assert z_nat == xy_nat;
		//assert xy_nat == z_nat;
		Fixed(inte.n, jr, false)

}

function method OneOverRoundDown (y :nat) : fixedpoint
	requires 2 <= y <= 100;
	ensures isFixed64(OneOverRoundDown(y));
	ensures lt(OneOverRoundDown(y), F(1,0));
	ensures gt(OneOverRoundDown(y), F(0,0));
{
	assert(AllAreNat32());
	F(0,[2147483648 , 1431655765 , 1073741824 , 858993459 , 715827882 , 613566756 , 536870912 , 
	477218588 , 429496729 , 390451572 , 357913941 , 330382099 , 306783378 , 286331153 , 268435456 , 252645135 , 
	238609294 , 226050910 , 214748364 , 204522252 , 195225786 , 186737708 , 178956970 , 171798691 , 165191049 , 
	159072862 , 153391689 , 148102320 , 143165576 , 138547332 , 134217728 , 130150524 , 126322567 , 122713351 , 
	119304647 , 116080197 , 113025455 , 110127366 , 107374182 , 104755299 , 102261126 , 99882960 , 97612893 , 
	95443717 , 93368854 , 91382282 , 89478485 , 87652393 , 85899345 , 84215045 , 82595524 , 81037118 , 79536431 , 
	78090314 , 76695844 , 75350303 , 74051160 , 72796055 , 71582788 , 70409299 , 69273666 , 68174084 , 67108864 , 
	66076419 , 65075262 , 64103989 , 63161283 , 62245902 , 61356675 , 60492497 , 59652323 , 58835168 , 58040098 , 
	57266230 , 56512727 , 55778796 , 55063683 , 54366674 , 53687091 , 53024287 , 52377649 , 51746593 , 51130563 , 
	50529027 , 49941480 , 49367440 , 48806446 , 48258059 , 47721858 , 47197442 , 46684427 , 46182444 , 45691141 , 
	45210182 , 44739242 , 44278013 , 43826196 , 43383508, 42949672][y-2])
}

function method OneOverRoundUp (y :nat) : fixedpoint
	requires 2 <= y <= 100;
	ensures isFixed64(OneOverRoundUp(y));
	ensures lt(OneOverRoundUp(y), F(1,0));
	ensures gt(OneOverRoundUp(y), F(0,0));
{
	assert(AllAreNat32());
	F(0,[2147483648 , 1431655765 , 1073741824 , 858993459 , 715827882 , 613566756 , 536870912 , 
	477218588 , 429496729 , 390451572 , 357913941 , 330382099 , 306783378 , 286331153 , 268435456 , 252645135 , 
	238609294 , 226050910 , 214748364 , 204522252 , 195225786 , 186737708 , 178956970 , 171798691 , 165191049 , 
	159072862 , 153391689 , 148102320 , 143165576 , 138547332 , 134217728 , 130150524 , 126322567 , 122713351 , 
	119304647 , 116080197 , 113025455 , 110127366 , 107374182 , 104755299 , 102261126 , 99882960 , 97612893 , 
	95443717 , 93368854 , 91382282 , 89478485 , 87652393 , 85899345 , 84215045 , 82595524 , 81037118 , 79536431 , 
	78090314 , 76695844 , 75350303 , 74051160 , 72796055 , 71582788 , 70409299 , 69273666 , 68174084 , 67108864 , 
	66076419 , 65075262 , 64103989 , 63161283 , 62245902 , 61356675 , 60492497 , 59652323 , 58835168 , 58040098 , 
	57266230 , 56512727 , 55778796 , 55063683 , 54366674 , 53687091 , 53024287 , 52377649 , 51746593 , 51130563 , 
	50529027 , 49941480 , 49367440 , 48806446 , 48258059 , 47721858 , 47197442 , 46684427 , 46182444 , 45691141 , 
	45210182 , 44739242 , 44278013 , 43826196 , 43383508, 42949672][y-2])
}

function method remainders (y :nat) : nat
	requires 2 <= y <= 100;
	ensures 0 <= remainders(y) <= 100;
{
	assert(AllAreNat32());
	[0 , 1 , 0 , 1 , 4 , 4 , 0 , 4 , 6 , 4 , 4 , 9 , 4 , 1 , 0 ,
	 1 , 4 , 6 , 16 , 4 , 4 , 12 , 16 , 21 , 22 , 22 , 4 , 16 , 16 ,
	  4 , 0 , 4 , 18 , 11 , 4 , 7 , 6 , 22 , 16 , 37 , 4 , 16 , 4 , 
	  31 , 12 , 42 , 16 , 39 , 46 , 1 , 48 , 42 , 22 , 26 , 32 , 25 ,
	   16 , 51 , 16 , 57 , 4 , 4 , 0 , 61 , 4 , 33 , 52 , 58 , 46 ,
	    9 , 40 , 32 , 44 , 46 , 44 , 4 , 22 , 50 , 16 , 49 , 78 ,
		 77 , 4 , 1 , 16 , 16 , 48 , 45 , 76 , 74 , 12 , 4 , 42 ,
		  6 , 64 , 35 , 88 , 4 , 96][y-2]
}


/***************************************************************************
 Proof of correctness of fixedpoint point operations
****************************************************************************/


ghost method umull32Andumulr32AreLegit(x :nat, y: nat, z: nat)
	requires nat32(x);
	requires nat32(y);
	requires z == (Power2(32) * umull32(x,y)) + umulr32(x,y);
	ensures z == x * y;
{
}

ghost method addFixedZeroIsIdentity(x: fixedpoint)
	requires isFixed64(x);
	ensures eq(addFixed(x, F(0,0)), x);
{}

ghost method addFixedAdheresToSpec(x :fixedpoint, y :fixedpoint, z :fixedpoint)
	requires isFixed64(x);
	requires isFixed64(y);
	requires isFixed64(z);
	requires z == addFixed(x,y);

	ensures liftFixed(x) + liftFixed(y) == liftFixed(z);
	ensures addFixedSpec(x,y,z);
{
	assert(AllAreNat64());
	assert(x.i < Power2(32));
	Power2IsDistributive(32,32,64);
	assert(Power2(32) * Power2(32) == Power2(64));
	assert(x.i < Power2(64));
	assert(y.i < Power2(32));
	Power2IsDistributive(32,32,64);
	assert(y.i < Power2(64));
	var z := addFixed(x,y);
	assert(z.i < Power2(32));
	Power2IsDistributive(32,32,64);
	assert(z.i < Power2(64));
	assert liftFixed(x) + liftFixed(y) == liftFixed(z);
}


ghost method negFixedAdheresToSpec(x: fixedpoint, y :fixedpoint)
	requires isFixed64(x);

	requires y == negFixed(x);					
	ensures  isFixed64(y);
	
	ensures (liftFixed(y) == (-1) * liftFixed(x));
{}


ghost method negFixedAddsToZero(x :fixedpoint)
	requires isFixed64(x);
	ensures isFixed64(negFixed(x));
	ensures eq(addFixed(x, negFixed(x)), F(0,0));
{}


ghost method umulFixedRoundDownLessThanOneIsLegit(x :fixedpoint, y :fixedpoint, z :fixedpoint, x_int :int, y_int :int, z_int :int)
	requires isFixed64(x);
	requires isFixed64(y);
	requires !z.o;

	requires gte(x, F(0,0));
	requires lt(x, F(1,0));
	requires gte(y, F(0,0));
	requires lt(y, F(1,0));

	requires eq(z, umulFixedRoundDown(x,y));
	ensures isFixed64(z);

	ensures  gte(z, F(0,0)) && lt(z, F(1,0));

	requires x_int == (Power2(32) * x.i) + x.j;
	requires y_int == (Power2(32) * y.i) + y.j;
	requires z_int == (Power2(32) * z.i) + z.j;

	ensures z_int == (x_int * y_int) / Power2(32); // Rounding down implied here	
{
	assert AllAreNat64();
	var xy_int :int := x_int * y_int;
	assert(0 <= x_int < Power2(32));
	assert(0 <= y_int < Power2(32));
	ThirtyTwoBitMultIs64Bit(x_int, y_int, xy_int);
	assert(0 <= xy_int < Power2(64));
	var xy_intR :int := xy_int / Power2(32);
	DivideBy2ToThe32(xy_int, xy_intR);
	assert(0 <= xy_intR < Power2(32));

	assert(0 <= z_int < Power2(32));

	assert xy_int == x.j * y.j;
	assert z_int == xy_intR;
}

ghost method umulFixedRoundUpLessThanOneIsLegit(x :fixedpoint, y :fixedpoint, z :fixedpoint, x_int :nat, y_int :nat, z_int :nat)
	requires isFixed64(x);
	requires isFixed64(y);
	requires !z.o;

	requires gte(x, F(0,0));
	requires lt(x, F(1,0));
	requires gte(y, F(0,0));
	requires lt(y, F(1,0));

	requires eq(z, umulFixedRoundUp(x,y));
	ensures isFixed64(z);

	ensures  gte(z, F(0,0)) && lt(z, F(1,0));

	requires x_int == (Power2(32) * x.i) + x.j;
	requires y_int == (Power2(32) * y.i) + y.j;
	requires z_int == (Power2(32) * z.i) + z.j;

	ensures z_int >= (x_int * y_int) / Power2(32); // Could be rounded up so greater than or equal to
	ensures z_int <= (x_int * y_int) + 1 / Power2(32); // But not rounded up by more than one ulp
/*{
	assert CanWePleaseTalkAboutNumbers();
	var xy_int :nat := x_int * y_int;
	assert(x_int < Power2(32));
	assert(y_int < Power2(32));
	ThirtyTwoBitMultIs64Bit(x_int, y_int, xy_int);
	assert(xy_int < Power2(64));
	
	var xy_intR :nat := xy_int / Power2(32);
	DivideBy2ToThe32(xy_int, xy_intR);
	assert(xy_intR < Power2(32));
	
	assert(z_int <= Power2(32));

	assert xy_int == x.j * y.j;

	var xy_intUp :nat := (x_int * y_int) + 1;
	assert x_int < Power2(32);
	assert x_int <= Power2(32) - 1;
	assert Lemma_TwoToTheThirtyTwoIs();
	assert Power2(32) == 4294967296;
	assert Power2(32) - 1 == 4294967295;
	assert x_int <= 4294967295;
	assert y_int <= 4294967295;
	assert (x_int * y_int) <= 18446744065119617025;
	assert (x_int * y_int) + 1 <= 18446744065119617026;
	assert Lemma_TwoToTheSixtyFourIs();
	assert(xy_intUp < Power2(64));
	var xy_intUpR :nat := (xy_intUp / Power2(32));
	DivideBy2ToThe32(xy_intUp, xy_intUpR);
	assert(xy_intUpR < Power2(32));

	assert z_int <= xy_intUpR;
}*/


/*
	We don't guarantee that you won't overflow (!isFixed64(z)). We only 
	guarantee that if you don't overflow, you will have the correct value.

	This one is exact, as there is no underflow.
*/
ghost method umulFixedLessThanOneNatIsLegit(x :fixedpoint, y :nat, z :fixedpoint, x_int :int, z_int :int)
	requires isFixed64(x);
	requires nat32(y);
	requires isFixed64(z);
	
	requires gte(x, F(0,0));
	requires lt(x, F(1,0));
	// 0 <= x < 1, and y is a nat.
	requires y >= 0;
	
	requires !z.o;
	requires !umulFixedNat(x,y).o;
	requires z.i == umulFixedNat(x,y).i;
	requires z.j == umulFixedNat(x,y).j;

	requires x_int == (Power2(32) * x.i) + x.j;
	requires z_int == (Power2(32) * z.i) + z.j;

	//ensures z_int == (x_int * y_int) / Power2(32);	
{
	assert AllAreNat64();
	var xy_int :nat := x_int * y;
	assert(0 <= x_int < Power2(32));
	ThirtyTwoBitMultIs64Bit(x_int, y, xy_int);

	var xj_y :nat := x.j * y;
	var xi_y :nat := (Power2(32) * x.i) * y;
	
	//assert xj_y + xi_y == xy_int;
	
	assert xy_int == z_int;
	assert x_int * y == z_int;

	//assert z_int == (x_int * y_int) / Power2(32);

}

ghost method addFixedIsCommutative(a :fixedpoint, b :fixedpoint)
	requires isFixed64(a);
	requires isFixed64(b);
	requires isFixed64(addFixed(a,b));
	requires isFixed64(addFixed(b,a));

	ensures eq(addFixed(a,b), addFixed(b,a));
{}

ghost method umulFixedRoundDownIsCommutative(a :fixedpoint, b :fixedpoint)
	requires isFixed64(a);
	requires isFixed64(b);
	requires gte(a, F(0,0));
	requires gte(b, F(0,0));
	requires isFixed64(umulFixedRoundDown(a,b));
	requires isFixed64(umulFixedRoundDown(b,a));

	ensures eq(umulFixedRoundDown(a,b), umulFixedRoundDown(b,a));
{} // How does Dafny know this. Seriously. I came here with no proof strategy at all.

ghost method umulFixedRoundUpIsCommutative(a :fixedpoint, b :fixedpoint)
	requires isFixed64(a);
	requires isFixed64(b);
	requires gte(a, F(0,0));
	requires gte(b, F(0,0));
	requires isFixed64(umulFixedRoundUp(a,b));
	requires isFixed64(umulFixedRoundUp(b,a));

	ensures eq(umulFixedRoundUp(a,b), umulFixedRoundUp(b,a));
{} // Or this one...

/*
This proof doesn't work, and we do not actually need it right now: we can work with just umulFixedLessThanOneNat and umulFixedLessThanOne


ghost method umulFixedIsLegit(x :fixedpoint, y :fixedpoint) 
	requires isFixed64(x);
	requires isFixed64(y);

	requires gte(x, F(0,0));
	requires gte(y, F(0,0));

	requires isFixed64(umulFixed(x,y));
{
	
	var z :fixedpoint := umulFixed(x,y);
	assert(AllAreNat64());
	assert(eq(z, umulFixed(x,y)));
	assert(isFixed64(z));
	
	//assert(isFixed64(z));
	assert(gte(z, F(0,0)));

	var x_nat :nat := (Power2(32) * x.i) + x.j;
	var y_nat :nat := (Power2(32) * y.i) + y.j;
	var z_nat :nat := (Power2(32) * z.i) + z.j;

	var xjyj :nat := x.j * y.j;
	
	
}
*/

/*
Don't need signed multiplication for now either...

function method mulFixed(x :fixedpoint, y: fixedpoint) : fixedpoint
	requires(isFixed64(x));
	requires(isFixed64(y));
	// Note we do not notify on underflow
{
	var sign := (lt(x, F(0,0)) && lt(y, F(0,0))) ||
				(gt(x, F(0,0)) && gt(y, F(0,0))) ||
				(eq(x, F(0,0)) || eq(y, F(0,0)));
	var xprime := if(lt(x, F(0,0))) then
		negFixed(x)
	else
		x;
	var yprime := if(lt(y, F(0,0))) then
		negFixed(y)
	else
		y;
	if(!isFixed64(xprime) || (!isFixed64(yprime))) then
		Fixed(0,0,true)
	else
		assert(isFixed64(xprime));
		assert(isFixed64(yprime));
		assert(gte(xprime, F(0,0)));
		assert(gte(yprime, F(0,0)));
		var unsigned := umulFixed(xprime, yprime);
		if(!sign) then
			negFixed(unsigned)
		else
			unsigned
}
*/

// Verifies but extremely slowly as it basically checks 100 code paths.
/*ghost method divisionIsSane()
{
	assert(CanWePleaseTalkAboutNumbers());

	var i :nat := 2;
	
	var x :fixedpoint := OneOverRoundDown(i);
	assert x.i == 0;
	assert x.j == 2147483648;
	assert 2147483648 * 2 + 0 == 4294967296;

	var x_nat :nat := (Power2(32) * x.i) + x.j;
	assert x_nat == 2147483648;
	var x_nat_plus_r :nat := (i * x_nat) + remainders(i);
	assert x_nat_plus_r == 4294967296;

	while (i <= 100) {
		var x :fixedpoint := OneOverRoundDown(i);
		var x_nat :nat := (Power2(32) * x.i) + x.j;
		var x_nat_plus_r :nat := (i * x_nat) + remainders(i);
		assert(x_nat_plus_r == 4294967296);

		i := i + 1;
	}

}*/

/*****************************************************************************
Real definition
******************************************************************************/

datatype R = rAbs() | rOfInt(i :int) | rOfFixed(f :fixedpoint);

function eqR (r1 :R, r2 :R) : bool

ghost method reflexiveEq(r :R)
	ensures eqR(r, r);

ghost method symmetricEq(r1 :R, r2 :R)
	requires eqR(r1, r2);
	ensures eqR(r2, r1);

ghost method transitiveEq(r1 :R, r2 :R, r3 :R)
	requires eqR(r1, r2);
	requires eqR(r2, r3);
	ensures eqR(r1, r3);

function ltR (r1 :R, r2 :R) : bool

function lteR (r1 :R, r2 :R) : bool

function gtR (r1 :R, r2 :R) : bool

function gteR (r1 :R, r2 :R) : bool

function addR (r1 : R, r2 :R) : R

function subtractR (r1 :R, r2 :R) : R

function multR (r1 :R, r2 :R) : R

function divR (r1 :R, r2 :R) : R

function lnR (r :R) : R
	requires gtR(r, rOfInt(0));
	ensures ltR(r, rOfInt(1)) ==> ltR(lnR(r), rOfInt(0));
	ensures eqR(r, rOfInt(1)) ==> eqR(lnR(r), rOfInt(0));
	ensures gtR(r, rOfInt(1)) ==> gtR(lnR(r), rOfInt(0));

function eToTheR (r :R) : R
	ensures gtR(eToTheR(r), rOfInt(0));
	ensures eqR(r, rOfInt(0)) ==> eqR(eToTheR(r), rOfInt(1));
	ensures ltR(r, rOfInt(0)) ==> ltR(eToTheR(r), rOfInt(1));
	ensures gtR(r, rOfInt(0)) ==> gtR(eToTheR(r), rOfInt(1));


ghost method eToTheLnR (r :R)
	requires gtR(r, rOfInt(0));
	ensures eqR(eToTheR(lnR(r)), r);

ghost method lnEToTheR (r :R)
	ensures eqR(lnR(eToTheR(r)), r);

ghost method lnIsMonotoniclyIncreasing(r1 :R, r2 :R)
	requires gtR(r1, rOfInt(0));
	requires gtR(r2, rOfInt(0));
	requires ltR(r1, r2);
	ensures ltR(lnR(r1), lnR(r2));

/*****************************************************************************
Noise generation definition
******************************************************************************/

/*//extern function that computes ln (j / 2^32), and returns the result as a fixedpoint point number
function method ext_ln (j :nat) : fixedpoint
	requires nat32(j);
	ensures isFixed64(ext_ln(j));
	ensures lte(ext_ln(j), F(0,0)); // x < 1 ==> ln(x) < 0
	ensures forall j1 :nat :: j1 < j ==> (lt(ext_ln(j1), ext_ln(j))); // monotonic
*/

// extern function that calculates 2 alpha / (1 + alpha)
function method ext_coeff(alpha :fixedpoint) : fixedpoint
	requires isFixed64(alpha);
	requires lte(alpha, F(1,0));
	ensures isFixed64(ext_coeff(alpha));
	
	ensures gte(ext_coeff(alpha), F(0,0));
	ensures lte(ext_coeff(alpha), F(1,0));
{
	assert AllAreNat32();
	F(0,4273492638) // alpha for epsilon = 0.01, sens = 1, g = 1.
}

function method seqSum (s :seq<int>) : int
	requires |s| >= 0;
{
	if |s| == 0 then
		0
	else if |s| == 1 then
		s[0]
	else
		s[0] + seqSum(s[1..])
}

datatype int_or_exception = IntegerWrapper(i :int) | DeltaException | AnalysisFailure(code :int);

// real delta = delta:nat / 2^32, strictly speaking.
method sampleNoise (bands :seq<int>, delta : nat, d :nat, alpha_max : fixedpoint) returns (noise :int_or_exception)
	requires |bands| > 1;
	requires nat32(delta);
	requires d < |bands| - 2;
	requires forall i :nat :: 0 <= i < |bands| ==> bands[i] > 0;
	requires forall i :nat :: 0 <= i < |bands| ==> bands[i] < Power2(32); // 
	requires forall i :nat :: 0 <= i < |bands| - 1 ==> bands[i] > bands[i+1]; // We are only going to check one side
	requires isFixed64(alpha_max);
	requires lte(alpha_max, F(1,0));
	requires gt(alpha_max, F(0,0));

{
	var cdrbands := bands[1..];
	var validbands := cdrbands[..|cdrbands|-d];
	assert |validbands| > 0;
	
	// Sum of bands is within 2^32
	var sumbands :=  bands[0] + (2 * seqSum(validbands));
	if (sumbands + delta < Power2(32)) {
		return AnalysisFailure(-1);
	}
	else {
		
		// Each band is multiplicatively alpha away
		var i :nat := 1;
		while(i < |bands|)
			decreases |bands| - i;
		{
			var b_old :fixedpoint := F(0, bands[i-1]);
			var b_new :fixedpoint := F(0, bands[ i ]);
			var b_old_alpha := umulFixedRoundDown(b_old, alpha_max);
			if lt(b_old_alpha, b_new) {
				return AnalysisFailure(i);
			}
			i := i + 1;
		}

		// Now we can choose a random number U < 2^32
		var U :nat := getRandom32();
		if(bands[0] >= U)
		{
			return IntegerWrapper(0);
		} else if (sumbands <= U) {
			return IntegerWrapper(|bands|);
		}

		assert U < sumbands;
		i := 1;
		var accum :nat := bands[0];
		assert accum <= bands[0];
		assert accum <= bands[0] + seqSum(bands[0..0]);
		while(accum < U)
			decreases U - accum;
			invariant U < sumbands;
			invariant 1 <= i < |bands|;
			//invariant accum <= bands[0] + 2 * seqSum(bands[0..(i-1)]);
		{

			if (accum + bands[i] >= U)
			{
				return IntegerWrapper(i);
			}
			else if (accum + (2 * bands[i]) >= U)
			{
				return IntegerWrapper(-1*i);
			}
			else
			{
				accum := accum + (2 * bands[i]);
				
				i := i + 1;	
				if(i >= |bands|) {
					return AnalysisFailure(-3); // debug only
				}	
			}
		}
				
	}
}


/*****************************************************************************
Budget management 
******************************************************************************/

method budgetCharge ( epsilonTotal :fixedpoint, epsilonQuery :fixedpoint) returns (epsilonRemaining :fixedpoint)

/*****************************************************************************
Logarithm definition
******************************************************************************/
/*
function method lnFixed(x :fixedpoint, terms :nat) :fixedpoint
	requires isFixed64(x);
	requires 0 < terms < 100;
	requires gt(x, F(0,0));
	requires lte(x, F(1,0));
{
	lnFixedTaylor(x, F(1,0), 1, terms)
}

function method lnFixedTaylor (x :fixedpoint, xToTermMinusOne :fixedpoint, term :nat, maxTerms :nat) : fixedpoint
	decreases (maxTerms - term);
	
	requires isFixed64(x);
	requires isFixed64(xToTermMinusOne);
	requires 0 < maxTerms < 100;
	requires 0 < term <= maxTerms;
	requires gt(x, F(0,0));
	requires lte(x, F(1,0));
	requires gt(xToTermMinusOne, F(0,0));
	requires lte(xToTermMinusOne, F(1,0));

	ensures isFixed64(lnFixedTaylor(x, xToTermMinusOne, term, maxTerms));
	ensures lte(lnFixedTaylor(x, xToTermMinusOne, term, maxTerms), F(0,0));
{
	if(eq(x, F(1,0))) then
		F(0,0)
	else
		var denom := if (term == 1) then F(1,0) else OneOverRoundDown(term);
		var xToTerm := umulFixedRoundDown(x, xToTermMinusOne);
		assert lte(xToTerm, F(1,0));
		assert gte(xToTerm, F(0,0));
		assert lte(denom, F(1,0));
		assert gte(denom, F(0,0));
		var nthTerm := umulFixedRoundDown(xToTerm, denom);
		assert isFixed64(nthTerm);

		if(term == maxTerms) then
			nthTerm
		else
			addFixed(nthTerm, lnFixedTaylor(x, xToTermMinusOne, term+1, maxTerms))
}
*/


/*
method ln (x :fixedpoint) returns (sum :fixedpoint)
	requires isFixed64(x);
	requires gt(x, F(0,0));
	requires lte(x, F(1,0));

	ensures isFixed64(sum);
{
	if(eq(x, F(1,0)))
	{
		sum := F(0,0);
	}
	else {
		assert(Lemma_TwoToTheThirtyTwoIs());
		assert(Power2(32) == 4294967296);
		sum := lnOneMinus(F(0, 4294967296 - x.j));
	}
}
*/
/*
method lnOneMinus (x :fixedpoint) returns (sum :fixedpoint)
	requires isFixed64(x);
	requires gte(x, F(0,0)) && lt(x, F(1,0)); // x = 1-U \in [0,1)
	requires x.i == 0 && nat32(x.j); // otherwise can be stated as this

	ensures isFixed64(sum);
	ensures lte(sum, F(0,0));
	ensures sum.i != -2147483648;
{
	
	var xToThe := x;
	sum := xToThe;
	assert isFixed64(sum);

	var i :nat := 2;
	assert isFixed64(xToThe);
	
	while(i <= 100) 
	invariant isFixed64(xToThe);
	invariant gte(xToThe, F(0,0));
	invariant lt(xToThe, F(1,0));
	invariant isFixed64(sum);
	invariant gte(sum, F(0,0));
	{
		xToThe := umulFixedRoundDown(xToThe, x);
		var term :fixedpoint := umulFixedRoundDown(xToThe, OneOverRoundDown(i));
		assert(lt(term, F(1,0)));
		assert(gte(term, F(0,0)));
		assert(isFixed64(term));

		sum := addFixed(sum, term);
		i := i + 1;
	}
	assert(gte(sum, F(0,0)));
	assert(isFixed64(sum));
	sum := negFixed(sum);
}
*/

/**********************************************************************
The Laplace Noise function implemented using fixedpoint point integers.
***********************************************************************/
/*
// lamba = sensitivity / epsilon
method geometricRandomNoise(lambda :nat) returns (noise :fixedpoint)
	requires nat32(lambda);
{
	var U := F(0,getRandom32()); // U := [0,1)
	var lnU :fixedpoint := lnOneMinus(U);
	var neglnU :fixedpoint := negFixed(lnU);
	assert gte(neglnU, F(0,0));
	assert isFixed64(neglnU);
	var lambdaTimeslnU :fixedpoint := umulFixedNat(neglnU, lambda);
	
	var cointoss := getRandom32();
	if (cointoss < 2147483648) // probability one half
	{
		noise := lambdaTimeslnU;
	}
	else
	{
		noise := negFixed(lambdaTimeslnU);
	}

}*/

/***********************************************************************
Error bar fixedpoint points
************************************************************************/

datatype frange = FRange(lower :fixedpoint, upper :fixedpoint);
/*
	lower bound and upper bound. Inclusive of both sides.
*/

function method isFRange64(f :frange) : bool
{
	isFixed64(f.lower) && isFixed64(f.upper) &&
		lte(f.lower, f.upper) // convenient to have only one sided franges
}

function method exactFRange(f :fixedpoint) : frange
{
	FRange(f, f)
}

function method isExact(f :frange) : bool
	requires isFRange64(f);
{
	eq(f.lower, f.upper)
}

function method lt_frange(x :frange, y :frange) : bool
	requires isFRange64(x);
	requires isFRange64(y);
{
	lt(x.upper, y.lower)
}

function method lte_frange(x :frange, y :frange) : bool
	requires isFRange64(x);
	requires isFRange64(y);
{
	lte(x.upper, y.lower)
}


function method eq_frange(x :frange, y :frange) : bool
	requires isFRange64(x);
	requires isFRange64(y);
{
	eq(x.lower, y.lower) && eq(x.upper, y.upper)
}

function method gt_frange(x :frange, y :frange) : bool
	requires isFRange64(x);
	requires isFRange64(y);
{
	gt(x.lower, y.upper)
}

function method gte_frange(x :frange, y :frange) : bool
	requires isFRange64(x);
	requires isFRange64(y);
{
	gte(x.lower, y.upper)
}

function method zero_frange() : frange
{
	FRange(F(0,0), F(0,0))
}

function method gte0_frange(x :frange) : bool
	requires isFRange64(x);
// This is such a common mnemonic that I write a shortcut here
{
	gte_frange(x, zero_frange())
}
/*
function method width(f :frange) : fixedpoint
	requires isFRange64(f);

	ensures isFixed64(width(f));
	ensures gte(width(f), F(0,0));
	ensures gte0_frange(f) ==> gte(width(f), F(0,0));
{
	var nl := negFixed(f.lower);
	assert(isFixed64(nl));
	
	var sum := addFixed(f.upper, nl);

	abs(addFixed(f.upper, negFixed(f.lower)))
}


/***********************************************************************
Error bar fixedpoint points operators
************************************************************************/

function method addFRange(x :frange, y :frange) : frange
	requires isFRange64(x);
	requires isFRange64(y);
{
	var left :fixedpoint := addFixed(x.lower, y.lower);
	var right:fixedpoint := addFixed(x.upper, y.upper);

	FRange(left, right)
}

function method negFRange(f :frange) : frange
	requires isFRange64(f);
	ensures isFRange64(negFRange(f));
{
	var left :fixedpoint := negFixed(f.upper);
	var right:fixedpoint := negFixed(f.lower);
	
	FRange(left, right)
}

function method umulFRange(x :frange, y :frange) : frange
	requires isFRange64(x);
	requires isFRange64(y);
	
	requires gte0_frange(x);
	requires gte0_frange(y);

{
	var lower :fixedpoint := umulFixedRoundDown(x.lower, y.lower);
	var upper :fixedpoint := umulFixedRoundUp  (x.upper, y.upper);

	FRange(lower, upper)
}


/***********************************************************************
Error bar fixedpoint points operators proofs of correctness
************************************************************************/


ghost method widthZeroImpliesLowerEqualsUpper(f :frange)
	requires isFRange64(f);
	ensures (eq(width(f), F(0,0)) <==> isExact(f));
{}

ghost method addFRangePreservesExact(x :frange, y :frange, z :frange)
	requires isFRange64(x);
	requires isFRange64(y);
	requires isFRange64(z);

	requires isExact(x);
	requires isExact(y);
	requires z == addFRange(x,y);

	ensures isExact(z);

{}

ghost method negFRangePreservesExact(x :frange, y :frange)
	requires isFRange64(x);
	requires isFRange64(y);

	requires y == negFRange(x);

	requires isExact(x);
	ensures isExact(y);
{}

ghost method umulFRangeAddsWidthsPlusOne(x :frange, y :frange, z :frange, xwidth :nat, ywidth :nat, zwidth :nat)
	requires isFRange64(x);
	requires isFRange64(y);
	requires isFRange64(z);
	requires lte_frange(x, y); // WLOG
	
	requires gte0_frange(x);
	requires gte0_frange(x);

	requires z == umulFRange(x, y);

	requires xwidth == width(x).i * Power2(32) + width(x).j;
	requires ywidth == width(y).i * Power2(32) + width(y).j;
	requires zwidth == width(z).i * Power2(32) + width(z).j;
	
	ensures zwidth <= xwidth + ywidth + 1;


	
/***********************************************************************
FRange based logarithm specification
************************************************************************/

function method kthTaylorTerm(k : nat, u : fixedpoint) : frange
	requires isFixed64(u);
	requires k < 1000;

*/
	
// End of module
}
