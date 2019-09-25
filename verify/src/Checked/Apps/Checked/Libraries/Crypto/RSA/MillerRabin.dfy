include "../../BigNum/BigNatMod.dfy"
include "../../BigNum/BigNatRandom.dfy"
include "../../Math/evenodd.dfy"
include "../../Math/power.dfy"
include "MillerRabinSpec.dfy"
include "division.dfy"

function IsPrime(n:nat) : bool
{
	forall cf:nat :: 2 <= cf < n ==> !divides(cf, n)
}

lemma lemma_bignat_even(N:BigNat)
	requires WellformedBigNat(N);
	ensures IsEven(I(N)) == IsEven(lo(N));
{
	var w31 := power2(31);
	reveal_power2();
	assert w31*2 == Width();
	{ lemma_mul_is_mul_boogie(w31,2); }
	assert mul(w31,2) == Width();

	if (IsEven(lo(N)))
	{
		var y0:int :| y0*2 == lo(N);
		var y := w31 * I(hi(N)) + y0;

		calc {
			y * 2;
			(w31*I(hi(N)) + y0) * 2;
				{ lemma_mul_is_distributive_add_forall(); }
			(w31*I(hi(N)))*2 + y0*2;
				{ lemma_mul_is_mul_boogie((w31*I(hi(N))),2); }
			mul(w31*I(hi(N)),2) + y0*2;
				{ lemma_mul_is_commutative_forall(); }
			mul(2,w31*I(hi(N))) + y0*2;
				{ lemma_mul_is_associative_forall(); }
			mul(mul(2,w31),I(hi(N))) + y0*2;
				{ lemma_mul_is_commutative_forall(); }
			mul(mul(w31,2),I(hi(N))) + y0*2;
			mul(Width(),I(hi(N))) + y0*2;
			Width()*I(hi(N)) + y0*2;
			Width()*I(hi(N)) + lo(N);
				{
					lemma_hilo(N);
					lemma_mul_is_commutative_forall();
				}
			I(N);
		}
		assert IsEven(I(N));
	}
	if (IsEven(I(N)))
	{
		var y :| y*2 == I(N);
		calc ==> {
			true;
				{
					lemma_hilo(N);
					lemma_mul_is_commutative_forall();
				}
			y*2 == Width()*I(hi(N)) + lo(N);
			y*2 == mul(w31,2)*I(hi(N)) + lo(N);
			y*2 - mul(w31,2)*I(hi(N)) == lo(N);
				{
					lemma_mul_is_commutative_forall();
					lemma_mul_is_associative_forall();
				}
			y*2 - mul(mul(w31,I(hi(N))),2) == lo(N);
				{ lemma_mul_is_mul_boogie(y,2); }
			mul(y,2) - mul(mul(w31,I(hi(N))),2) == lo(N);
				{ lemma_mul_is_commutative_forall(); }
			mul(2,y) - mul(2,mul(w31,I(hi(N)))) == lo(N);
				{ lemma_mul_is_distributive_sub(2, y, mul(w31,I(hi(N)))); }
			mul(2, y - mul(w31,I(hi(N)))) == lo(N);
			mul(2, y - w31*I(hi(N))) == lo(N);
				{ lemma_mul_is_commutative_forall(); }
			mul(y - w31*I(hi(N)), 2) == lo(N);
				{ lemma_mul_is_mul_boogie(y - w31*I(hi(N)),2); }
			(y - w31*I(hi(N)))*2 == lo(N);
			IsEven(lo(N));
		}
	}
}

function method WordIsEven_def(x:nat) : bool
	requires Word32(x);
{
	// TODO mod? Really!? A better implementation would check the low bit
	x%2 == 0
}

lemma lemma_WordIsEven(x:nat)
	requires Word32(x);
	ensures WordIsEven_def(x) == IsEven(x);
{
	if (WordIsEven_def(x))
	{
		lemma_fundamental_div_mod(x,2);
		assert x == 2 * (x / 2) + x % 2;
		assert x == 2 * (x / 2);
		var y:=(x/2);
		assert y*2 == x;
		assert IsEven(x);
	}
	else
	{
		assert x%2 == 1;
		if (IsEven(x))
		{
			var y :| y*2 == x;
			calc {
				true;
					{ lemma_fundamental_div_mod(x,2); }
				x == 2 * (x / 2) + x % 2;
				y*2 == 2 * (x/2) + 1;
				y*2 -2*(x/2)== 1;
					{ lemma_mul_is_distributive_sub_forall(); }
				2*(y-(x/2))== 1;
					{ lemma_no_half(y-(x/2)); }
				false;
			}
		}
	}
}

function method WordIsEven(x:nat) : bool
	requires Word32(x);
	ensures IsEven(x) == WordIsEven(x);
{
	lemma_WordIsEven(x);
	WordIsEven_def(x)
	// TODO mod? Really!? A better implementation would check the low bit
}

//lemma lemma_bignum_even(N:BigNum)
//	requires WellformedBigNum(N);
//	ensures IsEven(BV(N)) == IsEven(lo(N.value));
//{
//	if (N.negate)
//	{
//		lemma_bignat_even(N.value);
//		assert IsEven(BV(N))==IsEven(-BV(N));
//	}
//}
//
//function method IsEvenBigNum(N:BigNum) : bool
//	requires WellformedBigNum(N);
//	ensures IsEvenBigNum(N) == IsEven(BV(N));
//{
//	lemma_bignum_even(N);
//	if (zero(N.value)) then
//		true
//	else
//		WordIsEven(lo(N.value))
//}

function method IsEvenBigNat_def(N:BigNat) : bool
	requires WellformedBigNat(N);
{
	if (zero(N)) then
		true
	else
		WordIsEven(lo(N))
}

lemma lemma_IsEvenBigNat(N:BigNat)
	requires WellformedBigNat(N);
	ensures IsEvenBigNat_def(N) == IsEven(I(N));
{
	if (zero(N)) {
		calc {
			IsEvenBigNat_def(N);
			true;
				{ assert 0 * 2 == 0; }
			IsEven(0);
			IsEven(I(N));
		}
	}
	else
	{
		calc {
			IsEvenBigNat_def(N);
			WordIsEven(lo(N));
			IsEven(lo(N));
				{ lemma_bignat_even(N); }
			IsEven(I(N));
		}
	}
}

function method IsEvenBigNat(N:BigNat) : bool
	requires WellformedBigNat(N);
	ensures IsEvenBigNat(N) == IsEven(I(N));
{
	lemma_IsEvenBigNat(N);
	IsEvenBigNat_def(N)
}

lemma lemma_dividing_by_two(n:nat, q:nat, r:nat)
	requires 0 < n;
	requires mul(q,2)+r==n;
	requires r<2;
	requires IsEven(n);
	ensures 0 < q;
	ensures q < n;
	ensures r == 0;
{
	if (r!=0)
	{
		var y:nat :| y*2==n;
		assert r==1;
		calc ==> {
			mul(q,2)+1==n;
			mul(q,2)+1==y*2;
				{ lemma_mul_is_mul_boogie(y,2); }
			mul(q,2)+1==mul(y,2);
			1==mul(y,2) - mul(q,2);
				{ lemma_mul_is_commutative_forall(); }
			1==mul(2,y) - mul(2,q);
				{ lemma_mul_is_distributive_sub(2,y,q); }
			1==mul(2,y-q);
				{ lemma_mul_is_mul_boogie(2,y-q); }
			1==2*(y-q);
				{ lemma_no_half(y-q); }
			false;
		}
	}
	assert r==0;

	calc ==> {
		0 < mul(q,2);
			{ lemma_mul_basics(2); }
		mul(0,2) < mul(q,2);
			{ lemma_mul_strict_inequality_converse(0,q,2); }
		0 < q;
	}

	calc ==> {
		true;
			{ lemma_mul_strictly_increases(2,q); }
		q < mul(2,q);
			{ lemma_mul_is_commutative_forall(); }
		q < mul(q,2);
		q < n;
	}
}

method MR_find_s_D(N:BigNat, two:BigNat) returns (s:nat, D:BigNat)
	decreases I(N);
	requires ModestBigNatWords(N);
	requires 0 < I(N);
	requires WellformedBigNat(two);
	requires I(two) == 2;
	requires ModestBigNatWords(two);
	requires nonzero(two);
	ensures  WellformedBigNat(D);
	ensures  0 < I(D);
	ensures  power2(s)*I(D) == I(N);
	ensures  I(D) <= I(N);
	ensures  !IsEven(I(D));
	// TODO this is a silly runtime implementation, dividing out 2s one
	// after another! A better impl would count zero-valued LSBs and
	// shift them off in one step. If we had shifts.
{
	if (IsEvenBigNat(N))
	{
		lemma_2to32();
		assert 2 < Width();

		assert ModestBigNatWords(N);
		var Nover2:BigNat,zero:BigNat := BigNatDiv(N, two);

		lemma_dividing_by_two(I(N), I(Nover2), I(zero));
		assert 0 < I(Nover2);
		assert I(Nover2) < I(N);
		assert I(zero)==0;	// else !WordIsEven()

		calc ==> {
			I(Nover2) <= I(N);
				{ lemma_modesty_word_value_equivalence(N); }
			I(Nover2) < KindaBigNat();
				{ lemma_modesty_word_value_equivalence(Nover2); }
			ModestBigNatWords(Nover2);
		}
		var sub_s:nat;
		sub_s,D := MR_find_s_D(Nover2, two);
		s := sub_s + 1;

		calc {
			power2(s) * I(D);
			power2(sub_s+1) * I(D);
				{ lemma_power2_adds(sub_s,1); }
			mul(power2(sub_s), power2(1)) * I(D);
				{ lemma_mul_is_commutative_forall(); }
			I(D) * mul(power2(sub_s), power2(1));
				{ lemma_mul_is_associative_forall(); }
			mul(mul(I(D), power2(sub_s)), power2(1));
				{ lemma_mul_is_commutative_forall(); }
			mul(mul(power2(sub_s), I(D)), power2(1));
			mul(I(Nover2), power2(1));
				{ lemma_power2_1_is_2(); }
			mul(I(Nover2), 2);
			mul(I(Nover2), I(two));
			mul(I(Nover2), I(two))+I(zero);
			I(N);
		}
	}
	else
	{
		s := 0;
		D := N;
		calc {
			power2(s)*I(D);
			power2(0)*I(D);
				{ lemma_power2_0_is_1(); }
			mul(1,I(D));
				{ lemma_mul_basics_forall(); }
			I(D);
			I(N);
		}
		
		lemma_WordIsEven(lo(N));
		assert !IsEvenBigNat(N);
		assert !IsEven(I(N));
		assert !IsEven(I(D));
	}
}

lemma lemma_even_divisble_by_2(x:int)
	requires 0 <= x;
	requires IsEven(x);
	ensures  divides(2,x);
{
	lemma_even_mod_0_pos(x);
	assert mod(x, 2) == 0;
	assert divides(2,x);
}

method ProbeLoop(N:BigNat, Nminus1:BigNat, Xinit:BigNat, s:int, ghost problem:MRProblem, ghost probe_init:MRProbe)
	returns (isProbablyPrime:bool, ghost probe:MRProbe)

	requires FrumpyBigNat(N);
	requires I(N) > 3;
	requires WellformedBigNat(Nminus1);
	requires I(Nminus1) == I(N) - 1;
	requires FrumpyBigNat(Xinit);
	requires MRProblemValid(problem);
	requires probe_init.squares == [I(Xinit)];
	requires MRProbeInit(problem, probe_init);
	requires problem.n == I(N);
	requires problem.s == s;
	ensures probe.a == probe_init.a;
	ensures isProbablyPrime ==> MRProbeSuccessful(problem, probe);
{
	lemma_frumpy_is_modest(N);

	isProbablyPrime := true;
	probe := probe_init;

	var si:int := 1;
	var probing := true;
	var X:BigNat := Xinit;
	while (si <= s-1)
		invariant FrumpyBigNat(X);
		invariant MRProblemValid(problem);
		invariant 0 < |probe.squares|;
		invariant 0<s ==> |probe.squares| <= s;
		invariant MRProbeInit(problem, probe);
		invariant si==|probe.squares|;
		invariant probe.a == probe_init.a;
		invariant probe.squares[si-1] == I(X);
		invariant isProbablyPrime ==>
			(forall i :: 0<i<si ==>
				MRProbeChain(problem, probe, i));
		invariant !isProbablyPrime || probing || MRProbeSuccessful(problem, probe);
		invariant isProbablyPrime && !probing ==> probe.squares[|probe.squares|-1]==problem.n-1;
	{
		var Xsquared:BigNat := BigNatMul(X,X);
		lemma_mul_positive(I(X),I(X));
		lemma_frumpy_squared_is_modest(X,Xsquared);
		assert 0 <= I(Xsquared);
		assert 0 < I(N);
		var oldX := X;
		X := BigNatModulo(Xsquared, N);

		ghost var old_probe := probe;
		assert |old_probe.squares|==si;
		assert forall i :: 0<i<|old_probe.squares| ==>
			MRProbeChain(problem, old_probe, i);
		probe := MRProbe_c(probe.a, probe.squares + [I(X)]);

		lemma_mod_pos_bound(I(Xsquared),I(N));
		assert I(X) < I(N);
		assert FrumpyBigNat(X);
		lemma_2to32();
		var is_one:bool := TestEqSmallLiteralBigNat(1, X);
		if (is_one)
		{
			// n divides (a^{d2^{r-1}}-1)(a^{d2^{r-1}}+1);
			// hence n could be factored. In a lemma that I'm
			// not going to write just yet.
			isProbablyPrime := false;
			break;
		}
		assert |probe.squares| == si+1;
		calc {
			probe.squares[si];
			I(X);
			I(Xsquared) % I(N);
			(I(oldX)*I(oldX)) % I(N);
				{ lemma_square_is_power_2(I(oldX)); }
			power(I(oldX),2) % I(N);
				{ assert probe.squares[si-1] == I(oldX); }
			power(probe.squares[si-1],2) % I(N);
			power(probe.squares[si-1],2) % problem.n;
		}
		assert probe.squares[si] == power(probe.squares[si-1], 2) % problem.n;
		assert MRProbeChain(problem, probe, si);
		var is_nminus1:bool := BigNatEq(X, Nminus1);

		if (is_nminus1)
		{
			// "do next WitnessLoop" -- this one is successful
			probing := false;
//			calc {
//				|probe.squares|;
//				|old_probe.squares|+1;
//				si+1;
//				<= s;
//				problem.s;
//			}
			calc {
				|probe.squares|;
				si+1;
				<= s;
			}
			calc {
				probe.squares[|probe.squares|-1];
				I(X);
				I(Nminus1);
				I(N)-1;
				problem.n-1;
			}
			forall (i | 0<i<|probe.squares|)
				ensures MRProbeChain(problem, probe, i);
			{
				if (i<|old_probe.squares|)
				{
					assert i < |old_probe.squares|;	// DUNBROKE
					assert MRProbeChain(problem, old_probe, i);
					assert MRProbeChain(problem, probe, i);
				}
				else
				{
					assert i==|probe.squares|-1==si;
					assert MRProbeChain(problem, probe, i);
				}
			}

			assert MRProbeSuccessful(problem, probe);
			break;
		}

		ghost var old_si:int := si;
		assert forall i :: 0<i<old_si ==>
			MRProbeChain(problem, old_probe, i);
		forall (i | 0<i<old_si)
			ensures MRProbeChain(problem, probe, i);
		{
			assert MRProbeChain(problem, old_probe, i);
			assert probe.squares[i]==old_probe.squares[i];
		}
		si := si + 1;
		assert MRProbeChain(problem, probe, si-1);
		forall (i | 0<i<si)
			ensures MRProbeChain(problem, probe, i);
		{
		}
		assert forall i :: 0<i<si ==>
				MRProbeChain(problem, probe, i);
	}

	if (probing)
	{
		// Unsatisfactory initial X, and never
		// found the x-1 we needed in s-1 additional steps.
		isProbablyPrime := false;
	}

	assert isProbablyPrime ==>
		(forall i:int :: (0<i<si ==>
			MRProbeChain(problem, probe, i)));

	if (isProbablyPrime)
	{
		assert 0<s;
		assert |probe.squares| <= s;
		assert s == problem.s;
		assert |probe.squares| <= problem.s;
		assert probe.squares[|probe.squares|-1] == problem.n - 1;
		assert MRProbeSuccessful(problem, probe);
	}
	assert isProbablyPrime ==> MRProbeSuccessful(problem, probe);
}

method WitnessLoop(N:BigNat, Nminus1:BigNat, Nminus2:BigNat, D:BigNat, s:int, two:BigNat, strength:nat, ghost problem:MRProblem)
	returns (isProbablyPrime:bool, ghost probes:seq<MRProbe>)

	requires FrumpyBigNat(N);
	requires I(N) > 3;
	requires WellformedBigNat(Nminus1);
	requires I(Nminus1) == I(N) - 1;
	requires ModestBigNatWords(Nminus2);
	requires I(Nminus2) == I(N) - 2;
	requires FrumpyBigNat(D);
	requires ModestBigNatWords(two);
	requires I(two) == 2;
	requires nonzero(two);
	requires strength >= MILLER_RABIN_STRENGTH();
	requires MRProblemValid(problem);
	requires problem.n == I(N);
	requires problem.strength == strength;
	requires problem.s == s;
	requires problem.d == I(D);
	ensures isProbablyPrime ==> ValidMillerRabinSpec(problem, probes);
{
	probes := [];

	var ki:int :=0;
	while (ki < strength && isProbablyPrime)
		decreases strength - ki;
		invariant isProbablyPrime ==>
			(forall probe :: probe in probes
				==> MRProbeSuccessful(problem, probe));
		invariant MRProblemValid(problem);
		invariant |probes|==ki;
	{
		var A:BigNat := BigNatRandomFromInclusiveRange(two, Nminus2);
		var X:BigNat := BigNatModExp(A, D, N);
		assert FrumpyBigNat(X);

		ghost var probe:MRProbe := MRProbe_c(I(A), [I(X)]);
		calc {
			probe.squares[0];
			I(X);
			power(I(A),I(D)) % I(N);
			power(probe.a, problem.d) % problem.n;
		}
		assert MRProbeInit(problem, probe);

		var is_one:bool := TestEqSmallLiteralBigNat(1, X);
		if (is_one)
		{	// "continue"
			assert probe.squares==[I(X)]==[1];
			assert MRProbeSuccessful(problem, probe);
		}
		else
		{
			var is_nminus1:bool := BigNatEq(X, Nminus1);
			if (is_nminus1)
			{	// "continue"
				calc {
					probe.squares;
					[I(X)];
					[I(Nminus1)];
					[I(N)-1];
					[problem.n - 1];
				}
				assert MRProbeSuccessful(problem, probe);
			}
			else
			{
				isProbablyPrime,probe := ProbeLoop(N, Nminus1, X, s, problem, probe);
			} // "continue"
		} // "continue"

		probes := probes + [probe];

		ki := ki + 1;
	}
//	assert !(ki < strength && isProbablyPrime);
//	assert (ki >= strength || !isProbablyPrime);
	if (isProbablyPrime)
	{
		assert strength <= ki;
		assert forall probe :: probe in probes
			==> MRProbeSuccessful(problem, probe);
		calc {
			problem.strength;
			strength;
			<= ki;
			|probes|;
		}
		assert ValidMillerRabinSpec(problem, probes);
	}
}

method MillerRabinTest(N:BigNat, strength:nat) returns (isProbablyPrime:bool)
	requires FrumpyBigNat(N);
	requires I(N) > 3;
	requires strength >= MILLER_RABIN_STRENGTH();
	ensures isProbablyPrime ==> IsProbablyPrime(I(N), strength);
{
	lemma_frumpy_is_modest(N);

	if (IsEvenBigNat(N))
	{
		lemma_even_divisble_by_2(I(N));
		assert divides(2, I(N));
		assert !IsPrime(I(N));
		isProbablyPrime := false;
	}
	else
	{
		var one:BigNat := MakeSmallLiteralBigNat(1);
		lemma_2to32();
		assert 2 < Width();
		var two:BigNat := MakeSmallLiteralBigNat(2);
		var Nminus1:BigNat := BigNatSub(N,one);

		lemma_modesty_word_value_equivalence(N);
		lemma_modesty_word_value_equivalence(Nminus1);
		assert ModestBigNatWords(Nminus1);

		var Nminus2:BigNat := BigNatSub(N,two);
		lemma_modesty_word_value_equivalence(Nminus2);

		var s:int,D:BigNat := MR_find_s_D(Nminus1, two);
		assert FrumpyBigNat(D);

		ghost var problem:MRProblem := MRProblem_c(I(N), strength, s, I(D));
		assert s==problem.s;

		lemma_x_odd(I(N));
		lemma_x_odd(I(D));
		calc {
			power(2,problem.s)*problem.d;
			power(2,s)*I(D);
				{ lemma_power2_is_power_2(s); }
			power2(s)*I(D);
			I(N)-1;
		}
		lemma_mod_is_mod_boogie_for_2_which_is_also_a_number(I(N));
		lemma_mod_is_mod_boogie_for_2_which_is_also_a_number(I(D));
		assert MRProblemValid(problem);

		ghost var probes:seq<MRProbe>;
		isProbablyPrime,probes := WitnessLoop(N, Nminus1, Nminus2, D, s, two, strength, problem);
		if (isProbablyPrime)
		{
			MillerRabinSpec(problem, probes);
		}
	}
}
