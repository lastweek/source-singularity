include "../../../../Trusted/Spec/Libraries/Math/power.dfy"

datatype MRProblem = MRProblem_c(
	n:nat,
	strength:nat,
	s:nat,
	d:nat)

function method MILLER_RABIN_STRENGTH() : nat { 10 }

predicate MRProblemValid(problem:MRProblem)
{
	// Input: n > 3, an odd integer to be tested for primality;
	3 < problem.n
	&& problem.n%2==1

	// Input: k, a parameter that determines the accuracy of the test
	&& problem.strength >= MILLER_RABIN_STRENGTH()

	// write n - 1 as 2^s·d with d odd by factoring powers of 2 from n - 1
	&& problem.n-1 == power(2,problem.s)*problem.d
	&& problem.d%2==1
}

// The algorithm describes a "WitnessLoop" as one of the following.
// Our "MRProbe" is evidence of having done one of these.
// It captures a, plus the fact that we have either:
//		one x value x==1 or x==n-1 ("then do next WitnessLoop")
// or
//		<=s values, each the square-mod-n of the previous,
//		with no intermediate values equal to 1, and
//		with the last one equal to n-1.
//
//   pick a random integer a in the range [2, n - 2]
//   x := a^d mod n
//   if x = 1 or x = n - 1 then do next WitnessLoop
//   repeat s - 1 times:
//      x := x^2 mod n
//      if x = 1 then return composite
//      if x = n - 1 then do next WitnessLoop
//   return composite

datatype MRProbe = MRProbe_c(
	a:nat,
	squares:seq<int>)

predicate MRProbeInit(problem:MRProblem, probe:MRProbe)
	requires MRProblemValid(problem);
	requires 0 < |probe.squares|;
{
	probe.squares[0] == power(probe.a,problem.d) % problem.n
}

predicate MRProbeChain(problem:MRProblem, probe:MRProbe, i:nat)
	requires MRProblemValid(problem);
	requires 0 < i < |probe.squares|;
{
	probe.squares[i]==power(probe.squares[i-1], 2) % problem.n
	&& probe.squares[i]!=1
}

predicate MRProbeSuccessful(problem:MRProblem, probe:MRProbe)
	requires MRProblemValid(problem);
{
	0 < |probe.squares|
	&& MRProbeInit(problem,probe)
	&& (
		probe.squares==[1]
		|| probe.squares==[problem.n-1]
		|| ( |probe.squares| <= problem.s
			&& probe.squares[|probe.squares|-1]==problem.n-1
			&& forall i:int ::
				(0<i<|probe.squares| ==> MRProbeChain(problem, probe, i)))
		)
}

// If we want to be certain of compositeness, there's another requirement,
// which is that probes that don't end in 1 must be of length s.
// But we only care about primeness, so we don't bother specing that.

predicate ValidMillerRabinSpec(problem:MRProblem, probes:seq<MRProbe>)
	requires MRProblemValid(problem);
{
	problem.strength <= |probes|
	&& forall probe :: probe in probes ==> MRProbeSuccessful(problem, probe)
}

predicate IsProbablyPrime(n:nat,strength:nat)

lemma MillerRabinSpec(problem:MRProblem, probes:seq<MRProbe>)
	requires MRProblemValid(problem);
	requires ValidMillerRabinSpec(problem, probes);
	ensures IsProbablyPrime(problem.n, problem.strength);
{ assume false; }	// this is a spec axiom.

// TODO we could more directly translate the pseudocode into imperative
// dafny, and show that ValidMillerRabinSpec matches it.
