// Spec. TODO move to spec dir

include "Word32.dfy"

method {:axiom} Add32_with_carry(a:nat, b:nat, c:nat) returns (sum:nat, carry:nat)
	requires Word32(a);
	requires Word32(b);
	requires c==0 || c==1;
	ensures Word32(sum);
	ensures carry==0 || carry==1;
	ensures a+b+c == sum + INTERNAL_mul(carry,Width());

method {:axiom} Sub32_with_borrow(a:nat, b:nat, c:nat) returns (difference:nat, carry:nat)
	requires Word32(a);
	requires Word32(b);
	requires c==0 || c==1;
	ensures Word32(difference);
	ensures carry==0 || carry==1;
	ensures a-b-c == difference - INTERNAL_mul(carry,Width());

method {:axiom} Product32(a:nat, b:nat) returns (l:nat, h:nat)
	requires Word32(a);
	requires Word32(b);
	ensures Word32(l);
	ensures Word32(h);
	ensures l+INTERNAL_mul(h,Width()) == INTERNAL_mul(a,b);

method {:axiom} Divide32(n:nat, d:nat) returns (q:nat, r:nat)
	requires Word32(n);
	requires Word32(d);
	ensures Word32(q);
	ensures Word32(r);
	ensures 0<=r<d;
	ensures INTERNAL_mul(q,d) + r == n;

//method ArithmeticShiftLeft32(n:nat, s:nat) returns v:nat
//	requires Word32(n);
//	requires s<=32;
//	ensures Word32(v);
//	ensures INTERNAL_mul(n, power2(s)) == v + something;
//
//method ArithmeticShiftRight32(n:nat, s:nat) returns v:nat
//	requires Word32(n);
//	requires s<=32;
//	ensures Word32(v);
//	ensures INTERNAL_mul(v, power2(s)) + something == n;



method {:axiom} Random32() returns (r:nat)
	ensures Word32(r);
