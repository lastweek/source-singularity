include "BigNum.dfy"
include "../Math/mul.dfy"

datatype BigRat = BigRat_ctor(
    n : BigNum,
    d : BigNat);

static function WellformedBigRat(Q:BigRat) : bool
{
    WellformedBigNum(Q.n) && WellformedBigNat(Q.d) && !zero(Q.d)
}

static function RV(Q:BigRat) : real
    requires WellformedBigRat(Q);
{
    real_of(BV(Q.n)) / real_of(I(Q.d))
}

function method BigRatNegate(Q:BigRat) : BigRat
    requires WellformedBigRat(Q);
    ensures WellformedBigRat(BigRatNegate(Q));
    ensures RV(BigRatNegate(Q)) == real_of(0) - RV(Q);
{
    BigRat_ctor(BigNumNegate(Q.n), Q.d)
}

method BigRatAdd(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) + RV(B);
{
    var ScaledANumerator:BigNum := BigNumMul(A.n, BigNum_ctor(false, B.d));
    var ScaledBNumerator:BigNum := BigNumMul(B.n, BigNum_ctor(false, A.d));
    var ResultNumerator:BigNum := BigNumAdd(ScaledANumerator, ScaledBNumerator);
    var ResultDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);

    Lemma_RealOfMultiplyIsMultiply(BV(A.n), I(B.d));
    Lemma_RealOfMultiplyIsMultiply(I(A.d), I(B.d));
    Lemma_RealOfMultiplyIsMultiply(BV(B.n), I(A.d));
    Lemma_RealOfMultiplyIsMultiply(I(B.d), I(A.d));
}

method BigRatSub(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) - RV(B);
{
    var ScaledANumerator:BigNum := BigNumMul(A.n, BigNum_ctor(false, B.d));
    var ScaledBNumerator:BigNum := BigNumMul(B.n, BigNum_ctor(false, A.d));
    var ResultNumerator:BigNum := BigNumSub(ScaledANumerator, ScaledBNumerator);
    var ResultDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);

    Lemma_RealOfMultiplyIsMultiply(BV(A.n), I(B.d));
    Lemma_RealOfMultiplyIsMultiply(I(A.d), I(B.d));
    Lemma_RealOfMultiplyIsMultiply(BV(B.n), I(A.d));
    Lemma_RealOfMultiplyIsMultiply(I(B.d), I(A.d));
}

method BigRatCmp(A:BigRat, B:BigRat) returns (c:Cmp)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures (c==CmpLt) <==> (RV(A)  < RV(B));
    ensures (c==CmpEq) <==> (RV(A) == RV(B));
    ensures (c==CmpGt) <==> (RV(A)  > RV(B));
{
    var ScaledANumerator:BigNum := BigNumMul(A.n, BigNum_ctor(false, B.d));
    var ScaledBNumerator:BigNum := BigNumMul(B.n, BigNum_ctor(false, A.d));
    c := BigNumCmp(ScaledANumerator, ScaledBNumerator);

    ghost var CommonDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    ghost var ScaledA := BigRat_ctor(ScaledANumerator, CommonDenominator);
    ghost var ScaledB := BigRat_ctor(ScaledBNumerator, CommonDenominator);
    Lemma_ScalingPreservesValue(A, ScaledA, B.d);
    lemma_mul_is_commutative(I(A.d), I(B.d));
    Lemma_ScalingPreservesValue(B, ScaledB, A.d);
    Lemma_DivideByPositiveRealPreservesOrder(real_of(BV(ScaledANumerator)), real_of(BV(ScaledBNumerator)), real_of(I(CommonDenominator)));
}

method BigRatLt(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) < RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c==CmpLt);
}

method BigRatLe(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) <= RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c==CmpLt || c==CmpEq);
}

method BigRatEq(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) == RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c==CmpEq);
}

method BigRatNe(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) != RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c!=CmpEq);
}

method BigRatGe(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) >= RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c==CmpGt || c==CmpEq);
}

method BigRatGt(A:BigRat, B:BigRat) returns (r:bool)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures r == (RV(A) > RV(B));
{
    var c := BigRatCmp(A,B);
    r := (c==CmpGt);
}

method BigRatMul(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) * RV(B);
{
    var ResultNumerator:BigNum := BigNumMul(A.n, B.n);
    var ResultDenominator:BigNat := BigNatMul(A.d, B.d);
    lemma_mul_nonzero(I(A.d), I(B.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);

    Lemma_RealOfMultiplyIsMultiply(BV(A.n), BV(B.n));
    Lemma_RealOfMultiplyIsMultiply(I(A.d), I(B.d));
}

method BigRatDiv(A:BigRat, B:BigRat) returns (R:BigRat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(B);
    requires nonzero(B.n.value);
    ensures WellformedBigRat(R);
    ensures RV(R) == RV(A) / RV(B);
{
    var ResultNegative:bool := (A.n.negate != B.n.negate) && !zero(A.n.value);
    var ResultNumerator:BigNum := BigNumMul(BigNum_ctor(ResultNegative, A.n.value), BigNum_ctor(false, B.d));
    var ResultDenominator:BigNat := BigNatMul(B.n.value, A.d);
    lemma_mul_nonzero(I(B.n.value), I(A.d));
    R := BigRat_ctor(ResultNumerator, ResultDenominator);

    Lemma_RealOfMultiplyIsMultiply(BV(BigNum_ctor(ResultNegative, A.n.value)), BV(BigNum_ctor(false, B.d)));
    Lemma_RealOfMultiplyIsMultiply(I(B.n.value), I(A.d));
    assert I(ResultDenominator) == I(B.n.value) * I(A.d);
}

function method MakeSmallLiteralBigRat(x:nat) : BigRat
    requires x < Width();
    ensures WellformedBigRat(MakeSmallLiteralBigRat(x));
    ensures RV(MakeSmallLiteralBigRat(x)) == real_of(x);
{
    lemma_2toX();
    BigRat_ctor(MakeSmallLiteralBigNum(x), MakeSmallLiteralBigNat(1))
}

function method BigNatToBigRat(x:BigNat) : BigRat
    requires WellformedBigNat(x);
    ensures WellformedBigRat(BigNatToBigRat(x));
    ensures RV(BigNatToBigRat(x)) == real_of(I(x));
{
    lemma_2toX();
    BigRat_ctor(BigNum_ctor(false, x), MakeSmallLiteralBigNat(1))
}

///////////////////////////////////
// Useful mathematical lemmas
///////////////////////////////////

lemma Lemma_RealOfMultiplyIsMultiply(a:int, b:int)
    ensures real_of(a * b) == real_of(a) * real_of(b);
{
  lemma_mul_is_mul_boogie(a, b);
}

lemma Lemma_ScalingPreservesValue(A:BigRat, ScaledA:BigRat, scale:BigNat)
    requires WellformedBigRat(A);
    requires WellformedBigRat(ScaledA);
    requires WellformedBigNat(scale);
    requires nonzero(scale);
    requires BV(ScaledA.n) == BV(A.n) * I(scale);
    requires I(ScaledA.d) == I(A.d) * I(scale);
    ensures RV(A) == RV(ScaledA);
{
    Lemma_RealOfMultiplyIsMultiply(BV(A.n), I(scale));
    Lemma_RealOfMultiplyIsMultiply(I(A.d), I(scale));
}

lemma Lemma_DivideByPositiveRealPreservesOrder(a:real, b:real, c:real)
    requires c > real_of(0);
    ensures a < b <==> a/c < b/c;
    ensures a == b <==> a/c == b/c;
    ensures a > b <==> a/c > b/c;
{
}
