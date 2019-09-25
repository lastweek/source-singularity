include "FleetNatAdd.i.dfy"
include "FleetNatMulOpt.i.dfy"

//- mpi_mul_hlp uses 16/8/1 unrolling and muladdc and optionally a special MULADDC_HUIT instruction
//- then it propagates the carries out.
//- s is the source value, d is the dest value (shifted with pointer math), b is the single
//- limb being multiplied in.
//- mpi_mul_mpi counts up the zeros and preallocates i+j, since that's actually precise.




lemma lemma_FleetNatMul_one_partial_sum_induction(pv:int,
    oldcs:seq<int>, lastcs:seq<int>, cs:seq<int>, asq:seq<int>, adigits:int,
    bi:int, bv:int, j:int, lastj:int, carry:int, lastcarry:int,
    lastcj:int, newcj:int)
    requires pv==power2(32);
    requires IsWordSeq(cs);
    requires IsWordSeq(oldcs);
    requires IsWordSeq(lastcs);
    requires IsWordSeq(asq);
    requires |cs|==|lastcs|==|oldcs|;
    requires forall i :: 0<=i<|cs| && i!=|cs|-1-(lastj+bi) ==> lastcs[i]==cs[i];
    requires lastj+1 == j <= adigits <= |asq|;
    requires 0 <= lastj;
    requires 0 <= bi;
    requires lastj+bi < |cs|;
    //- element operation components
    requires lastcj == DigitAt(lastcs, lastj+bi);
    requires newcj == DigitAt(cs, lastj+bi);
    requires newcj + carry*pv == DigitAt(asq, lastj) * bv + lastcj + lastcarry;
    requires 0<=carry<pv;
    //- loop invariants
    requires BEWordSeqToInt(lastcs) + lastcarry*power(pv, lastj+bi)
        == BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0)) * bv * power(pv, bi);
    ensures BEWordSeqToInt(cs) + carry*power(pv, j+bi)
        == BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, j, 0)) * bv * power(pv, bi);
{
    assert SelectDigitRange(lastcs, |lastcs|, j+bi) == SelectDigitRange(cs, |cs|, j+bi);    //- OBSERVE SEQ
    assert SelectDigitRange(lastcs, lastj+bi, 0) == SelectDigitRange(cs, lastj+bi, 0);  //- OBSERVE SEQ
    calc {
        BEWordSeqToInt(lastcs);
            { lemma_PluckDigit(cs, lastj+bi);
              lemma_PluckDigit(lastcs, lastj+bi); }
        BEWordSeqToInt(cs)
         - DigitAt(cs, lastj+bi) * power(pv, lastj+bi)
         + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi);
    }
    
    var aj := DigitAt(asq, lastj);

    calc {
        BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, j, 0)) * bv * power(pv, bi);
            { lemma_mul_is_associative_forall(); }
        BEWordSeqToInt(oldcs)
         + BEWordSeqToInt(SelectDigitRange(asq, j, 0)) * (bv * power(pv, bi));
            { lemma_PluckDigit_general(asq, j, lastj, 0); }
        BEWordSeqToInt(oldcs) + (
          BEWordSeqToInt(SelectDigitRange(asq, j, j)) * power(pv, j)
          + aj * power(pv, lastj)
          + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0))
         )* (bv * power(pv, bi));
            { assert SelectDigitRange(asq, j, j)==[]; //- OBSERVE SEQ
              reveal_BEDigitSeqToInt_private(); }
        BEWordSeqToInt(oldcs) + (
          aj * power(pv, lastj)
          + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0))
         )* (bv * power(pv, bi));
            { lemma_mul_is_distributive_forall(); }
        aj * power(pv, lastj)* (bv * power(pv, bi))
          + BEWordSeqToInt(oldcs)
          + BEWordSeqToInt(SelectDigitRange(asq, lastj, 0))* (bv * power(pv, bi));
            { lemma_mul_is_associative_forall(); } //- apply partial sum hypothesis
        aj * power(pv, lastj)* (bv * power(pv, bi))
            + BEWordSeqToInt(lastcs) + lastcarry*power(pv, lastj+bi);
            //- earlier calc
        aj * power(pv, lastj)* (bv * power(pv, bi))
            + BEWordSeqToInt(cs)
            - DigitAt(cs, lastj+bi) * power(pv, lastj+bi)
            + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi)
            + lastcarry*power(pv, lastj+bi);
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv, lastj, bi); }
        aj * bv * power(pv, lastj + bi)
            + BEWordSeqToInt(cs)
            - DigitAt(cs, lastj+bi) * power(pv, lastj+bi)
            + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi)
            + lastcarry*power(pv, lastj+bi);
            { lemma_mul_is_distributive_forall(); }
        (aj * bv - DigitAt(cs, lastj+bi) + DigitAt(lastcs, lastj+bi) + lastcarry)
                * power(pv, lastj + bi)
            + BEWordSeqToInt(cs);
            { lemma_power_1(pv); }  //- and apply earlier calc
        BEWordSeqToInt(cs) + carry*power(pv,1) * power(pv, lastj+bi);
            { lemma_mul_is_associative_forall(); lemma_power_adds(pv,1,lastj+bi); }
        BEWordSeqToInt(cs) + carry*power(pv, j+bi);
    }
}

method FleetNatMul_one(c:array<int>, bi:nat, a:array<int>, adigits:int, bv:int)
    requires c!=null;
    requires IsDigitSeq(power2(32), c[..]);
    requires a!=c;
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires 0<=adigits<=a.Length;
    requires adigits <= c.Length;
    //- c-adequate-length requirement:
    requires BEWordSeqToInt(c[..])
         + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi)
        < power(power2(32), c.Length);
    requires adigits + bi <= c.Length;
    requires 0 <= bv < power2(32);
    modifies c;
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(c[..])
        == BEWordSeqToInt(old(c[..]))
         + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi);
{
    ghost var pv := power2(32);
    lemma_2toX();
    ghost var oldcs := c[..];

    var alenm1 := a.Length-1;
    var clenm1 := c.Length-1;
    var j := 0;
    var carry := 0;
    lemma_BEWordSeqToInt_SelectDigitRange_empty(a[..]); //- establish partial sum invariant
    lemma_BEInterpretation_Select_general(pv, a[..], adigits, j, 0);    //- establish carry invariant
    while (j < adigits)
        invariant 0<=j<=adigits;
        invariant IsDigitSeq(pv, c[..]);
        invariant 0<=carry<pv;
        //- partial sum invariant:
        invariant BEWordSeqToInt(c[..]) + carry*power(pv, j+bi)
            == BEWordSeqToInt(oldcs)
             + BEWordSeqToInt(SelectDigitRange(a[..], j, 0)) * bv * power(pv, bi);
    {
        ghost var lastj := j;
        ghost var lastcarry := carry;
        ghost var lastcs := c[..];
        ghost var asq := a[..];

        var ci := clenm1 - (j+bi);
        var ai := alenm1 - j;
        var aj := a[ai];
        var lastcj := c[ci];
        var newcj;

//- #if opt
        newcj,carry := FleetNatMulMathOpt(aj, bv, lastcj, carry);
//- #endif opt
//- #if standard
//-        //- mul
//-        lemma_mod_properties();
//-        lemma_word32(aj);
//-        lemma_word32(bv);
//-        var mhi,mlo := asm_Mul64(aj, bv);
//-        lemma_asm_Mul64(aj, bv, mhi, mlo);
//-
//-        //- add1
//-        lemma_word32(mlo);
//-        lemma_word32(lastcarry);
//-        var add1 := asm_Add(mlo, carry);
//-        var carry1 := 0;
//-        if (add1 < carry) { carry1 := 1; }
//-        lemma_asm_Add_properties(mlo, lastcarry, add1, carry1);
//-
//-        //- add2
//-        lemma_word32(lastcj);
//-        newcj := asm_Add(add1, lastcj);
//-        var carry2 := 0;
//-        if (newcj < lastcj) { carry2 := 1; }
//-        lemma_asm_Add_properties(add1, lastcj, newcj, carry2);
//-
//-        //- add3
//-        lemma_word32(carry1);
//-        lemma_word32(carry2);
//-        var add3 := asm_Add(carry1, carry2);
//-        ghost var carry3 := 0;
//-        if (add3 < carry2) { carry3 := 1; }
//-        lemma_asm_Add_properties(carry1, carry2, add3, carry3);
//-
//-        //- add4
//-        carry := asm_Add(add3, mhi);
//-        ghost var carry4 := 0;
//-        if (carry < mhi) { carry4 := 1; }
//-        lemma_asm_Add_properties(add3, mhi, carry, carry4);
//-
//-        lemma_FleetNatMul_one_element_properties(pv,
//-            aj, bv, mhi, mlo,
//-            lastcarry, add1, carry1,
//-            lastcj, newcj, carry2,
//-            add3, carry3,
//-            carry, carry4);
//- #endif standard

        c[ci] := newcj;
        j := j + 1;

        lemma_FleetNatMul_one_partial_sum_induction(
            pv, oldcs, lastcs, c[..], a[..], adigits, bi, bv, j, lastj, carry, lastcarry,
            lastcj, newcj);
//-        lemma_FleetNatMul_one_carry_induction(
//-            pv, oldcs, lastcs, c[..], a[..], adigits, bi, bv, j, lastj, carry, lastcarry);
    }

    //- propagate the carry out
    while (carry > 0)
        invariant adigits<=j<=c.Length;
        invariant 0<=carry<pv;
        invariant IsDigitSeq(pv, c[..]);
        invariant BEWordSeqToInt(c[..]) + carry*power(pv, j+bi)
            == BEWordSeqToInt(oldcs)
             + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(pv, bi);
        decreases c.Length - j;
    {
        ghost var lastcs := c[..];
        ghost var lastj := j;
        ghost var lastcarry := carry;

        if (j+bi >= c.Length)
        {
            calc {
                power(pv, c.Length);
                >  //- contradicts requirement c-adequate-length.
                BEWordSeqToInt(oldcs)
                 + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(pv, bi);
                BEWordSeqToInt(c[..]) + carry*power(pv, j+bi);
                >=  { lemma_BEWordSeqToInt_bound(c[..]); }
                carry*power(pv, j+bi);
                >=  { lemma_power_positive(pv,j+bi); lemma_mul_increases(carry, power(pv, j+bi)); }
                power(pv, j+bi);
                >=  { lemma_power_increases(pv, c.Length, j+bi); }
                power(pv, c.Length);
            }
        }
        var ci := clenm1 - (j+bi);
        var lastcj := c[ci];

        lemma_word32(carry);
        lemma_word32(lastcj);
        var newcj := asm_Add(carry, lastcj);
        lemma_mod0x100000000(carry+lastcj);
        c[ci] := newcj;
        carry := 0;
        if (newcj < lastcj) { carry := 1; }
        j := j + 1;
        

        calc {
            newcj * power(pv, lastj+bi) + carry*power(pv, j+bi);
            {
                lemma_mod0x100000000(lastcarry+lastcj);
                lemma_mod_properties();
                lemma_asm_Add_properties(lastcarry, lastcj, newcj, carry);
            }
            (lastcarry+lastcj-pv*carry) * power(pv, lastj+bi) + carry*power(pv, j+bi);
                { lemma_mul_is_distributive_forall(); }
            lastcj*power(pv,lastj+bi) + lastcarry*power(pv,lastj+bi)
                - (pv*carry)*power(pv,lastj+bi) + carry*power(pv, j+bi);
            {
                calc {
                    (pv * carry) * power(pv,lastj+bi);
                        { lemma_mul_is_associative_forall(); }
                    carry * (pv*power(pv,lastj+bi));
                        { lemma_power_1(pv); }
                    carry * (power(pv,1)*power(pv,lastj+bi));
                        { lemma_power_adds(pv,1,lastj+bi); }
                    carry * power(pv,j+bi);
                }
            }
            lastcj*power(pv, lastj+bi) + lastcarry * power(pv, lastj+bi);
        }
        ghost var leftjunk := BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j+bi));
        assert SelectDigitRange(c[..], c.Length, j+bi) == SelectDigitRange(lastcs, |lastcs|, j+bi);   //- OBSERVE SEQ
        ghost var rightjunk := BEWordSeqToInt(SelectDigitRange(c[..], lastj+bi, 0));
        assert SelectDigitRange(c[..], lastj+bi, 0) == SelectDigitRange(lastcs, lastj+bi, 0); //- OBSERVE SEQ
        calc {
            BEWordSeqToInt(c[..]) + carry*power(pv, j+bi);
                { lemma_PluckDigit(c[..], lastj+bi); }
            BEWordSeqToInt(SelectDigitRange(c[..], c.Length, j+bi)) * power(pv, j+bi)
                + DigitAt(c[..], lastj+bi) * power(pv, lastj+bi)
                + BEWordSeqToInt(SelectDigitRange(c[..], lastj+bi, 0))
                + carry*power(pv, j+bi);
            leftjunk * power(pv, j+bi)
                + newcj * power(pv, lastj+bi)
                + rightjunk
                + carry*power(pv, j+bi);
            leftjunk * power(pv, j+bi)
                + lastcj * power(pv, lastj+bi)
                + rightjunk
                + lastcarry * power(pv, lastj+bi);
            BEWordSeqToInt(SelectDigitRange(lastcs, |lastcs|, j+bi)) * power(pv, j+bi)
                + DigitAt(lastcs, lastj+bi) * power(pv, lastj+bi)
                + BEWordSeqToInt(SelectDigitRange(lastcs, lastj+bi, 0))
                + lastcarry * power(pv, lastj+bi);
                { lemma_PluckDigit(lastcs, lastj+bi); }
            BEWordSeqToInt(lastcs) + lastcarry * power(pv, lastj+bi);
        }
    }
}

lemma {:timeLimitMultiplier 2} lemma_FleetNatMul_c_adequate_length(a:array<int>, b:array<int>, adigits:nat, bdigits:nat, bi:nat, bv:int)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires b!=null;
    requires IsDigitSeq(power2(32), b[..]);
    requires 0<=adigits<=a.Length;
    requires 0<=bi<bdigits<=b.Length;
    requires BEWordSeqToInt(a[..]) == BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0));
    requires BEWordSeqToInt(a[..]) < power(power2(32), adigits);
    requires BEWordSeqToInt(b[..]) < power(power2(32), bdigits);
    requires bv == b[b.Length-1-bi];
    ensures BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0))
             + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi)
        < power(power2(32), adigits + bdigits);
{
    ghost var pv := power2(32); lemma_2toX();
    var aval := BEWordSeqToInt(a[..]);
    var bval := BEWordSeqToInt(b[..]);
    calc {
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0))
         + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(power2(32),bi);
            //-{ lemma_LeadingZeros(pv, [], SelectDigitRange(a[..], adigits, 0)); }
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0))
         + BEWordSeqToInt(a[..]) * bv * power(power2(32),bi);
            { lemma_mul_is_associative_forall(); lemma_mul_is_distributive_forall(); }
        BEWordSeqToInt(a[..]) * (
            BEWordSeqToInt(SelectDigitRange(b[..], bi, 0)) + bv * power(power2(32),bi));
            { lemma_BEDigitSeqToInt_singleton(pv, DigitAt(b[..], bi)); }
        BEWordSeqToInt(a[..]) *
            (BEDigitSeqToInt(pv, [DigitAt(b[..], bi)])*power(pv,bi)
                + BEDigitSeqToInt(pv, SelectDigitRange(b[..], bi, 0)));
            { lemma_SelectSingletonRange(b[..], bi+1, bi); }
        BEWordSeqToInt(a[..]) *
            (BEDigitSeqToInt(pv, SelectDigitRange(b[..], bi+1, bi))*power(pv,bi)
                + BEDigitSeqToInt(pv, SelectDigitRange(b[..], bi, 0)));
            { lemma_BEInterpretation_Select_general(pv, b[..], bi+1, bi, 0); }
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0));
        <= {
            calc {
                BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0));
                <= { lemma_BEWordSeqToInt_bound(SelectDigitRange(b[..], b.Length, bi+1));
                    lemma_power_positive(pv, bi+1);
                    lemma_mul_strictly_positive_forall();
                }
                BEWordSeqToInt(SelectDigitRange(b[..], b.Length, bi+1))*power(pv, bi+1)
                    + BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0));
                { lemma_BEInterpretation_Select_general(pv, b[..], b.Length, bi+1, 0); }
                BEWordSeqToInt(SelectDigitRange(b[..], b.Length, 0));
                { assert b[..] == SelectDigitRange(b[..], b.Length, 0); /* OBSERVE SEQ */ }
                BEWordSeqToInt(b[..]);
            }
            lemma_BEWordSeqToInt_bound(a[..]);
            lemma_mul_inequality(
                BEWordSeqToInt(SelectDigitRange(b[..], bi+1, 0)),
                BEWordSeqToInt(b[..]),
                BEWordSeqToInt(a[..]));
          }
        BEWordSeqToInt(a[..]) * BEWordSeqToInt(b[..]);
        aval * bval;
        <=  {
            lemma_BEWordSeqToInt_bound(b[..]);
            lemma_mul_inequality(aval, power(pv,adigits), bval); }
        power(pv, adigits) * bval;
        <   {
            lemma_power_positive(pv, adigits);
            lemma_mul_strict_inequality(bval, power(pv, bdigits), power(pv,adigits)); }
        power(pv, adigits) * power(pv, bdigits);
            { lemma_power_adds(pv, adigits, bdigits); }
        power(pv, adigits + bdigits);
    }
}

method FleetNatMul(a:array<int>, b:array<int>) returns (c:array<int>)
    requires a!=null;
    requires IsDigitSeq(power2(32), a[..]);
    requires b!=null;
    requires IsDigitSeq(power2(32), b[..]);
    ensures c!=null;
    ensures fresh(c);
    ensures IsDigitSeq(power2(32), c[..]);
    ensures BEWordSeqToInt(c[..]) == BEWordSeqToInt(a[..]) * BEWordSeqToInt(b[..]);
{
    ghost var pv := power2(32); lemma_2toX();
    var adigits := CountNonzeroDigits(a);
    var bdigits := CountNonzeroDigits(b);
    var cdigits := adigits + bdigits;

    c := FleetAlloc(cdigits);

    var bi := 0;

    lemma_LeadingZeros(pv, [], SelectDigitRange(b[..], bi, 0));
    lemma_BEWordSeqToInt_SelectDigitRange_empty(b[..]);

    var blenm1 := b.Length - 1;
    while (bi < bdigits)
        invariant 0<=bi<=bdigits;
        invariant IsDigitSeq(power2(32), c[..]);
        invariant BEWordSeqToInt(c[..]) == BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0));
    {
        ghost var lastc := c[..];
        ghost var lastbi := bi;
        var bv := b[blenm1 - bi];

        lemma_FleetNatMul_c_adequate_length(a, b, adigits, bdigits, bi, bv);
        FleetNatMul_one(c, bi, a, adigits, bv);
        bi := bi + 1;
        calc {
            BEWordSeqToInt(c[..]);
            BEWordSeqToInt(lastc)
                + BEWordSeqToInt(SelectDigitRange(a[..], adigits, 0)) * bv * power(pv,lastbi);
            BEWordSeqToInt(lastc)
                + BEWordSeqToInt(a[..]) * bv * power(pv,lastbi);
            BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0))
                + BEWordSeqToInt(a[..]) * bv * power(pv,lastbi);
                { lemma_mul_is_associative_forall(); lemma_mul_is_distributive_forall(); }
            BEWordSeqToInt(a[..]) * (
                BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0)) + bv * power(pv,lastbi));
                { lemma_SelectSingletonRange(b[..], bi, lastbi);
                  lemma_BEDigitSeqToInt_singleton(pv, DigitAt(b[..], lastbi)); }
            BEWordSeqToInt(a[..]) * (
                BEWordSeqToInt(SelectDigitRange(b[..], bi, lastbi)) * power(pv, lastbi)
                + BEWordSeqToInt(SelectDigitRange(b[..], lastbi, 0)));
                { lemma_BEInterpretation_Select_general(pv, b[..], bi, lastbi, 0); }
            BEWordSeqToInt(a[..]) * BEWordSeqToInt(SelectDigitRange(b[..], bi, 0));
        }
    }

    lemma_LeadingZeros(pv, SelectDigitRange(b[..], bi, 0), b[..]);
}
