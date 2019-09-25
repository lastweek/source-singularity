// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    class Digits
    {
        readonly Digit[] _digits;
        readonly int _digitI;
        internal Digits(int n) { _digits = new Digit[n]; _digitI = 0; }
        internal Digits(Digit[] digits) { _digits = digits; _digitI = 0; }
        Digits(Digit[] digits, int digitI) {
            _digits = digits;
            _digitI = digitI;
        }
        internal Digit this[int i] {
            get {
                if (_digitI + i < _digits.Length) {
                    return _digits[_digitI + i];
                }
                else {
                    return 0;
                }
            }
            set {
                if (_digitI + i < _digits.Length) {
                    _digits[_digitI + i] = value;
                }
                else {
                    Debug.Assert(value == 0, "internal error");
                }
            }
        }
        int _N { get { return _digits.Length - _digitI; } }
        internal void _Set(Digits from, int n) {
            for (int i = 0; i < n; i++) {
                this[i] = from[i];
            }
        }
        internal void _SetAll(Digit val, int n) {
            for (int i = 0; i < n; i++) {
                this[i] = val;
            }
        }
        internal bool _Overlaps(Digits that) {
            return _digits.Equals(that._digits);
        }
        public static Digits operator +(Digits digits, int i) {
            return new Digits(digits._digits, digits._digitI + i);
        }
        public override string ToString() {
            string s = "(";
            for (int i = _digitI; i < _N; i++) {
                if (i > _digitI) {
                    s += ",";
                }
                s += _digits[i].ToString();
            }
            return s + ")";
        }
        internal static void Set(Digits a, int aN, Digits b, int bN) {
            b._Set(a, aN);
            (b + aN)._SetAll(0, bN - aN);
        }
        internal static Digit GetBit(Digits a, int i) {
            return a[i / Digit.BitN] >> i % Digit.BitN & 1;
        }
        internal static void SetBit(Digits a, int i, uint bit) {
            int j = i / Digit.BitN, k = i % Digit.BitN;
            a[j] = a[j] & ~((1U & ~bit) << k) | (1U & bit) << k;
        }
        internal static int Compare(Digits a, Digit ivalue, int aN) {
            return Compare(a, aN, new Digits(new Digit[] { ivalue }), 1);
        }
        internal static int SigDigitN(Digits a, int aN) {
            int i = aN;
            while (i != 0 && a[i - 1] == 0) {
                i--;
            }
            return i;
        }
        internal static int SigBitN(Digits a, int aN) {
            int sigDigitN = SigDigitN(a, aN);
            if (sigDigitN == 0) {
                Debug.Assert(false, "untested code");
                return 0;
            }
            return (int)((sigDigitN - 1) * Digit.BitN
                       + Digit.SigBitN(a[sigDigitN - 1]));
        }
        internal static Digit
        Accumulate(Digits a, Digit mult, Digits b, int n) {
            Digit carry = 0;
            for (int i = 0; i != n; i++) {
                UInt64 dtemp = (UInt64)mult * a[i] + b[i] + carry;
                b[i] = Digit2.Lo(dtemp);
                carry = Digit2.Hi(dtemp);
            }
            return carry;
        }
        internal static Digit
        Decumulate(Digits a, Digit mult, Digits b, int n) {
            Digit borrow = 0;
            for (int i = 0; i != n; i++) {
                UInt64 dtemp;
                unchecked {
                    dtemp = (UInt64)b[i] - borrow - (UInt64)mult * a[i];
                }
                b[i] = Digit2.Lo(dtemp);
                unchecked { borrow = 0 - Digit2.Hi(dtemp); }
            }
            return borrow;
        }
        internal static void Shift(Digits a, int shiftBitN, Digits b, int n) {
            int itranslate = shiftBitN >= 0
                           ? shiftBitN / Digit.BitN
                           : -(-shiftBitN / Digit.BitN);
            ShiftLost(a, shiftBitN - Digit.BitN * itranslate, b, n);
            if (itranslate < 0) {
                Debug.Assert(false, "untested code");
                int dtranslate = -itranslate;
                for (int i = 0; i != n; i++) {
                    Debug.Assert(false, "untested code");
                    b[i] = i + dtranslate < n ? b[i + dtranslate] : 0;
                }
            }
            else if (itranslate > 0) {
                Debug.Assert(false, "untested code");
                int dtranslate = itranslate;
                for (int i = n; i-- != 0;) {
                    Debug.Assert(false, "untested code");
                    b[i] = i >= dtranslate ? b[i - dtranslate] : 0;
                }
            }
        }
        internal static Digit
        ShiftLost(Digits a, int bitScale, Digits b, int n) {
            if (n == 0) {
                Debug.Assert(false, "untested code"); return 0;
            }
            if (bitScale == 0) {
                Debug.Assert(false, "untested code");
                b._Set(a, n);
                return 0;
            }
            Digit bitNLost = 0;
            if (bitScale > 0) {
                if (bitScale > Digit.BitN) {
                    throw new ArgumentException();
                }
                if (bitScale == Digit.BitN) {
                    bitNLost = a[n - 1];
                    for (int i = n - 1; i != 0; i--) {
                        b[i] = a[i - 1];
                    }
                    b[0] = 0;
                }
                else {
                    for (int i = 0; i != n; i++) {
                        Digit bNew = a[i] << bitScale | bitNLost;
                        bitNLost = a[i] >> Digit.BitN - bitScale;
                        b[i] = bNew;
                    }
                }
            }
            else {
                if (bitScale < - Digit.BitN) {
                    throw new ArgumentException();
                }
                if (bitScale == -Digit.BitN) {
                    bitNLost = a[0];
                    for (int i = 1; i != n; i++) {
                        b[i - 1] = a[i];
                    }
                    b[n - 1] = 0;
                }
                else {
                    for (int i = n; i-- != 0;) {
                        Digit bNew = a[i] >> -bitScale | bitNLost;
                        bitNLost = a[i] << Digit.BitN + bitScale;
                        b[i] = bNew;
                    }
                    bitNLost >>= Digit.BitN + bitScale;
                }
            }
            return bitNLost;
        }
        internal static void
        Mul(Digits a, int aN, Digits b, int bN, Digits c) {
            Debug.Assert(!c._Overlaps(a) && !c._Overlaps(b)
                       , "overlapping arguments");
            Digits p1, p2;
            int i, n1, n2;
            if (aN > bN) {
                p1 = a;
                p2 = b;
                n1 = aN;
                n2 = bN;
            }
            else {
                p2 = a;
                p1 = b;
                n2 = aN;
                n1 = bN;
            }
            if (n2 == 0) {
                Debug.Assert(false, "untested code");
                c._SetAll(0, n1);
                return;
            }
            c[n1] = Mul(p1, p2[0], c, n1);
            for (i = 1; i != n2; i++) {
                c[i + n1] = Accumulate(p1, p2[i], c + i, n1);
            }
        }
        internal static Digit Mul(Digits a, Digit mult, Digits b, int n) {
            Digit carry = 0;
            for (int i = 0; i != n; i++) {
                UInt64 dtemp = (UInt64)mult * a[i] + carry;
                b[i] = Digit2.Lo(dtemp);
                carry = Digit2.Hi(dtemp);
            }
            return carry;
        }
        internal static void
        BytesToDigits(byte[] bytes, int bytesI, Digits digits, int bitN) {
            if (bitN == 0) {
                Debug.Assert(false, "untested code"); return;
            }
            int digitN = (bitN + (Digit.BitN - 1)) / Digit.BitN;
            digits._SetAll(0, digitN);
            for (int iDigit = 0; iDigit != digitN; iDigit++) {
                int byteNLeft = (bitN + 7) / 8 - 4 * iDigit;
                Digit digit = 0;
                for (
                    int iByte = 0;
                    iByte != (4 > byteNLeft ? byteNLeft : 4);
                    iByte++
                ) {
                    digit
                 ^= (Digit)bytes[bytesI + byteNLeft - 1 - iByte] << 8 * iByte;
                }
                digits[iDigit] = digit;
            }
            digits[digitN - 1] &= Digit.MaxValue >> Digit.BitN * digitN - bitN;
        }
        internal static void
        DigitsToBytes(Digits digits, byte[] bytes, int byteI, int bitN) {
            for (int i = 0; i != (bitN + (Digit.BitN - 1)) / Digit.BitN; i++) {
                Digit dvalue = digits[i];
                int byteNLeft = (bitN + 7) / 8 - 4 * i;
                for (int j = 0; j != (byteNLeft > 4 ? 4 : byteNLeft); j++) {
                    bytes[byteI + byteNLeft - 1 - j] = (byte)(dvalue & 0xff);
                    dvalue >>= 8;
                }
            }
        }
        internal static void Div(
            Digits num
          , int numN
          , Digits denom
          , int denomN
          , Reciprocal recip
          , Digits q
          , Digits r
        ) {
            if (denomN == 0) {
                throw new DivideByZeroException();
            }
            if (num == null || denom == null || r == null) {
                throw new ArgumentNullException();
            }
            Debug.Assert(!r._Overlaps(num) && !r._Overlaps(denom)
                       , "overlapping arguments");
            if (q != null) {
                Debug.Assert(
                    !q._Overlaps(num) && !q._Overlaps(denom) && !r._Overlaps(q)
                  , "overlapping arguments"
                );
            }
            Digit dlead = denom[denomN - 1];
            if (dlead == 0) {
                throw new ArgumentException();
            }
            if (numN < denomN) {
                Debug.Assert(false, "untested code");
                Set(num, numN, r, denomN);
                return;
            }
            if (denomN == 1) {
                Div(num, dlead, recip, q, numN, r); return;
            }
            if (recip == null) {
                recip = new Reciprocal();
                DivPrecondition(denom, denomN, recip);
            }
            r[denomN - 1] = 0;
            r._Set(num + (numN - denomN + 1), denomN - 1);
            for (int iq = numN - denomN + 1; iq-- != 0;) {
                Digit rTop = r[denomN - 1];
                for (int i = denomN - 1; i != 0; i--) {
                    r[i] = r[i - 1];
                }
                r[0] = num[iq];
                Digit qest;
                if (rTop == 0 && Compare(r, denom, denomN) < 0) {
                    qest = 0;
                }
                else {
                    qest
                  = recip.EstQuotient(rTop, r[denomN - 1], r[denomN - 2]);
                    if (qest < Digit.MaxValue) {
                        qest += 1;
                    }
                    Digit borrow = Decumulate(denom, qest, r, denomN);
                    if (borrow > rTop) {
                        qest -= 1;
                        borrow -= Add(r, denom, r, denomN);
                    }
                    Debug.Assert(borrow == rTop, "internal error");
                }
                if (q != null) {
                    q[iq] = qest;
                }
            }
        }
        static void Div(
            Digits numer
          , Digit den
          , Reciprocal recip
          , Digits q
          , int n
          , Digits r
        ) {
            Digit carry = 0;
            int nLeft = n;
            if (nLeft > 0 && numer[nLeft - 1] < den) {
                nLeft--;
                carry = numer[nLeft];
                if (q != null) {
                    q[nLeft] = 0;
                }
            }
            if (recip == null && nLeft < 2) {
                for (int i = nLeft; i-- != 0;) {
                    Digit qest = 0;
                    Digit2.Div((UInt64)carry << Digit.BitN | numer[i]
                             , den
                             , out qest
                             , out carry);
                    if (q != null) {
                        q[i] = qest;
                    }
                }
            }
            else {
                if (recip == null) {
                    recip = new Reciprocal();
                    DivPrecondition(new Digits(new Digit[] { den }), 1, recip);
                }
                for (int i = nLeft; i-- != 0;) {
                    Digit qest = 0;
                    Digit2.Div((UInt64)carry << Digit.BitN | numer[i]
                             , den
                             , recip
                             , out qest
                             , out carry);
                    if (q != null) {
                        q[i] = qest;
                    }
                }
            }
            r[0] = carry;
        }
        internal static void
        DivPrecondition(Digits denom, int denomN, Reciprocal recip) {
            if (denom == null) {
                throw new ArgumentNullException();
            }
            if (denomN == 0 || denom[denomN - 1] == 0) {
                throw new ArgumentException();
            }
            int recipBitShift = Digit.BitN - Digit.SigBitN(denom[denomN - 1]);
            Digit dlead2 = denom[denomN - 1]
                , dlead1 = denomN >= 2 ? denom[denomN - 2] : 0
                , dlead0 = denomN >= 3 ? denom[denomN - 3] : 0
                , dShiftHi = dlead2 << recipBitShift
                           | dlead1 >> 1 >> Digit.BitN - 1 - recipBitShift
                , dShiftLo = dlead1 << recipBitShift
                           | dlead0 >> 1 >> Digit.BitN - 1 - recipBitShift;
            Digit recipMpy, r;
            Digit2.Div((UInt64)(Digit.MaxValue - dShiftHi) << Digit.BitN
                     | Digit.MaxValue - dShiftLo
                     , dShiftHi
                     , out recipMpy
                     , out r);
            if (Digit2.Hi((UInt64)recipMpy * dShiftLo) > r) {
                recipMpy -= 1;
            }
            r = (Digit.MaxValue >> recipBitShift) - denom[denomN - 1];
            for (int id = denomN; id-- != 0 && r < recipMpy;) {
                UInt64 test1 = (UInt64)r << Digit.BitN
                             | Digit.MaxValue - (id > 0 ? denom[id - 1] : 0)
                     , test2 = (UInt64)recipMpy * denom[id];
                if (test2 > test1) {
                    recipMpy -= 1; break;
                }
                test1 = test1 - test2;
                r = Digit2.Lo(test1);
                if (Digit2.Hi(test1) != 0) {
                    break;
                }
            }
            recip._shiftBitN = recipBitShift;
            recip._multiplier = recipMpy;
        }
        static uint Add(Digits a, int aN, Digits b, int bN, Digits c) {
            if (aN < bN || aN < 0 || bN < 0) {
                throw new ArgumentException();
            }
            uint carry = Add(a, b, c, bN);
            return Add(a + bN, carry, c + bN, aN - bN);
        }
        static void
        AddFull(Digits a, int aN, Digits b, int bN, Digits c, out int cN) {
            uint carry;
            if (aN < bN) {
                Debug.Assert(false, "untested code");
                carry = Add(b, bN, a, aN, c);
                cN = bN;
            }
            else {
                carry = Add(a, aN, b, bN, c);
                cN = aN;
            }
            if (carry != 0) {
                Debug.Assert(false, "untested code");
                c[cN++] = carry;
            }
        }
        internal static uint Add(Digits a, Digit immediate, Digits b, int n) {
            uint carry = immediate;
            for (int i = 0; i != n; i++) {
                Digit bi = a[i] + carry;
                b[i] = bi;
                if (bi >= carry) {
                    if (a != b) {
                        (b + i + 1)._Set(a + i + 1, n - i - 1);
                    }
                    return 0;
                }
                carry = 1;
            }
            return carry;
        }
        internal static uint Add(Digits a, Digits b, Digits c, int n) {
            uint carry = 0;
            for (int i = 0; i != n; i++) {
                Digit ai = a[i], bi = b[i], sum = unchecked(carry + (ai + bi));
                c[i] = sum;
                carry = ((ai | bi) ^ (ai ^ bi) & sum) >> Digit.BitN - 1;
            }
            return carry;
        }
        internal static int
        AddSub(Digits a, Digits b, Digits c, Digits d, int n) {
            uint carry1 = 0, carry2 = 0;
            for (int i = 0; i != n; i++) {
                Digit ai = a[i]
                    , bi = b[i]
                    , ci = c[i]
                    , sum1 = unchecked(ai + bi + carry1)
                    , sum2 = unchecked(sum1 - ci - carry2);
                d[i] = sum2;
                carry1 = (sum1 ^ (sum1 ^ ai | sum1 ^ bi)) >> Digit.BitN - 1;
                carry2 = (sum1 ^ (sum1 ^ ci | sum1 ^ sum2)) >> Digit.BitN - 1;
            }
            return (int)carry1 - (int)carry2;
        }
        internal static int Compare(Digits a, int aN, Digits b, int bN) {
            int la = aN, lb = bN;
            while (la > lb) {
                if (a[la - 1] != 0) { return + 1; } la--;
            }
            while (lb > la) {
                if (b[lb - 1] != 0) { return -1; } lb--;
            }
            Debug.Assert(la == lb, "internal error");
            while (la != 0) {
                if (a[la - 1] != b[la - 1]) {
                    return a[la - 1] > b[la - 1] ? +1 : -1;
                }
                la--;
            }
            return 0;
        }
        internal static int Compare(Digits a, Digits b, int n) {
            for (int i = n; i-- != 0;) {
                if (a[i] != b[i]) {
                    return a[i] > b[i] ? + 1 : - 1;
                }
            }
            return 0;
        }
        internal static int CompareSum(Digits a, Digits b, Digits c, int n) {
            int sumPrev = 0;
            for (int i = n; i-- != 0;) {
                Digit aval = a[i]
                    , bval = b[i]
                    , cval = c[i]
                    , sumNow = unchecked(aval + bval);
                Debug.Assert(sumPrev == 0 || sumPrev == -1, "internal error");
                sumPrev += (sumNow < aval ? 1 : 0) - (sumNow < cval ? 1 : 0);
                unchecked { sumNow -= cval; }
                if (
                    sumPrev != unchecked((int)(uint)sumNow)
                 || unchecked(sumPrev + 3 & 2) == 0
                ) {
                    return (sumPrev + 2 & 2) - 1;
                }
            }
            return sumPrev;
        }
        internal static int Sub(Digits a, Digit isub, Digits b, int n) {
            Digit borrow = isub;
            for (int i = 0; i != n; i++) {
                Digit ai = a[i];
                b[i] = ai - borrow;
                if (ai >= borrow) {
                    if (a != b) {
                        (b + i + 1)._Set(a + i + 1, n - i - 1);
                    }
                    return 0;
                }
                borrow = 1;
            }
            return (int)borrow;
        }
        internal static uint Sub(Digits a, Digits b, Digits c, int n) {
            uint borrow = 0;
            for (int i = 0; i != n; i++) {
                Digit ai = a[i], bi = b[i], sum = unchecked(ai - bi - borrow);
                c[i] = sum;
                borrow = (ai ^ (ai ^ bi | ai ^ sum)) >> Digit.BitN - 1;
            }
            return borrow;
        }
        internal static void ExtendedGcd(
            Digits a
          , int aN
          , Digits b
          , int bN
          , Digits ainvmodb
          , Digits binvmoda
          , Digits gcd
          , out int lgcd
        ) {
            Debug.Assert(!gcd._Overlaps(a)
                      && !gcd._Overlaps(b)
                      && !ainvmodb._Overlaps(a)
                      && !ainvmodb._Overlaps(b)
                      && !ainvmodb._Overlaps(gcd)
                       , "overlapping arguments");
            int aSigDigitN = SigDigitN(a, aN), bSigDigitN = SigDigitN(b, bN);
            if (aSigDigitN == 0 || bSigDigitN == 0) {
                throw new ArgumentException();
            }
            int[] abN = new int[2] { aSigDigitN, bSigDigitN };
            if (a == null || b == null || gcd == null || ainvmodb == null) {
                throw new ArgumentNullException();
            }
            int maxDigitN = aN > bN ? aN : bN;
            Digits ab0Padded = new Digits(maxDigitN + 2)
                 , ab1Padded = new Digits(maxDigitN + 2)
                 , tempProd = new Digits(2 * maxDigitN)
                 , tempQ = new Digits(maxDigitN + 1);
            Digits[] ab = new Digits[] { ab0Padded + 1, ab1Padded + 1 };
            ab[0]._Set(a, aSigDigitN);
            ab[1]._Set(b, bSigDigitN);
            Digits[]
                tempsMul
              = new Digits[] { new Digits(maxDigitN), new Digits(maxDigitN) };
            tempsMul[0][0] = 1;
            int mulN = 1, iterations = 0;
            while (abN[0] != 0 && abN[1] != 0) {
                int abN0 = abN[0], abN1 = abN[1];
                Digits pab0top = ab[0] + (abN0 - 1)
                     , pab1top = ab[1] + (abN1 - 1);
                Digit topword0 = pab0top[0], topword1 = pab1top[0];
                int topsigbitN0 = Digit.SigBitN(topword0)
                  , topsigbitN1 = Digit.SigBitN(topword1)
                  , sigbitN0 = Digit.BitN * (abN0 - 1) + topsigbitN0
                  , sigbitN1 = Digit.BitN * (abN1 - 1) + topsigbitN1
                  , maxSigBitN = sigbitN0 > sigbitN1 ? sigbitN0 : sigbitN1
                  , maxlab = abN0 > abN1 ? abN0 : abN1
                  , ibig = Compare(ab[1], abN1, ab[0], abN0) > 0 ? 1 : 0
                  , ismall = 1 - ibig;
                Digit[] mat22 = new Digit[4];
                iterations++;
                Debug.Assert(iterations <= Digit.BitN * (aN + bN + 1)
                           , "too many iterations");
                if (maxlab == 1) {
                    Digit ab0, ab1, m00, m01, m10, m11;
                    if (topword0 > Digit.MaxValue - topword1) {
                        if (ibig == 0) {
                            topword0 -= topword1;
                        }
                        else {
                            topword1 -= topword0;
                        }
                        Digit carry = Add(tempsMul[0]
                                        , tempsMul[1]
                                        , tempsMul[ibig]
                                        , mulN);
                        if (carry != 0) {
                            Debug.Assert(false, "untested code");
                            Debug.Assert(mulN < bN, "internal error");
                            tempsMul[ibig][mulN] = carry;
                            mulN++;
                        }
                    }
                    ab0 = topword0;
                    ab1 = topword1;
                    m00 = 1;
                    m01 = 0;
                    m10 = 0;
                    m11 = 1;
                    while (ab1 != 0) {
                        if (ab0 >= ab1) {
                            if (ab0 >> 2 >= ab1) {
                                Digit q = ab0 / ab1;
                                ab0 -= q * ab1;
                                m00 += q * m10;
                                m01 += q * m11;
                            }
                            else {
                                do {
                                    ab0 -= ab1;
                                    m00 += m10;
                                    m01 += m11;
                                } while (ab0 >= ab1);
                            }
                        }
                        Debug.Assert(ab1 > ab0, "internal error");
                        if (ab0 == 0) {
                            break;
                        }
                        if (ab1 >> 2 >= ab0) {
                            Digit q = ab1 / ab0;
                            ab1 -= q * ab0;
                            m10 += q * m00;
                            m11 += q * m01;
                        }
                        else {
                            do {
                                ab1 -= ab0;
                                m10 += m00;
                                m11 += m01;
                            } while (ab1 >= ab0);
                        }
                        Debug.Assert(ab0 > ab1, "internal error");
                    }
                    ab[0][0] = ab0;
                    ab[1][0] = ab1;
                    abN[0] = ab0 != 0 ? 1 : 0;
                    abN[1] = ab1 != 0 ? 1 : 0;
                    mat22[0] = m00;
                    mat22[1] = m01;
                    mat22[2] = m10;
                    mat22[3] = m11;
                    Digits carrys = new Digits(2);
                    Mul22U(mat22, tempsMul[0], tempsMul[1], mulN, carrys);
                    if (carrys[0] == 0 && carrys[1] == 0) {
                    }
                    else {
                        Debug.Assert(mulN < bN, "internal error");
                        tempsMul[0][mulN] = carrys[0];
                        tempsMul[1][mulN] = carrys[1];
                        mulN++;
                    }
                }
                else if (
                    sigbitN0 > sigbitN1 + Digit.BitN / 2
                 || sigbitN1 > sigbitN0 + Digit.BitN / 2
                ) {
                    int smallMulN = SigDigitN(tempsMul[ismall], mulN);
                    Div(ab[ibig]
                      , abN[ibig]
                      , ab[ismall]
                      , abN[ismall]
                      , null
                      , tempQ
                      , tempProd);
                    int lQ = SigDigitN(tempQ, abN[ibig] - abN[ismall] + 1);
                    abN[ibig] = SigDigitN(tempProd, abN[ismall]);
                    ab[ibig]._Set(tempProd, abN[ibig]);
                    Mul(tempQ, lQ, tempsMul[ismall], smallMulN, tempProd);
                    AddFull(tempProd
                          , SigDigitN(tempProd, lQ + smallMulN)
                          , tempsMul[ibig]
                          , mulN
                          , tempsMul[ibig]
                          , out mulN);
                }
                else {
                    int norm = (int)(Digit.BitN * maxlab - maxSigBitN);
                    pab0top[1] = pab1top[1] = 0;
                    Debug.Assert(maxlab >= 2, "internal error");
                    UInt64 lead0
                         = (UInt64)
                           (ab[0][maxlab - 1] << norm
                          | ab[0][maxlab - 2] >> 1 >> Digit.BitN - 1 - norm)
                        << Digit.BitN
                         | (ab[0][maxlab - 2] << norm
                          | ab[0][maxlab - 3] >> 1 >> Digit.BitN - 1 - norm)
                         , lead1
                         = (UInt64)
                           (ab[1][maxlab - 1] << norm
                          | ab[1][maxlab - 2] >> 1 >> Digit.BitN - 1 - norm)
                        << Digit.BitN
                         | (ab[1][maxlab - 2] << norm
                          | ab[1][maxlab - 3] >> 1 >> Digit.BitN - 1 - norm);
                    LehmerMat22(lead0, lead1, mat22);
                    if ((mat22[1] | mat22[2]) == 0) {
                        Debug.Assert(false, "untested code");
                        Debug.Assert(
                            mat22[0] == 1 && mat22[3] == 1, "internal error");
                        mat22[ibig + 1] = 1;
                    }
                    int lab = abN0 > abN1 ? abN0 : abN1;
                    int[] scarrys = new int[2];
                    Mul22S(mat22, ab[0], ab[1], lab, scarrys);
                    Debug.Assert(scarrys[0] == 0 && scarrys[1] == 0
                               , "internal error");
                    int abN0Sig = lab, abN1Sig = lab;
                    while (abN0Sig != 0 && ab[0][abN0Sig - 1] == 0) {
                        abN0Sig--;
                    }
                    while (abN1Sig != 0 && ab[1][abN1Sig - 1] == 0) {
                        abN1Sig--;
                    }
                    abN[0] = abN0Sig;
                    abN[1] = abN1Sig;
                    Digits carrys = new Digits(2);
                    Mul22U(mat22, tempsMul[0], tempsMul[1], mulN, carrys);
                    if (carrys[0] == 0 && carrys[1] == 0) {
                    }
                    else {
                        Debug.Assert(mulN < bN, "internal error");
                        tempsMul[0][mulN] = carrys[0];
                        tempsMul[1][mulN] = carrys[1];
                        mulN++;
                    }
                }
            }
            Digit igcd = (Digit)(abN[0] == 0 ? 1U : 0U);
            lgcd = abN[igcd];
            gcd._Set(ab[igcd], lgcd);
            Debug.Assert(Compare(b, tempsMul[1 - igcd], bN) >= 0
                      && Compare(tempsMul[1 - igcd], tempsMul[igcd], bN) >= 0
                       , "internal error");
            if (igcd == 0) {
                ainvmodb._Set(tempsMul[0], bN);
            }
            else {
                Sub(tempsMul[0], tempsMul[1], ainvmodb, bN);
            }
            if (binvmoda != null) {
                Sub(tempsMul[1 - igcd], ainvmodb, tempsMul[1 - igcd], bN);
                Mul(a, aN, tempsMul[1 - igcd], bN, tempProd);
                Add(tempProd, aN + bN, gcd, lgcd, tempProd);
                Div(tempProd
                  , aN + bSigDigitN
                  , b
                  , bSigDigitN
                  , null
                  , tempQ
                  , tempsMul[1 - igcd]);
                Debug.Assert(SigDigitN(tempsMul[1 - igcd], bSigDigitN) == 0
                           , "internal error");
                binvmoda._Set(tempQ, aN);
            }
        }
        static void
        LehmerMat22(UInt64 lead0orig, UInt64 lead1orig, Digit[] mat22) {
            Digit lead0h = Digit2.Hi(lead0orig)
                , lead0l = Digit2.Lo(lead0orig)
                , lead1h = Digit2.Hi(lead1orig)
                , lead1l = Digit2.Lo(lead1orig);
            bool progress = true;
            Digit m00 = 1, m01 = 0, m10 = 0, m11 = 1;
            Debug.Assert(lead0h != 0
                      && lead1h != 0
                      && ((lead0h | lead1h) & 1U << Digit.BitN - 1) != 0
                       , "internal error");
            while (progress) {
                progress = false;
                if (lead0h - 1 > lead1h && lead0h != 0) {
                    if (lead0h >> 2 >= lead1h + 2) {
                        Digit q = lead0h / (lead1h + 2);
                        UInt64 prod10By11 = (UInt64)q * (m10 + m11)
                             , prod1l = (UInt64)q * lead1l;
                        Debug.Assert(q > 3, "internal error");
                        if (
                            Digit2.Hi(prod10By11) == 0
                         && Digit2.Lo(prod10By11)
                         <= Digit.MaxValue / 2 - m00 - m01
                        ) {
                            Digit prod10 = q * m10;
                            progress = true;
                            lead0h
                         -= (Digit)((long)(UInt32)q * lead1h
                                  + Digit2.Hi(prod1l)
                                  + (Digit2.Lo(prod1l) > lead0l ? 1L : 0L));
                            unchecked { lead0l -= Digit2.Lo(prod1l); }
                            m00 += prod10;
                            m01 += Digit2.Lo(prod10By11) - prod10;
                            Debug.Assert((m00 | m01) < 1U << Digit.BitN - 1
                                       , "internal error");
                        }
                    }
                    else {
                        Digit overflowTest;
                        do {
                            m00 += m10;
                            m01 += m11;
                            overflowTest = (m00 | m01) & 1U << Digit.BitN - 1;
                            lead0h -= lead1h + (lead1l > lead0l ? 1U : 0U);
                            unchecked { lead0l -= lead1l; }
                        } while (overflowTest == 0 && lead0h >= lead1h + 2);
                        progress = true;
                        if (overflowTest != 0) {
                            progress = false;
                            m00 -= m10;
                            m01 -= m11;
                        }
                    }
                }
                if (lead1h - 1 > lead0h && lead1h != 0) {
                    if (lead1h >> 2 >= lead0h + 2) {
                        Digit q = lead1h / (lead0h + 2);
                        UInt64 prod00And01 = (UInt64)q * (m00 + m01)
                             , prod0l = (UInt64)q * lead0l;
                        Debug.Assert(q > 3, "internal error");
                        if (
                            Digit2.Hi(prod00And01) == 0
                         && Digit2.Lo(prod00And01)
                         <= Digit.MaxValue / 2 - m10 - m11
                        ) {
                            Digit prod00 = q * m00;
                            progress = true;
                            lead1h -= q * lead0h
                                    + Digit2.Hi(prod0l)
                                    + (Digit2.Lo(prod0l) > lead1l ? 1U : 0U);
                            unchecked { lead1l -= Digit2.Lo(prod0l); }
                            m10 += prod00;
                            m11 += Digit2.Lo(prod00And01) - prod00;
                            Debug.Assert((m10 | m11) < 1U << Digit.BitN - 1
                                       , "internal error");
                        }
                    }
                    else {
                        Digit overflowTest;
                        do {
                            m10 += m00;
                            m11 += m01;
                            overflowTest = (m10 | m11) & 1U << Digit.BitN - 1;
                            lead1h -= lead0h + (lead0l > lead1l ? 1U : 0U);
                            unchecked { lead1l -= lead0l; }
                        } while (overflowTest == 0 && lead1h >= lead0h + 2);
                        progress = true;
                        if (overflowTest != 0) {
                            progress = false;
                            m10 -= m00;
                            m11 -= m01;
                        }
                    }
                }
            }
            Debug.Assert(((m00 | m01 | m10 | m11) & 1U << Digit.BitN - 1) == 0
                       , "internal error");
            mat22[0] = m00;
            mat22[1] = m01;
            mat22[2] = m10;
            mat22[3] = m11;
        }
        static void Mul22U(
            Digit[] mat
          , Digits vec1
          , Digits vec2
          , int lvec
          , Digits carrys
        ) {
            Digit carry1 = 0, carry2 = 0;
            Digit m11 = mat[0], m12 = mat[1], m21 = mat[2], m22 = mat[3];
            if (m12 > Digit.MaxValue - m11 || m21 > Digit.MaxValue - m22) {
                throw new ArgumentException();
            }
            for (int i = 0; i != lvec; i++) {
                UInt64 prod11 = (UInt64)m11 * vec1[i] + carry1
                     , prod21 = (UInt64)m21 * vec1[i] + carry2
                     , prod12 = (UInt64)m12 * vec2[i] + Digit2.Lo(prod11)
                     , prod22 = (UInt64)m22 * vec2[i] + Digit2.Lo(prod21);
                vec1[i] = Digit2.Lo(prod12);
                vec2[i] = Digit2.Lo(prod22);
                carry1 = Digit2.Hi(prod11) + Digit2.Hi(prod12);
                carry2 = Digit2.Hi(prod21) + Digit2.Hi(prod22);
            }
            carrys[0] = carry1;
            carrys[1] = carry2;
        }
        static void
        Mul22S(Digit[] mat, Digits vec1, Digits vec2, int lvec, int[] carrys) {
            int carry1 = 0, carry2 = 0;
            Digit m11 = mat[0], m12 = mat[1], m21 = mat[2], m22 = mat[3];
            if (((m11 | m12 | m21 | m22) & 1U << Digit.BitN - 1) != 0) {
                throw new ArgumentException();
            }
            for (int i = 0; i != lvec; i++) {
                UInt64 prod11 = (UInt64)m11 * vec1[i]
                     , prod12 = (UInt64)m12 * vec2[i]
                     , prod21 = (UInt64)m21 * vec1[i]
                     , prod22 = (UInt64)m22 * vec2[i]
                     , prod1 = unchecked(prod11 + (UInt64)carry1)
                     , prod2 = unchecked(prod22 + (UInt64)carry2);
                prod1 = unchecked(prod1 - prod12);
                prod2 = unchecked(prod2 - prod21);
                vec1[i] = Digit2.Lo(prod1);
                vec2[i] = Digit2.Lo(prod2);
                carry1 = unchecked((int)Digit2.Hi(prod1));
                carry2 = unchecked((int)Digit2.Hi(prod2));
            }
            carrys[0] = carry1;
            carrys[1] = carry2;
        }
        internal static void
        Random(Digits digits, int digitN, Random generator) {
            for (int i = 0; i < digitN; i++) {
                digits[i] = Digit.Random(generator);
            }
        }
    }
    public class Reciprocal {
        internal Digit _multiplier;
        internal int _shiftBitN;
        internal Digit EstQuotient(Digit n2, Digit n1, Digit n0) {
            Digit nShiftHi
                = n2 << _shiftBitN | n1 >> 1 >> Digit.BitN - 1 - _shiftBitN
                , nShiftLo
                = n1 << _shiftBitN | n0 >> 1 >> Digit.BitN - 1 - _shiftBitN;
            UInt64 qprod = ((UInt64)nShiftHi << Digit.BitN | nShiftLo)
                         + (UInt64)nShiftHi * _multiplier;
            if ((nShiftLo & 1U << Digit.BitN - 1) != 0) {
                qprod += _multiplier >> 1;
            }
            return Digit2.Hi(qprod);
        }
    }
}
