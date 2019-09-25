// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    class Modulus
    {
        internal readonly int _digitN;
        readonly int _scaleBitN;
        readonly bool _fromRight;
        readonly Reciprocal _leftRecip;
        readonly Digit _rightRecip;
        internal readonly Digits _mod;
        readonly Digits _multiplier1;
        readonly Digits _multiplier2;
        internal readonly Digits _one;
        MulAlgorithm _algorithm;
        internal Modulus(Digits mod, int digitN, bool fromRight) {
            if (digitN == 0 || mod[digitN - 1] == 0) {
                throw new ArgumentException();
            }
            _mod = mod;
            _digitN = digitN;
            _fromRight = fromRight;
            _one = new Digits(digitN);
            _multiplier1 = new Digits(digitN);
            _multiplier2 = new Digits(digitN);
            // this.mod.Set(this.mod, _digitN);
            _leftRecip = new Reciprocal();
            Digits.DivPrecondition(mod, digitN, _leftRecip);
            Digit mod0inv = 0;
            if ((mod[0] & 1) != 0) {
                mod0inv = Digit.TwoAdicInverse(mod[0]);
            }
            _rightRecip = mod0inv;
            int digitN2 = (digitN + 1) / 2;
            Digits temp = new Digits(digitN + digitN2);
            if (!fromRight) {
                _algorithm = new MulAlgorithm(_MulFromLeft);
                int dividendN = digitN + digitN2;
                _scaleBitN = 0;
                for (int i = 0; i != dividendN; i++) {
                    temp[i] = Digit.MaxValue;
                }
                temp[dividendN - 1] = Digit.MaxValue >> _leftRecip._shiftBitN;
                Digits q = new Digits(digitN2 + 1);
                Digits r = new Digits(digitN);
                Digits.Div(temp, dividendN, mod, digitN, _leftRecip, q, r);
                Debug.Assert(q[digitN2] == 1, "internal error");
                Digits.Add(r, 1U, r, digitN);
                Digits.Sub(mod, r, r, digitN);
            }
            else {
                _algorithm = new MulAlgorithm(_MulFromRight);
                _scaleBitN = Digit.BitN * digitN;
                if (mod0inv == 0) {
                    throw new ArgumentException();
                }
                _multiplier2[0] = mod0inv;
                temp[digitN] = Digits.Mul(mod, mod0inv, temp, digitN);
                Debug.Assert(temp[0] == 1, "internal error");
                for (int i = 1; i != digitN2; i++) {
                    Digit mul = unchecked(0 - mod0inv * temp[i]);
                    _multiplier2[i] = mul;
                    temp[i + digitN]
                  = Digits.Accumulate(mod, mul, temp + i, digitN);
                    Debug.Assert(temp[i] == 0, "internal error");
                }
                _multiplier1._Set(temp + digitN2, digitN);
            }
            _ToModular(new Digits(new Digit[] { 1 }), 1, _one);
        }
        void _BasePowerSquaring(Digits basepower) {
            _Mul(basepower, basepower, basepower);
        }
        class Temps2000
        {
            internal Modulus _modulus;
            internal Digits[] _bucket = new Digits[1L << 5];
            internal bool[] _bucketBusy = new bool[1L << 5];
        }
        void _BucketMul(UInt32 ibucket, Digits mult, Temps2000 temps) {
            Digits bloc = temps._bucket[ibucket];
            if (temps._bucketBusy[ibucket]) {
                _Mul(bloc, mult, bloc);
            }
            else {
                temps._bucketBusy[ibucket] = true;
                bloc._Set(mult, _digitN);
            }
        }
        internal void
        _Exp(Digits @base, Digits exp, int expDigitN, Digits answer) {
            int expBitNUsed = Digits.SigBitN(exp, expDigitN);
            ushort[] widthCutoffs = new ushort[] { 6, 24, 80, 240, 672 };
            Digits basepower = answer;
            int bucketWidth = 1;
            while (
                bucketWidth < 5 && widthCutoffs[bucketWidth - 1] < expBitNUsed
            ) {
                bucketWidth++;
            }
            Modular.ValidateData(@base, _mod, _digitN);
            UInt32 bucketMask = (1U << bucketWidth) - 1;
            UInt32 maxBucket = bucketMask;
            Digits bucketData = new Digits((int)(_digitN * maxBucket));
            Temps2000 temps = new Temps2000();
            temps._modulus = this;
            temps._bucket[0] = null;
            Modular.Add(_one, _one, bucketData, _mod, _digitN);
            bool base2 = Digits.Compare(@base, bucketData, _digitN) == 0;
            if (base2 && expBitNUsed != 0) {
                int shiftMax
                  = Digit.BitN * _digitN > 1024 ? 1024 : Digit.BitN * _digitN;
                int highExponBitN = 0;
                bool bighBitNProcessed = false;
                Digits temp = bucketData;
                for (int i = expBitNUsed; i-- != 0;) {
                    Digit expBit = Digits.GetBit(exp, i);
                    if (bighBitNProcessed) {
                        _Mul(temp, temp, temp);
                        if (expBit != 0) {
                            Modular.Add(temp, temp, temp, _mod, _digitN);
                        }
                    }
                    else {
                        highExponBitN = (int)(2 * highExponBitN + expBit);
                        if (i == 0 || 2 * highExponBitN >= shiftMax) {
                            bighBitNProcessed = true;
                            _Shift(_one, highExponBitN, temp);
                        }
                    }
                }
                temps._bucket[1] = temp;
                Debug.Assert(bighBitNProcessed, "internal error");
            }
            else {
                UInt32 ibucket;
                for (ibucket = 1; ibucket <= maxBucket; ibucket++) {
                    Digits bloc = bucketData
                                + (int)(_digitN
                                      * (ibucket
                                       - 1
                                       + ((ibucket & 1) == 0 ? maxBucket : 0))
                                      / 2);
                    temps._bucket[ibucket] = bloc;
                    temps._bucketBusy[ibucket] = false;
                    bloc._Set(_one, _digitN);
                }
                basepower._Set(@base, _digitN);
                Digit carried = 0;
                int ndoubling = 0;
                for (int i = 0; i != expBitNUsed; i++) {
                    Digit bitNow = Digits.GetBit(exp, i);
                    Debug.Assert(carried >> bucketWidth + 2 == 0
                               , "internal error");
                    if (bitNow != 0) {
                        while (ndoubling >= bucketWidth + 1) {
                            if ((carried & 1) != 0) {
                                ibucket = carried & bucketMask;
                                carried -= ibucket;
                                temps._modulus
                               ._BucketMul(ibucket, basepower, temps);
                            }
                            temps._modulus._BasePowerSquaring(basepower);
                            carried /= 2;
                            ndoubling--;
                        }
                        carried |= 1U << ndoubling;
                    }
                    ndoubling++;
                }
                while (carried != 0) {
                    bool squareNow = false;
                    if (carried <= maxBucket) {
                        ibucket = carried;
                    }
                    else if ((carried & 1) == 0) {
                        squareNow = true;
                    }
                    else if (carried <= 3 * maxBucket) {
                        ibucket = maxBucket;
                    }
                    else {
                        Debug.Assert(false, "untested code");
                        ibucket = carried & bucketMask;
                    }
                    if (squareNow) {
                        carried /= 2;
                        temps._modulus._BasePowerSquaring(basepower);
                    }
                    else {
                        carried -= ibucket;
                        temps._modulus._BucketMul(ibucket, basepower, temps);
                    }
                }
                for (ibucket = maxBucket; ibucket >= 2; ibucket--) {
                    if (temps._bucketBusy[ibucket]) {
                        bool found = false;
                        UInt32 jbucket, jbucketMax, kbucket;
                        Digits bloci;
                        if ((ibucket & 1) == 0) {
                            jbucketMax = ibucket / 2;
                        }
                        else {
                            jbucketMax = 1;
                        }
                        for (
                            jbucket = ibucket >> 1;
                            jbucket != ibucket && !found;
                            jbucket++
                        ) {
                            if (temps._bucketBusy[jbucket]) {
                                jbucketMax = jbucket;
                                found = temps._bucketBusy[ibucket - jbucket];
                            }
                        }
                        jbucket = jbucketMax;
                        kbucket = ibucket - jbucket;
                        bloci = temps._bucket[ibucket];
                        temps._modulus._BucketMul(jbucket, bloci, temps);
                        temps._modulus._BucketMul(kbucket, bloci, temps);
                    }
                }
            }
            answer._Set(temps._bucket[1], _digitN);
        }
        void _MulFromLeft(Digits a, Digits b, Digits c) {
            Digits product = new Digits(2 * _digitN);
            Digits.Mul(a, _digitN, b, _digitN, product);
            Digits
           .Div(product, 2 * _digitN, _mod, _digitN, _leftRecip, null, c);
        }
        void _MulFromRight(Digits a, Digits b, Digits c) {
            Digit minv = _rightRecip
                , minva0 = unchecked(minv * a[0])
                , mul1 = b[0]
                , mul2 = unchecked(minva0 * mul1)
                , carry1 = Digit2.Hi((UInt64)mul1 * a[0])
                , carry2 = Digit2.Hi((UInt64)mul2 * _mod[0]);
            UInt64 prod1, prod2;
            Debug.Assert(unchecked(mul1 * a[0]) == unchecked(mul2 * _mod[0])
                       , "internal error");
            Digits temp1 = new Digits(_digitN), temp2 = new Digits(_digitN);
            for (int i = 1; i != _digitN; i++) {
                prod1 = (UInt64)mul1 * a[i] + carry1;
                prod2 = (UInt64)mul2 * _mod[i] + carry2;
                temp1[i - 1] = Digit2.Lo(prod1);
                temp2[i - 1] = Digit2.Lo(prod2);
                carry1 = Digit2.Hi(prod1);
                carry2 = Digit2.Hi(prod2);
            }
            temp1[_digitN - 1] = carry1;
            temp2[_digitN - 1] = carry2;
            for (int j = 1; j != _digitN; j++) {
                mul1 = b[j];
                mul2 = unchecked(minva0 * mul1 + minv * (temp1[0] - temp2[0]));
                prod1 = (UInt64)mul1 * a[0] + temp1[0];
                prod2 = (UInt64)mul2 * _mod[0] + temp2[0];
                Debug.Assert(Digit2.Lo(prod1) == Digit2.Lo(prod2)
                           , "internal error");
                carry1 = Digit2.Hi(prod1);
                carry2 = Digit2.Hi(prod2);
                for (int i = 1; i != _digitN; i++) {
                    prod1 = (UInt64)mul1 * a[i] + temp1[i] + carry1;
                    prod2 = (UInt64)mul2 * _mod[i] + temp2[i] + carry2;
                    temp1[i - 1] = Digit2.Lo(prod1);
                    temp2[i - 1] = Digit2.Lo(prod2);
                    carry1 = Digit2.Hi(prod1);
                    carry2 = Digit2.Hi(prod2);
                }
                temp1[_digitN - 1] = carry1;
                temp2[_digitN - 1] = carry2;
            }
            Modular.Sub(temp1, temp2, c, _mod, _digitN);
        }
        internal void _FromModular(Digits a, Digits b) {
            Modular.ValidateData(a, _mod, _digitN);
            _Shift(a, -_scaleBitN, b);
        }
        internal void _Mul(Digits a, Digits b, Digits c) {
            Modular.ValidateData(a, _mod, _digitN);
            if (a != b) {
                Modular.ValidateData(b, _mod, _digitN);
            }
            _algorithm(a, b, c);
        }
        void _Shift(Digits a, int n, Digits b) {
            if (a != b) {
                b._Set(a, _digitN);
            }
            Modular.ValidateData(a, _mod, _digitN);
            if (n < 0 && (_mod[0] & 1) == 0) {
                throw new ArgumentException();
            }
            while (n > 0) {
                int shiftNow = n > Digit.BitN ? Digit.BitN : n;
                Digit carryOut = Digits.ShiftLost(b, shiftNow, b, _digitN)
                    , qest = _leftRecip
                            .EstQuotient(carryOut
                                       , b[_digitN - 1]
                                       , _digitN >= 2 ? b[_digitN - 2] : 0);
                carryOut -= Digits.Decumulate(_mod, qest, b, _digitN);
                if (carryOut != 0 || Digits.Compare(b, _mod, _digitN) >= 0) {
                    carryOut -= Digits.Sub(b, _mod, b, _digitN);
                }
                Debug.Assert(carryOut == 0, "internal error");
                n -= shiftNow;
            }
            while (n < 0) {
                int shiftNow = -n > Digit.BitN ? Digit.BitN : -n;
                Digit mul = unchecked(0 - _rightRecip * b[0])
                          & Digit.MaxValue >> Digit.BitN - shiftNow
                    , carry = Digits.Accumulate(_mod, mul, b, _digitN)
                    , lowBitNLost = Digits.ShiftLost(b, -shiftNow, b, _digitN);
                b[_digitN - 1] |= carry << Digit.BitN - shiftNow;
                Debug.Assert(lowBitNLost == 0, "internal error");
                n += shiftNow;
            }
        }
        internal void _ToModular(Digits a, int aDigitN, Digits b) {
            Digits aR;
            int aRDigitN;
            if (Digits.Compare(a, aDigitN, _mod, _digitN) >= 0) {
                aR = new Digits(_digitN);
                Digits.Div(a, aDigitN, _mod, _digitN, _leftRecip, null, aR);
                aRDigitN = _digitN;
            }
            else {
                aR = a;
                aRDigitN = aDigitN;
            }
            aRDigitN = Digits.SigDigitN(aR, aRDigitN);
            Digits.Set(aR, aRDigitN, b, _digitN);
            _Shift(b, _scaleBitN, b);
        }
        delegate void MulAlgorithm(Digits arg0, Digits arg1, Digits arg2);
    }
}
