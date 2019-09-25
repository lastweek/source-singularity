// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    class Prime
    {
        const uint _RabinTestN = 50;
        const uint _IterationsAllowed = 5000;
        internal static Digits NewPrime(int pBitN, Random generator) {
            if (pBitN < Digit.BitN) {
                throw new ArgumentException();
            }
            int pDigitN = (pBitN + (Digit.BitN - 1)) / Digit.BitN;
            Digits p = new Digits(pDigitN);
            while (true) {
                for (
                    int iteration = 0;
                    iteration < _IterationsAllowed;
                    iteration++
                ) {
                    Digits.Random(p, pDigitN, generator);
                    p[pDigitN - 1] >>= Digit.BitN * pDigitN - pBitN;
                    p[0] |= 1;
                    Digits.SetBit(p, pBitN - 1, 1);
                    Digits.SetBit(p, pBitN - 2, 1);
                    if (DivisibleBySomeLowPrime(p, pDigitN)) {
                        continue;
                    }
                    Modulus modulus = new Modulus(p, pDigitN, true);
                    Digits minus1 = new Digits(pDigitN);
                    Modular
                   .Neg(modulus._one, minus1, modulus._mod, modulus._digitN);
                    Digits exp = new Digits(pDigitN);
                    Digits.Shift(p, -1, exp, pDigitN);
                    Digits @base = new Digits(pDigitN);
                    for (int i = 1; i <= _RabinTestN; i++) {
                        if (i == 1) {
                            Modular.Add(modulus._one
                                      , modulus._one
                                      , @base
                                      , modulus._mod
                                      , modulus._digitN);
                        }
                        else {
                            Modular.NonZeroRandom(
                                p, @base, pDigitN, generator);
                        }
                        Digits result = new Digits(pDigitN);
                        modulus._Exp(@base, exp, pDigitN, result);
                        if (Digits.Compare(result, minus1, pDigitN) == 0) {
                            return p;
                        }
                        if (
                            Digits.Compare(result, modulus._one, pDigitN) != 0
                        ) {
                            break;
                        }
                    }
                }
                Debug.Assert(false, "too many iterations");
            }
        }
        static Digit[]
            LowPrimesProduct
          = new Digit[] {
                4240068105U, 3842999413U, 3059475739U, 4294251953U, 4294770617U
              , 4294737533U, 4293835597U, 4294901213U, 4294933861U, 1353041857U
              , 4148193053U, 4286755457U, 4291682933U, 4294875479U
              , 4294914791U, 4294097393U, 4289642801U, 4280410741U
              , 4294824337U, 4294927237U, 4294924747U, 4294928843U
            };
        internal static bool DivisibleBySomeLowPrime(Digits digits, int n) {
            if (n == 0 || (digits[0] & 1) == 0) {
                Debug.Assert(false, "untested code");
                return true;
            }
            for (int l = 0; l != LowPrimesProduct.Length; l++) {
                Digit product = LowPrimesProduct[l]
                    , productInverse = Digit.TwoAdicInverse(product)
                    , r = 0;
                for (int i = 0; i != n; i++) {
                    Digit mulby;
                    unchecked {
                        r += digits[i];
                        if (r < digits[i]) {
                            r -= product;
                        }
                        mulby = productInverse * r;
                        Debug.Assert(mulby * product == r, "internal error");
                    }
                    r = product - Digit2.Hi((UInt64)mulby * product);
                }
                if (Digit.OddGcd(r, product) != 1) {
                    return true;
                }
            }
            return false;
        }
    }
}
