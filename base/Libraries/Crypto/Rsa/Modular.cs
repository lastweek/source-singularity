// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    class Modular
    {
        internal static void
        Add(Digits a, Digits b, Digits c, Digits mod, int n) {
            Debug.Assert(n != 0, "internal error");
            Digit alead = a[n - 1], blead = b[n - 1], mlead = mod[n - 1];
            if (alead >= mlead) {
                ValidateData(a, mod, n);
            }
            if (blead >= mlead) {
                ValidateData(b, mod, n);
            }
            int test;
            if (blead > mlead - alead) {
                test = +1;
            }
            else if (mlead - alead - blead > 1) {
                test = -1;
            }
            else {
                test = Digits.CompareSum(a, b, mod, n);
            }
            if (test >= 0) {
                int carry = Digits.AddSub(a, b, mod, c, n);
                Debug.Assert(carry == 0, "internal error");
            }
            else {
                uint carry = Digits.Add(a, b, c, n);
                Debug.Assert(carry == 0, "internal error");
            }
        }
        internal static void Neg(Digits a, Digits b, Digits mod, int n) {
            Digit allZero = 0;
            for (int i = 0; i != n; i++) {
                allZero |= a[i]; b[i] = a[i];
            }
            if (allZero != 0) {
                if (Digits.Sub(mod, b, b, n) != 0) {
                    throw new ArgumentException();
                }
            }
        }
        internal static void
        Sub(Digits a, Digits b, Digits c, Digits mod, int n) {
            Debug.Assert(n > 0, "internal error");
            Digit alead = a[n - 1], blead = b[n - 1], mlead = mod[n - 1];
            int itest;
            if (alead == blead) {
                itest = Digits.Compare(a, b, n - 1);
            }
            else {
                itest = alead < blead ? -1 : +1;
            }
            if (itest < 0) {
                if (blead >= mlead) {
                    ValidateData(b, mod, n);
                }
                int carry = Digits.AddSub(a, mod, b, c, n);
                Debug.Assert(carry == 0, "internal error");
            }
            else {
                if (alead >= mlead) {
                    Debug.Assert(false, "untested code");
                    ValidateData(a, mod, n);
                }
                uint borrow = Digits.Sub(a, b, c, n);
                Debug.Assert(borrow == 0, "internal error");
            }
        }
        internal static void ValidateData(Digits data, Digits mod, int n) {
            if (Digits.Compare(data, mod, n) >= 0) {
                throw new ArgumentException();
            }
        }
        static void Random(Digits mod, Digits arr, int n, Random generator) {
            Debug.Assert(!arr._Overlaps(mod), "overlapping arguments");
            int sigDigitN = n;
            while (sigDigitN > 0 && mod[sigDigitN - 1] == 0) {
                Debug.Assert(false, "untested code");
                arr[sigDigitN - 1] = 0;
                sigDigitN--;
            }
            if (sigDigitN == 0) {
                throw new ArgumentException();
            }
            Digit nlead = mod[sigDigitN - 1];
            int ntry = 0;
            do {
                ntry++;
                Debug.Assert(ntry <= 100, "too many iterations");
                Digits.Random(arr, sigDigitN - 1, generator);
                arr[sigDigitN - 1] = Digit.Random(0, nlead, generator);
            } while (Digits.Compare(arr, mod, sigDigitN) >= 0);
        }
        internal static void
        NonZeroRandom(Digits mod, Digits arr, int n, Random generator) {
            if (Digits.Compare(mod, 1U, n) <= 0) {
                throw new ArgumentException();
            }
            int ntry = 0;
            do {
                ntry++;
                Debug.Assert(ntry <= 100, "too many iterations");
                Random(mod, arr, n, generator);
            } while (Digits.SigDigitN(arr, n) == 0);
        }
    }
}
