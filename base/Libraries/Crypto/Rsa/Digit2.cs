// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    internal class Digit2 {
        internal static Digit Lo(UInt64 x) {
            return unchecked((UInt32)(x & Digit.MaxValue));
        }
        internal static Digit Hi(UInt64 x) {
            Digit hi = unchecked((UInt32)(x >> Digit.BitN));
            return hi;
        }
        internal static void
        Div(UInt64 num, Digit denom, out Digit q, out Digit r) {
            Digit numHi = Hi(num), numLo = Lo(num);
            if (numHi >= denom) {
                throw new ArgumentException();
            }
            q = (Digit)(num / denom);
            r = unchecked(numLo - denom * q);
            Digit rr = unchecked((Digit)(num - denom * q));
            Debug.Assert(rr == r, "internal error");
        }
        internal static void Div(
            UInt64 num
          , Digit denom
          , Reciprocal recip
          , out Digit q
          , out Digit r
        ) {
            Digit numHi = Hi(num)
                , numLo = Lo(num)
                , qEst = Digit.MaxValue - recip.EstQuotient(numHi, numLo, 0);
            UInt64 rEst = unchecked(
                              ((UInt64)(numHi - denom) << Digit.BitN | numLo)
                            + (UInt64)qEst * denom
                          );
            q = unchecked((Digit)(Hi(rEst) - qEst));
            r = unchecked(Lo(rEst) + (denom & Hi(rEst)));
            Digit qq, rr;
            Div(num, denom, out qq, out rr);
            Debug.Assert(qq == q && rr == r, "internal error");
        }
    }
}
