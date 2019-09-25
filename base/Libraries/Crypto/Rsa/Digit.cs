// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Diagnostics;

namespace Microsoft.Singularity.Crypto.PublicKey
{
    struct Digit
    {
        readonly UInt32 _digit;
        Digit(UInt32 digit) { _digit = digit; }
        public static implicit operator UInt32(Digit d) { return d._digit; }
        public static explicit operator long(Digit d) {
            return (long)d._digit;
        }
        public static implicit operator Digit(UInt32 digit) {
            return new Digit(digit);
        }
        public override string ToString() { return _digit.ToString(); }
        public static Digit operator <<(Digit d, int n) {
            Debug.Assert(0 <= n && n < BitN, "internal error");
            return new Digit(d._digit << n);
        }
        public static Digit operator >>(Digit d, int n) {
            Debug.Assert(0 <= n && n < BitN, "internal error");
            return new Digit(d._digit >> n);
        }
        internal const int BitN = 32;
        internal const UInt32 MaxValue = UInt32.MaxValue;
        static byte[]
            leadingZeroBitN
          = new byte[] { 4, 3, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0 };
        internal static int SigBitN(Digit d) {
            d |= 1;
            int bitN = BitN;
            while (d < 1U << BitN - 5) {
                bitN -= 5; d <<= 5;
            }
            return bitN - leadingZeroBitN[d >> BitN - 4];
        }
        internal static Digit TwoAdicInverse(Digit d) {
            if ((d & 1) == 0) {
                throw new ArgumentException();
            }
            UInt32 dInverse = unchecked(3 * d ^ 2)
                 , error = unchecked(1 - d * dInverse);
            Debug.Assert((error & 31) == 0, "internal error");
            for (int bitN = 5; bitN < BitN / 2; bitN *= 2) {
                unchecked {
                    dInverse += dInverse * error;
                    error = error * error;
                    Debug.Assert(error == 1 - d * dInverse, "internal error");
                }
            }
            return unchecked(dInverse * error + dInverse);
        }
        static byte[]
            trailingZeroN
          = new byte[] { 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0 };
        internal static Digit OddGcd(Digit d1, Digit d2) {
            if (((d1 | d2) & 1) == 0) {
                throw new ArgumentException();
            }
            if (d1 == 0 || d2 == 0) {
                Debug.Assert(false, "untested code");
                return d1 + d2;
            }
            do { d1 >>= trailingZeroN[d1 & 15]; } while ((d1 & 1) == 0);
            do { d2 >>= trailingZeroN[d2 & 15]; } while ((d2 & 1) == 0);
            while (d1 != d2) {
                int sh1 = 1 + trailingZeroN[(d1 ^ d2) >> 1 & 15];
                UInt32 n12Max = d1 > d2 ? d1 : d2;
                d1 = d1 ^ d2 ^ n12Max;
                d2 = n12Max - d1 >> sh1;
                do { d2 >>= trailingZeroN[d2 & 15]; } while ((d2 & 1) == 0);
                Debug.Assert((d1 & d2 & 1) != 0, "internal error");
            }
            return d1;
        }
        internal static Digit Random(Random generator) {
            return (UInt32)generator.Next(65536) << 16
                 | (UInt32)generator.Next(65536);
        }
        internal static Digit
        Random(UInt32 dlow, UInt32 dhigh, Random generator) {
            if (dhigh < dlow) {
                throw new ArgumentException();
            }
            UInt32 spread = dhigh - dlow;
            int shiftBitN = BitN - SigBitN(spread | 1);
            UInt32 result = 0;
            do {
                result = Random(generator)._digit >> shiftBitN;
            } while (result > spread);
            return dlow + result;
        }
    }
}
