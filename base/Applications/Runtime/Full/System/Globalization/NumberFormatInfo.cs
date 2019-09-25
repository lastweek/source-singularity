// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
namespace System.Globalization
{
    using System;

    //| <include path='docs/doc[@for="NumberFormatInfo"]/*' />
    sealed public class NumberFormatInfo {
        private NumberFormatInfo() {}   // Prevent from being created

        internal static bool validForParseAsNumber
        {
            get { return true; }
#if DONT
            get { return CultureInfo.sDecimal != sThousand; }
#endif
        }

        internal static String perMilleSymbol = "\u2030";

        internal static String negativeInfinitySymbol {
            get { return CultureInfo.sNegInfinity; }
        }

        internal static String positiveInfinitySymbol {
            get { return CultureInfo.sPosInfinity; }
        }

        internal static int[] numberGroupSizes {
            get { return CultureInfo.nGrouping; }
        }

        internal static int[] percentGroupSizes {
            get { return CultureInfo.nGrouping; }
        }

        internal static String nanSymbol {
            get { return CultureInfo.sNan; }
        }

        internal static int numberNegativePattern {
            get { return CultureInfo.iNegNumber; }
        }

        internal static int percentPositivePattern {
            get { return CultureInfo.iPositivePercent; }
        }

        internal static int percentNegativePattern {
            get { return CultureInfo.iNegativePercent; }
        }

        internal static String negativeSign {
            get { return CultureInfo.sNegativeSign; }
        }

        internal static int numberDecimalDigits {
            get { return CultureInfo.iDigits; }
        }

        internal static String numberDecimalSeparator {
            get { return CultureInfo.sDecimal; }
        }

        internal static String numberGroupSeparator {
            get { return CultureInfo.sThousand; }
        }

        internal static String positiveSign {
            get { return CultureInfo.sPositiveSign; }
        }

        internal static int percentDecimalDigits {
            get { return CultureInfo.iDigits; }
        }

        internal static String percentDecimalSeparator {
            get { return CultureInfo.sDecimal; }
        }

        internal static String percentGroupSeparator {
            get { return CultureInfo.sThousand; }
        }

        internal static String percentSymbol {
            get { return CultureInfo.sPercent; }
        }

        internal static void ValidateParseStyle(NumberStyles style) {
            if ((style & NumberStyles.AllowHexSpecifier) != 0) { // Check for hex number
                if ((style & ~NumberStyles.HexNumber) != 0)
                    throw new ArgumentException("Arg_InvalidHexStyle");
            }
        }

    } // NumberFormatInfo
}
