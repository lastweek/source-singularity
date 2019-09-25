namespace System.GCs {

    using Microsoft.Bartok.Runtime;
    using System.Runtime.CompilerServices;
    using System.Threading;

    // this class contains all of the things from the generational GC that
    // is accessed by the greater runtime in a non-virtual fashion.  putting
    // it here is necessary to allow devirtualization of critical
    // non-generational GC methods.
    [NoCCtor]
    internal class GenerationalGCData
    {
        
        [TrustedNonNull]
        internal static RememberedSet installedRemSet;

        // PageType.Owner0 is not 0 now. One side effect is that the following arrays
        // have unused entries.

        internal static short[]     gcCountTable;

        internal static short[]     gcFrequencyTable;

        internal static UIntPtr[]   gcPromotedTable;
        internal static UIntPtr[]   gcPromotedLimitTable;

        internal static int[]       fromSpacePageCounts;

        internal static UIntPtr     nurserySize;
        internal static UIntPtr     pretenuredSinceLastFullGC;
        internal const  PageType    nurseryGeneration     = PageType.Owner0;
        internal const  PageType    largeObjectGeneration = PageType.Owner1;
        internal static PageType    defaultGeneration;

        internal static PageType MIN_GENERATION {
            get { return PageType.Owner0; }
        }
        internal static PageType MAX_GENERATION {
            get { return PageType.Owner1; }
        }

        // These two arrays contain the range of pages each generation is within
        internal static UIntPtr[] MinGenPage;
        internal static UIntPtr[] MaxGenPage;

        [Inline]
        internal static bool IsLargeObjectSize(UIntPtr size) {
            UIntPtr largeObjectSize =
                (UIntPtr) (1 << Constants.LargeObjectBits);
            return size >= largeObjectSize;
        }

    }
}
