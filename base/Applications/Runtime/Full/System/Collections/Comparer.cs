// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class:  Comparer
//
// Purpose: Default IComparer implementation.
//
//===========================================================  
namespace System.Collections
{

    using System;
    using System.Globalization;
    //| <include path='docs/doc[@for="Comparer"]/*' />
    public sealed class Comparer : IComparer
    {
        //| <include path='docs/doc[@for="Comparer.Default"]/*' />
        public static readonly Comparer Default = new Comparer();

        public Comparer() {
        }

        // Compares two Objects by calling CompareTo.  If a ==
        // b,0 is returned.  If a implements
        // IComparable, a.CompareTo(b) is returned.  If a
        // doesn't implement IComparable and b does,
        // -(b.CompareTo(a)) is returned, otherwise an
        // exception is thrown.
        //
        //| <include path='docs/doc[@for="Comparer.Compare"]/*' />
        public int Compare(Object a, Object b) {
            if (a == b) return 0;
            if (a == null) return -1;
            if (b == null) return 1;

            String sa = a as String;
            String sb = b as String;
            if (sa != null && sb != null)
                return CompareInfo.Compare(sa, sb);
            IComparable ia = a as IComparable;
            if (ia != null)
                return ia.CompareTo(b);
            IComparable ib = b as IComparable;
            if (ib != null)
                return -ib.CompareTo(a);
            throw new ArgumentException("Argument_ImplementIComparable");
        }
    }
}
