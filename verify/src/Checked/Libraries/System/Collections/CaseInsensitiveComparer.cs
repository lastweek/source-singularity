// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class: CaseInsensitiveComparer
//
//============================================================  
namespace System.Collections
{
    using System;
    using System.Collections;
    using System.Globalization;

    //| <include path='docs/doc[@for="CaseInsensitiveComparer"]/*' />
    public class CaseInsensitiveComparer : IComparer {
        public static readonly CaseInsensitiveComparer Default = new CaseInsensitiveComparer();

        //| <include path='docs/doc[@for="CaseInsensitiveComparer.CaseInsensitiveComparer"]/*' />
        public CaseInsensitiveComparer() {
        }

        //| <include path='docs/doc[@for="CaseInsensitiveHashCodeProvider.DefaultInvariant"]/*' />
        public static CaseInsensitiveComparer DefaultInvariant
        {
            get
            {
                return Default;
            }
        }

        // Behaves exactly like Comparer.Default.Compare except that the comparison is case insensitive
        // Compares two Objects by calling CompareTo.  If a ==
        // b,0 is returned.  If a implements
        // IComparable, a.CompareTo(b) is returned.  If a
        // doesn't implement IComparable and b does,
        // -(b.CompareTo(a)) is returned, otherwise an
        // exception is thrown.
        //
        //| <include path='docs/doc[@for="CaseInsensitiveComparer.Compare"]/*' />
        public int Compare(Object a, Object b) {
            String sa = a as String;
            String sb = b as String;
            if (sa != null && sb != null)
                return CompareInfo.Compare(sa, sb, CompareOptions.IgnoreCase);
            else
                return Comparer.Default.Compare(a,b);
        }
    }
}
