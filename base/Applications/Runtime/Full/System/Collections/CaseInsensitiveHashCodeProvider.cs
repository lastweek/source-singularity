// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//============================================================
//
// Class: CaseInsensitiveHashCodeProvider
//
// Purpose: Designed to support hashtables which require
// case-insensitive behavior while still maintaining case,
// this provides an efficient mechanism for getting the
// hashcode of the string ignoring case.
//
//============================================================  
namespace System.Collections
{
    using System;
    using System.Collections;
    using System.Globalization;

    //| <include path='docs/doc[@for="CaseInsensitiveHashCodeProvider"]/*' />
    public class CaseInsensitiveHashCodeProvider : IHashCodeProvider {

        public static readonly CaseInsensitiveHashCodeProvider Default
        = new CaseInsensitiveHashCodeProvider();

        //| <include path='docs/doc[@for="CaseInsensitiveHashCodeProvider.CaseInsensitiveHashCodeProvider"]/*' />
        public CaseInsensitiveHashCodeProvider() {
        }

        //| <include path='docs/doc[@for="CaseInsensitiveHashCodeProvider.DefaultInvariant"]/*' />
        public static CaseInsensitiveHashCodeProvider DefaultInvariant
        {
            get
            {
                return Default;
            }
        }

        //| <include path='docs/doc[@for="CaseInsensitiveHashCodeProvider.GetHashCode"]/*' />
        public int GetHashCode(Object obj) {
            if (obj == null) {
                throw new ArgumentNullException("obj");
            }

            String s = obj as String;
            if (s == null) {
                return obj.GetHashCode();
            }

            return TextInfo.GetCaseInsensitiveHashCode(s);
        }
    }
}
