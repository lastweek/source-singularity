// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
// Void
//  This class represents an empty variant
////////////////////////////////////////////////////////////////////////////////

namespace System
{

    using System;

    //| <include path='docs/doc[@for="Empty"]/*' />
    internal sealed class Empty
    {
        //Package private constructor
        internal Empty() {
        }

        //| <include path='docs/doc[@for="Empty.Value"]/*' />
        public static readonly Empty Value = new Empty();

        //| <include path='docs/doc[@for="Empty.ToString"]/*' />
        public override String ToString()
        {
            return String.Empty;
        }
    }
}
