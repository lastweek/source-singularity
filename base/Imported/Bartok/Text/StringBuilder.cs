// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*============================================================
**
** Class:  StringBuilder
**
** Purpose: A prototype implementation of the StringBuilder
** class.
**
===========================================================*/
namespace System.Text
{
    using System.Text;
    using System.Threading;
    using System;
    using System.Diagnostics;
    using System.Runtime.CompilerServices;

    // This class represents a mutable string.  It is convenient for situations in
    // which it is desirable to modify a string, perhaps by removing, replacing, or
    // inserting characters, without creating a new String subsequent to
    // each modification.
    //
    // The methods contained within this class do not return a new StringBuilder
    // object unless specified otherwise.  This class may be used in conjunction with the String
    // class to carry out modifications upon strings.
    //
    // When passing null into a constructor in VJ and VC, the null
    // should be explicitly type cast.
    // For Example:
    // StringBuilder sb1 = new StringBuilder((StringBuilder)null);
    // StringBuilder sb2 = new StringBuilder((String)null);
    //
    //| <include path='docs/doc[@for="StringBuilder"]/*' />
    [NoCCtor]
    public sealed partial class StringBuilder {

        [RequiredByBartok]
        internal String m_StringValue = null;

    }
}



