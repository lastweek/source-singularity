// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
//=============================================================================
//
// Class: RankException
//
// Purpose: For methods that are passed arrays with the wrong number of
//          dimensions.
//
//=============================================================================  

namespace System
{

    using System;

    //| <include path='docs/doc[@for="RankException"]/*' />
    public class RankException : SystemException
    {
        //| <include path='docs/doc[@for="RankException.RankException"]/*' />
        public RankException()
            : base("Arg_RankException") {
        }

        //| <include path='docs/doc[@for="RankException.RankException1"]/*' />
        public RankException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="RankException.RankException2"]/*' />
        public RankException(String message, Exception innerException)
            : base(message, innerException) {
        }
    }
}
