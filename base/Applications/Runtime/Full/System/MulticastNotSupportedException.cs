// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
////////////////////////////////////////////////////////////////////////////////
// MulticastNotSupportedException
// This is thrown when you add multiple callbacks to a non-multicast delegate.
////////////////////////////////////////////////////////////////////////////////

namespace System
{

    using System;

    //| <include path='docs/doc[@for="MulticastNotSupportedException"]/*' />
    public sealed class MulticastNotSupportedException : SystemException {

        //| <include path='docs/doc[@for="MulticastNotSupportedException.MulticastNotSupportedException"]/*' />
        public MulticastNotSupportedException()
            : base("Arg_MulticastNotSupportedException") {
        }

        //| <include path='docs/doc[@for="MulticastNotSupportedException.MulticastNotSupportedException1"]/*' />
        public MulticastNotSupportedException(String message)
            : base(message) {
        }

        //| <include path='docs/doc[@for="MulticastNotSupportedException.MulticastNotSupportedException2"]/*' />
        public MulticastNotSupportedException(String message, Exception inner)
            : base(message, inner) {
        }
    }
}
