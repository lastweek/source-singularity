// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System.Threading
{
    using System.Threading;
    using System;
    // A constant used by methods that take a timeout (Object.Wait, Thread.Sleep
    // etc) to indicate that no timeout should occur.
    //
    // @todo: this should become an enum.
    //| <include path='docs/doc[@for="Timeout"]/*' />
    public sealed class Timeout
    {
        private Timeout()
        {
        }

        //| <include path='docs/doc[@for="Timeout.Infinite"]/*' />
        public static readonly TimeSpan Infinite = TimeSpan.Infinite;
    }

}
