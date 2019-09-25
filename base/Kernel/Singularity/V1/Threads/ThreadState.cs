////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ThreadState.cs
//
//  Note:
//

namespace Microsoft.Singularity.V1.Threads
{
    using System;
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="ThreadState"]/*' />
    [Flags]
    public enum ThreadState
    {
        Undefined   = 0x0,
        Running     = 0x1,
        Unstarted   = 0x2,
        Stopped     = 0x4,
        Suspended   = 0x8,
        Blocked     = 0x10,
        Runnable    = 0x20
    }
}
