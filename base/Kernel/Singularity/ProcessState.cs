////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Process.cs
//
//  Note:
//

namespace System.Threading
{
    public enum ProcessState
    {
        Unstarted,
        Running,
        Suspending,
        SuspendingRecursive,
        Suspended,
        Stopping,
        Stopped,
    }
}
