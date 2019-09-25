///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: MpBootStatus.cs
//
//  Note:
//    This structure just contains a list of constants that are used to
//    signify the progress of processors as they are bought up by the BSP.
//

namespace Microsoft.Singularity
{
    using System.Runtime.CompilerServices;
    using System;

    /// <summary> Constants used in MP systems to describe the
    /// progress of an initializing application processor
    /// (AP). </summary>
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in c++")]
    public struct MpBootStatus
    {
        [AccessedByRuntime("referenced in c++")]
        public const uint Phase1Entry = 0x00000001;
        [AccessedByRuntime("referenced in c++")]
        public const uint Phase2Entry = 0x00000002;
        [AccessedByRuntime("referenced in c++")]
        public const uint Phase3Entry = 0x00000003;
        [AccessedByRuntime("referenced in c++")]
        public const uint UndumpEntry = 0x00000004;
        [AccessedByRuntime("referenced in c++")]
        public const uint HalEntry    = 0x00000005;

        [AccessedByRuntime("referenced in c++")]
        public const uint FailureMask  = 0x80000000;
        [AccessedByRuntime("referenced in c++")]
        public const uint BadSignature = 0x80000001;
        [AccessedByRuntime("referenced in c++")]
        public const uint ConfigLimit  = 0x80000002;
        [AccessedByRuntime("referenced in c++")]
        public const uint AllocFailure = 0x80000003;

        // XXX the following are just to keep Bartok happy.
        // Without nop this struct is generated as a class.
        // Without dummy Bartok falls over.
        int dummy;

        [AccessedByRuntime("referenced in c++")]
        public static void nop() {}
    }
}
