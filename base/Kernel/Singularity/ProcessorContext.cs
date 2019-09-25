////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ProcessorContext.cs
//
//  Note:
//

namespace Microsoft.Singularity
{
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;
    using Microsoft.Singularity.Isal;
#if SINGULARITY_KERNEL
    using Microsoft.Singularity.Hal;
#endif

    [NoCCtor]
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    [AccessedByRuntime("referenced from c++")]
    internal struct ProcessorContext
    {
        // All fields are private to the kernel.
        //
        // It's important that the embedded ThreadContexts in this struct are paragraph-aligned.
        // That's because those ThreadContexts contain 'mmx' fields, which are the target of
        // FXSAVE and FXRSTOR instructions.  Intel specifies that those fields must be paragraph-
        // aligned, or the instructions will fault.

        [AccessedByRuntime("referenced from c++")]
        internal CpuRecord                  cpuRecord;

        [AccessedByRuntime("referenced from c++")] private unsafe void *halCpu;
        [AccessedByRuntime("referenced from c++")] private unsafe void *_processor; // Only changed by garbage collector.

        [AccessedByRuntime("referenced from c++")] internal UIntPtr exception;

        [AccessedByRuntime("referenced from c++")] internal volatile int ipiFreeze;
        [AccessedByRuntime("referenced from c++")] internal unsafe ProcessorContext* nextProcessorContext; // singly-linked circular list node for MpExecution use

        [AccessedByRuntime("referenced from c++")] internal volatile int gcIpiGate; //

        //////////////////////////////////////////////////// External Methods.
        //
        internal Processor processor {
            [NoHeapAllocation]
            get { return GetProcessor(); }
        }

        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal extern void UpdateAfterGC(Processor processor);

        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(32)]
        [NoHeapAllocation]
        private extern Processor GetProcessor();
    }
}


