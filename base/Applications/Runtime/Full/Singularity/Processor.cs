////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

namespace Microsoft.Singularity
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Threading;

    using Microsoft.Singularity.V1.Services;
    using Microsoft.Singularity.V1.Threads;

    using Microsoft.Singularity.Isal;

    [CLSCompliant(false)]
    [NoCCtor]
    [AccessedByRuntime("referenced in Processor.cpp")]
    public class Processor
    {
        public static long CyclesPerSecond
        {
            [NoHeapAllocation]
            get { return ProcessService.GetCyclesPerSecond(); }
        }

        public static ulong CycleCount
        {
            get { return GetCycleCount(); }
        }

        public static ulong GetCycleCount()
        {
            return Isa.GetCycleCount();
        }

        public static void WriteMsr(uint offset,ulong value)
        {
            Isa.WriteMsr(offset, value);
        }

        public static ulong ReadMsr(uint offset)
        {
            return Isa.ReadMsr(offset);
        }

        public static bool AtKernelPrivilege()
        {
            return !Isa.IsInUserMode();
        }

        public static void ReadCpuid(uint feature, 
                                     out uint v0, out uint v1, out uint v2, out uint v3)
        {
            Isa.ReadCpuid(feature, out v0, out v1, out v2, out v3);
        }

        public static ulong ReadPmc(uint offset)
        {
            return Isa.ReadPmc(offset);
        }

        [NoHeapAllocation]
        [AccessedByRuntime("output to header : called by c code")]
        internal static unsafe ThreadContext * GetCurrentThreadContext()
        {
            unsafe {
                return (ThreadContext *) Isa.GetCurrentThread();
            }
        }

        [NoHeapAllocation]
        [AccessedByRuntime("output to header : called by c code")]
        internal static unsafe ProcessorContext * GetCurrentProcessorContext()
        {
            unsafe {
                return (ProcessorContext *) Isa.GetCurrentCpu();
            }
        }

        [NoHeapAllocation]
        internal static Thread GetCurrentThread()
        {
            unsafe {
                return GetCurrentThreadContext()->thread;
            }
        }

        //////////////////////////////////////////////////////////////////////
        //
        // These methods are currently marked external because they are used
        // by device drivers.  We need a tool to verify that device drivers
        // are in fact using them correctly!
        //

        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static bool DisableLocalPreemption()
        {
            //  BUGBUG: this is a placeholder until the new scheduler work
            //  gets implemented, and we'll be able to control the local scheduling

            //  The current usage in SIPs seem only to rely on disabling preemption for
            //  performance reasons, not for corectness. 
            //  return PlatformService.DisableInterrupts();

            return false;
        }

        [NoHeapAllocation]
        [AccessedByRuntime("referenced from c++")]
        public static void RestoreLocalPreemption(bool enabled)
        {
            //  Same as above, use the interrupts disabled temporary, until the scheduller
            //  changes with a SIP hierarcy get integrated. 
            
            //  The current usage in SIPs seem only to rely on disabling preemption for
            //  performance reasons, not for corectness. 
            //  PlatformService.RestoreInterrupts(enabled);
        }

    }
}
