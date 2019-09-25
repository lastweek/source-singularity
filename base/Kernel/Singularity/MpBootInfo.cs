///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: MpBootInfo.cs
//
//  Note:
//    This structure holds values needed to bring the application processors
//    into protected mode.
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity
{
    [StructLayout(LayoutKind.Sequential, Pack=4)]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in c++")]
    public struct MpBootInfo
    {
#if SINGULARITY_MP
        [AccessedByRuntime("referenced in c++")]
        public const uint MAX_CPU =
#  if MAX_CPU4
                                    4;
#  elif MAX_CPU3
                                    3;
#  elif MAX_CPU2
                                    2;
#  else
                                    15;
#  endif  // MAX_CPUX
#else
        [AccessedByRuntime("referenced in c++")]
        public const uint MAX_CPU = 1;
#endif // SINGULARITY_MP

        [AccessedByRuntime("referenced in c++")]
        public const uint Signature = 0x4d504249; // "MPBI"

        // Settings for next processor to enter protected mode
        [AccessedByRuntime("referenced in c++")]
        public uint     signature;
        [AccessedByRuntime("referenced in c++")]
        public UIntPtr  KernelStackBegin;
        [AccessedByRuntime("referenced in c++")]
        public UIntPtr  KernelStack;
        [AccessedByRuntime("referenced in c++")]
        public UIntPtr  KernelStackLimit;
        [AccessedByRuntime("referenced in c++")]
        public volatile int TargetCpu;

        [AccessedByRuntime("defined in MpBootInfo.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        internal static unsafe extern MpBootInfo * HalGetMpBootInfo();

        [AccessedByRuntime("defined in MpBootInfo.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        internal static unsafe extern void HalReleaseMpStartupLock();

        public unsafe void ReleaseMpStartupLock()
        {
             HalReleaseMpStartupLock();
        }

        public unsafe bool PrepareForCpuStart(int targetCpu)
        {

            UIntPtr size = MemoryManager.PagePad(
                Platform.BootCpu.KernelStackBegin
                - Platform.BootCpu.KernelStackLimit);

            UIntPtr stack = MemoryManager.KernelAllocate(
                MemoryManager.PagesFromBytes(size), null, 0, System.GCs.PageType.Stack);

            if (stack == UIntPtr.Zero) {
                return false;
            }

            KernelStackLimit = stack;
            KernelStackBegin = stack + size;
            signature = Signature;
            TargetCpu = targetCpu;

            HalReleaseMpStartupLock();

            return true;
        }
    }
}
