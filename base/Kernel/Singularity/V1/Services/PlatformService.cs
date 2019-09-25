////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DebugService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.V1.Services
{
    [AccessedByRuntime("Method called from HAL.cpp")]
    public struct PlatformService
    {
        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        public static bool DisableInterrupts()
        {
            return PrivilegedGate.DisableInterrupts();
        }

        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        public static void RestoreInterrupts(bool enabled)
        {
            PrivilegedGate.RestoreInterrupts(enabled);
        }

        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        public static bool InterruptsDisabled()
        {
            return PrivilegedGate.InterruptsDisabled();
        }

        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        [CLSCompliant(false)]
        public static void CleanAndInvalidateDCache(UIntPtr address, UIntPtr length)
        {
#if ISA_ARM
            Microsoft.Singularity.Isal.Arm.XScale.Mmu.CleanInvalidateDCacheLines(address, length);
#endif
        }

        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        [CLSCompliant(false)]
        public static void InvalidateDCache(UIntPtr address, UIntPtr length)
        {
#if ISA_ARM
            Microsoft.Singularity.Isal.Arm.XScale.Mmu.InvalidateDCacheLines(address, length);
#endif
        }

        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        [CLSCompliant(false)]
        public static void SetCacheAttributes(UIntPtr address, UIntPtr length, bool cacheable, bool bufferable)
        {
#if ISA_ARM
            Microsoft.Singularity.Isal.Arm.XScale.Mmu.SetCacheAttributes(address, length, cacheable, bufferable);
#endif
        }

        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        public static int GetProcessorContextOffset()
        {
            return Platform.ThePlatform.CpuRecordPointerOffset;
        }

        [ExternalEntryPoint]
        [AccessedByRuntime("Called from HAL.cpp")]
        public static int GetThreadContextOffset()
        {
            return Platform.ThePlatform.ThreadRecordPointerOffset;
        }
    }
}
