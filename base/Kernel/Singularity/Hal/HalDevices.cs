///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: HalDevices.cs
//
//        Many of these methods may be called from C++ or ASM code (PIC functions)
//        so they need to be static. It basically switches out to the HalDevices
//        interface implemented by the specific activated HAL.
//

using System;
using System.Collections;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Io;

using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.Hal
{
    [CLSCompliant(false)]
    public abstract class HalDevices
    {
        public abstract void Initialize(Processor processor);

        public abstract void ReleaseResources();

        [NoHeapAllocation]
        public abstract void EnableIoInterrupt(byte irq);

        [NoHeapAllocation]
        public abstract void DisableIoInterrupt(byte irq);

        [NoHeapAllocation]
        public abstract bool InternalInterrupt(byte interrupt);

        [NoHeapAllocation]
        public abstract byte GetMaximumIrq();

        [NoHeapAllocation]
        public abstract int GetProcessorCount();

        public abstract void StartApProcessors(int cpus);

        [NoHeapAllocation]
        public abstract void ResetApProcessors();

        [NoHeapAllocation]
        public abstract void FreezeProcessors();

        [NoHeapAllocation]
        public abstract void SendFixedIPI(byte vector, int from, int to);

        [NoHeapAllocation]
        public abstract void BroadcastFixedIPI(byte vector, bool includeSelf);

        [NoHeapAllocation]
        public abstract void ClearFixedIPI(int interrupt);

        public abstract byte TranslatePciInterrupt(byte currentInterruptLine,
                                                   byte pciInterruptPin,
                                                   PciPort pciPort);
    }
}

