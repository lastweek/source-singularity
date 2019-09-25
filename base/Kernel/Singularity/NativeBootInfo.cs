//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity
{

    [StructLayout(LayoutKind.Sequential, Pack=4)]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in c++")]
    public struct NativeBootInfo
    {

        // IDT and PIC
        [AccessedByRuntime("referenced in c++")]
        internal IX.IDTP   BiosIdtPtr;
        [AccessedByRuntime("referenced in c++")]
        internal ushort     BiosPicMask;
        [AccessedByRuntime("referenced in c++")]
        internal byte       BiosWarmResetCmos;
        [AccessedByRuntime("referenced in c++")]
        internal uint       BiosWarmResetVector;
        [AccessedByRuntime("referenced in c++")]
        internal uint       Info16;

        // Temporary IDT
        [AccessedByRuntime("referenced in c++")]
        internal ulong    IdtEnter0;
        [AccessedByRuntime("referenced in c++")]
        internal ulong    IdtEnter1;
        [AccessedByRuntime("referenced in c++")]
        internal ulong    IdtEnterN;
        [AccessedByRuntime("referenced in c++")]
        internal ulong    IdtTarget;

        [AccessedByRuntime("referenced in c++")]
        internal ulong    Pdpt32;

        [AccessedByRuntime("referenced in c++")]
        internal ulong    Undump;

        //
        [AccessedByRuntime("referenced in c++")]
        internal ulong    Heap32;

        // PCI Information (V2.0+)
        [AccessedByRuntime("referenced in c++")]
        internal uint       PciBiosAX;
        [AccessedByRuntime("referenced in c++")]
        internal uint       PciBiosBX;
        [AccessedByRuntime("referenced in c++")]
        internal uint       PciBiosCX;
        [AccessedByRuntime("referenced in c++")]
        internal uint       PciBiosEDX;

        // BIOS Information
        [AccessedByRuntime("referenced in c++")]
        public   ulong      AcpiRoot32;
        [AccessedByRuntime("referenced in c++")]
        internal ulong      PnpNodesAddr32;
        [AccessedByRuntime("referenced in c++")]
        internal uint       PnpNodesSize32;
        [AccessedByRuntime("referenced in c++")]
        internal ulong      SmbiosRoot32;
        [AccessedByRuntime("referenced in c++")]
        internal ulong      DmiRoot32;
        [AccessedByRuntime("referenced in c++")]
        internal uint       IsaCsns;
        [AccessedByRuntime("referenced in c++")]
        internal ushort     IsaReadPort;
        [AccessedByRuntime("referenced in c++")]
        internal uint       Ebda32;
        [AccessedByRuntime("referenced in c++")]
        public   uint       MpFloat32;

        // 1394 Information
        [AccessedByRuntime("referenced in c++")]
        internal ulong      Ohci1394Base;
        [AccessedByRuntime("referenced in c++")]
        internal ulong      Ohci1394BufferAddr32;
        [AccessedByRuntime("referenced in c++")]
        internal uint       Ohci1394BufferSize32;

        // MP specific variables
        [AccessedByRuntime("referenced in c++")]
        public   ulong      MpEnter32;          // Entry point
        [AccessedByRuntime("referenced in c++")]
        public   uint       MpCpuCount;         // No of AP's booted
        [AccessedByRuntime("referenced in c++")]
        public   uint       MpStatus32;         // Error indicator
        [AccessedByRuntime("referenced in c++")]
        public   ulong      MpStartupLock32;    // Pointer to MP init lock var
        [AccessedByRuntime("referenced in c++")]
        public   ulong      MpBootInfo32;       // Pointer to MpBootInfo

#if ISA_IX64
        [AccessedByRuntime("referenced in c++")]
        internal ulong Ppml432; // pointer to Page Map Level-4
        [AccessedByRuntime("referenced in c++")]
        internal ulong AddrTss; // pointer to the 64-bit TSS containing the IST stack table
#endif

        [AccessedByRuntime("defined in BootInfo.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        internal static unsafe extern NativeBootInfo * HalGetBootInfo();

        [NoHeapAllocation]
        public static unsafe NativeBootInfo GetBootInfo()
        {
            NativeBootInfo *ptr;

            ptr = HalGetBootInfo();
            return *ptr;
        }
    }
}
