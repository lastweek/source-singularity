// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// Simple PE Loader for Singularity
//
// Currently does not support:
//      x64
//      sections loaded at separate addresses
//      loading at preferred address

// #define verbose

namespace Microsoft.Singularity.Loader
{
    using System;
    using System.Diagnostics;
    using System.Runtime.InteropServices;
    using System.Threading;
    using Microsoft.Singularity;
    using Microsoft.Singularity.Io;

    [CLSCompliant(false)]
    internal struct SectionHeader
    {
        internal const uint IMAGE_SCN_MEM_DISCARDABLE = 0x02000000;  // Can be discarded.
        internal const uint IMAGE_SCN_MEM_READ        = 0x40000000;  // Is readable.
        internal const uint IMAGE_SCN_MEM_WRITE       = 0x80000000;  // Is writeable.

        // State

        internal readonly String name;
        internal readonly uint   virtualSize;
        internal readonly uint   virtualAddress;
        internal readonly uint   sizeOfRawData;
        internal readonly uint   pointerToRawData;
        internal readonly uint   characteristics;

        internal SectionHeader(IoMemory mem, ref int offset)
        {
            if (offset + 40 > mem.Length) {
                Error.AccessOutOfRange();
            }
            name                = mem.ReadAsciiZeroString(offset, 8);
            virtualSize         = mem.Read32Unchecked(offset + 8);
            virtualAddress      = mem.Read32Unchecked(offset + 12);
            sizeOfRawData       = mem.Read32Unchecked(offset + 16);
            pointerToRawData    = mem.Read32Unchecked(offset + 20);
            characteristics     = mem.Read32Unchecked(offset + 36);
            offset += 40;
        }

        [Conditional("DEBUG")]
        internal void DumpToStream()
        {
            Tracing.Log(Tracing.Debug,
                        "    {0:x8}..{1:x8} [{2:x8}..{3:x8}] char={4:x8}",
                        virtualAddress, virtualAddress + virtualSize,
                        pointerToRawData, pointerToRawData + sizeOfRawData,
                        characteristics);
        }

        internal bool IsDiscardable
        {
            get { return ((characteristics & IMAGE_SCN_MEM_DISCARDABLE) != 0); }
        }

    }
}
