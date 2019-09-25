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
    using Microsoft.Singularity;
    using Microsoft.Singularity.Io;

    using System;
    using System.Diagnostics;
    using System.Runtime.InteropServices;
    using System.Threading;

    internal struct DirectoryEntry
    {
        // State
        internal readonly uint virtualAddress;
        internal readonly uint size;

        internal DirectoryEntry(IoMemory mem, ref int offset)
        {
            if (offset + 8 > mem.Length) {
                Error.AccessOutOfRange();
            }

            virtualAddress = mem.Read32Unchecked(offset + 0);
            size           = mem.Read32Unchecked(offset + 4);
            offset += 8;
        }

        // Output Routines

        [Conditional("DEBUG")]
        internal void DumpToStream(String prefix)
        {
            Tracing.Log(Tracing.Debug, "    {0} {1:x8}..{2:x8}",
                        prefix, virtualAddress, virtualAddress + size);
        }
    }
}
