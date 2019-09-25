//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Heap for memory passed between processes.
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;
using System.Collections;
using System.Diagnostics;

namespace Microsoft.Singularity.Memory
{
    // <summary>
    // Non-garbage collected heap for memory transferred between processes.
    // </summary>
    [NoCCtor]
    [CLSCompliant(false)]
    public partial class SharedHeap {

        // <summary>
        // Structure for tracking allocated regions.
        // </summary>
        [StructLayout(LayoutKind.Sequential)]
        [RequiredByBartok]
        public partial struct Allocation {
            private UIntPtr data;  // Address of the allocated memory region.
            private UIntPtr size;  // Size of above in bytes.
            private unsafe UIntPtr type;  // Type information.
            internal unsafe Allocation *next;  // Next on owner's list.
            private unsafe Allocation *prev;  // Previous on owner's list.
            private int owner;
        }

    }
}
