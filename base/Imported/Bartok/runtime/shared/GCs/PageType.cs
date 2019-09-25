//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs {

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;

    // If the order of the page types is to be changed, remember to change
    // the 5 functions pointed out in PageTable, and minor change in
    // ConvertMethod.cs. We do not put the functions in this file, since
    // PageType is an enum, not a class. These should be the only places
    // that know the internal of PageType. Other classes should be already
    // cleaned all the assumptions of the page type values and order.
    // Also note that generational collectors have the assumption that an
    // older generation has bigger value than a younger one. So do not
    // change the order of Owner0...Owner7.

    [FlagsAttribute]
    public enum PageType : byte {

        // Let Unallocated be 0. Then after the page table is allocated by VirtualAlloc,
        // which automatically initializes the memory to 0, the page table entries
        // need not to be reinitialized as Unallocated.

        Unallocated     = 0x00,
        NonGC           = 0x01,                         // Used by Singularity ABI.

        // System pages are unavailable to the GC heap.
        Stack           = 0x02,                         // Used by Singularity ABI.
        System          = 0x03,                         // Used by Singularity ABI.
        Shared          = 0x04,                         // Shared heap page.
        Unknown         = 0x05,

        // For GC heap.

        // Unused pages are available for inclusion in the GC heap.
        UnusedDirty     = 0x06,
        UnusedClean     = 0x07,

        // Let all the GC heap types be higher numbers so that in PageTable.IsGCPage,
        // we still need only one comparison: type >=Owner0.

        Owner0          = 0x08,
        Owner1          = 0x09,
        Owner2          = 0x0a,
        Owner3          = 0x0b,
        Owner4          = 0x0c,
        Owner5          = 0x0d,
        Owner6          = 0x0e,
        Owner7          = 0x0f,

        Zombie4         = 0x0c,
        Zombie5         = 0x0d,
        Zombie6         = 0x0e,
        Zombie7         = 0x0f,

        // Masks for page type.

        TypeMask        = 0x0c,
        ZombieMask    = 0x0c,
        Zombie            = 0x4
    }
}
