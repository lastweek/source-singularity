//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/


namespace System.GCs {

    using System.Runtime.CompilerServices;
    using System.Threading;

    internal class CentralPT: PageTable {

        [PreInitRefCounts]
        [NoStackLinkCheck]
        new internal static unsafe void Initialize() {
            SetProcessTag((uint) Thread.GetCurrentProcessIndex() << 16);
            pageTableCount = new UIntPtr(1U) << (int) (31 - PageBits);
            UIntPtr pageTableSize = pageTableCount * sizeof(uint);
            halPageDescriptor = (uint *)
                MemoryManager.AllocateMemory(pageTableSize);
            UIntPtr startPage = Page((UIntPtr) halPageDescriptor);
            UIntPtr pageCount = PageCount(PagePad(pageTableCount));
            SetType(startPage, pageCount, PageType.System);
            SetProcess(UIntPtr.Zero, pageTableCount);
        }

        [Inline]
        internal static unsafe uint PageTableEntryImpl(UIntPtr page)
        {
            return *(halPageDescriptor + page);
        }

        [Inline]
        internal static unsafe void SetPageTableEntryImpl(UIntPtr page,
                                                          uint value)
        {
            *(halPageDescriptor + page) = value;
        }
    }
}
