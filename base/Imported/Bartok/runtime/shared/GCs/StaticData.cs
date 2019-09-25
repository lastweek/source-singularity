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

    internal unsafe class StaticData
    {
        [RequiredByBartok]
        private static int sectionCount;
        [RequiredByBartok]
        private static UIntPtr **dataSectionEnd; // unmanaged uint**[]
        [RequiredByBartok]
        private static UIntPtr **dataSectionBase; // unmanaged uint**[]
        [RequiredByBartok]
        private static UIntPtr **roDataSectionEnd; // unmanaged uint**[]
        [RequiredByBartok]
        private static UIntPtr **roDataSectionBase; // unmanaged uint**[]
        [RequiredByBartok]
        private static uint **staticDataPointerBitMap; // unmanaged uint*[]

        [PreInitRefCounts]
#if !SINGULARITY                // Needed before Bartok runtime is initialized
        [NoStackLinkCheck]
#endif
        internal static void Initialize() {
            for (int section = 0; section < sectionCount; section++) {
                UIntPtr startAddr = (UIntPtr) dataSectionBase[section];
                startAddr = PageTable.PageAlign(startAddr);
                UIntPtr size = (UIntPtr) dataSectionEnd[section] - startAddr;
                size = PageTable.PagePad(size);
                PageManager.SetStaticDataPages(startAddr, size);
            }
            for (int section = 0; section < sectionCount; section++) {
                UIntPtr startAddr = (UIntPtr) roDataSectionBase[section];
                startAddr = PageTable.PageAlign(startAddr);
                UIntPtr size = (UIntPtr) roDataSectionEnd[section]-startAddr;
                size = PageTable.PagePad(size);
                PageManager.SetStaticDataPages(startAddr, size);
            }
        }

        internal static
        void ScanStaticData(DirectReferenceVisitor referenceVisitor)
        {
            Finalizer.VisitBootstrapData(referenceVisitor);
            for (int section = 0; section < sectionCount; section++) {
                int size = (int)
                    (*(dataSectionEnd+section)-*(dataSectionBase+section));
                int iters = (size + 31) / 32;
                UIntPtr *ptr = *(dataSectionBase+section);
                uint *pointerBitmap = *(staticDataPointerBitMap+section);
                for (int i = 0; i < iters; i++) {
                    uint mask = *pointerBitmap++;
                    if (mask != 0) {
                        for (int j = 0; j < 32; j++) {
                            if ((mask & 1) != 0 && *ptr != UIntPtr.Zero) {
                                referenceVisitor.Visit(ptr);
                            }
                            ptr++;
                            mask >>= 1;
                        }
                    } else {
                        ptr += 32;
                    }
                }
            }
        }

        internal static
        uint ScanStaticPointerData(NonNullReferenceVisitor referenceVisitor)
        {
            uint totalSize = 0;
            for (int section = 0; section < sectionCount; section++) {
                uint size = (uint)(*(dataSectionEnd+section)-
                    *(dataSectionBase+section));
                totalSize += size;
                UIntPtr *ptr = *(dataSectionBase+section);
                uint *pointerBitmap = *(staticDataPointerBitMap+section);
                uint iters = (size + 31) / 32;
                for (uint i = 0; i < iters; i++) {
                    uint mask = *pointerBitmap++;
                    if (mask != 0) {
                        for (int j = 0; j < 32; j++) {
                            if ((mask & 1) != 0) {
                                referenceVisitor.Visit(ptr);
                            }
                            ptr++;
                            mask >>= 1;
                        }
                    } else {
                        ptr += 32;
                    }
                }
            }

            for (int section = 0; section < sectionCount; section++) {
                uint size = (uint)(*(roDataSectionEnd+section)-
                    *(roDataSectionBase+section));
                totalSize += size;
            }

            return totalSize*(uint)UIntPtr.Size;
        }
    }

}
