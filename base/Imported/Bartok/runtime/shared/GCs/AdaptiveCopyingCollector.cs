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

    using System.Collections;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

#if SINGULARITY
    using Microsoft.Singularity;
#endif
    [NoCCtor]
    internal class AdaptiveCopyingCollector: GenerationalCollector
    {

        internal static AdaptiveCopyingCollector instance;

        private AdaptiveCopyingCollector() {
        }

        public static new void Initialize() {
            GenerationalCollector.Initialize();
            SemispaceCollector.Initialize();
            SlidingCollector.Initialize();
            // instance = new AdaptiveCopyingCollector();
            instance = (AdaptiveCopyingCollector )
                BootstrapMemory.Allocate(typeof(AdaptiveCopyingCollector));
        }

        internal override void TruncateOlderAllocationAreas(int generation) {
            SemispaceCollector.instance.TruncateOlderAllocationAreas(generation);
            SlidingCollector.instance.TruncateOlderAllocationAreas(generation);
        }

        internal override void CollectGeneration(int generation,
                                                 UIntPtr generationPageCount)
        {
            UIntPtr availableMemory = (UIntPtr)
                (MemoryManager.MemorySize - MemoryManager.OperatingSystemSize);
            UIntPtr softPageCountLimit = PageTable.PageCount(availableMemory);
            if (generation == (int)MAX_GENERATION &&
                (generationPageCount << 1) > softPageCountLimit) {
                // Use sliding collector when fromSpace > 1/2 available memory
                SlidingCollector.instance.CollectGeneration(generation, generationPageCount);
            } else {
                SemispaceCollector.instance.CollectGeneration(generation, generationPageCount);
            }
        }

        internal override void EnableHeap() {
            SlidingCollector.instance.EnableHeap();
            SemispaceCollector.instance.EnableHeap();
        }

    }

}
