//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs
{

    using Microsoft.Bartok.Options;
    using System.Runtime.CompilerServices;
    using System.Threading;

    [NoCCtor]
    [MixinConditional("GCProfiling")]
    [Mixin(typeof(BaseCollector))]
    internal abstract class ProfilingBaseCollector : BaseCollector
    {

#region Allocation

        [ManualRefCounts]
        internal override Object AllocateObject(VTable vtable,
                                                Thread currentThread)
        {
            Object result = base.AllocateObject(vtable, currentThread);
            if (GC.IsProfiling) {
                ProfileAllocation(result);
            }
            if (VTable.enableGCProfiling) {
                ulong size = (ulong) ObjectLayout.ObjectSize(vtable);
                RegisterNewObject(size);
            }
            return result;
        }

        [ManualRefCounts]
        internal override Array AllocateVector(VTable vtable,
                                               int numElements,
                                               Thread currentThread)
        {
            Array result =
                base.AllocateVector(vtable, numElements, currentThread);
            if (VTable.enableGCProfiling) {
                ulong size = (ulong)
                    ObjectLayout.ArraySize(vtable,
                                           unchecked((uint) numElements));
                RegisterNewObject(size);
            }
            return result;
        }

        [ManualRefCounts]
        internal override Array AllocateArray(VTable vtable,
                                              int rank,
                                              int totalElements,
                                              Thread currentThread)
        {
            Array result =
                base.AllocateArray(vtable, rank, totalElements, currentThread);
            if (VTable.enableGCProfiling) {
                ulong size = (ulong)
                    ObjectLayout.ArraySize(vtable,
                                           unchecked((uint)totalElements));
                RegisterNewObject(size);
            }
            return result;
        }

        [ManualRefCounts]
        internal override String AllocateString(int stringLength,
                                                Thread currentThread)
        {
            String result = base.AllocateString(stringLength, currentThread);
            if (VTable.enableGCProfiling) {
                ulong size = (ulong)
                    ObjectLayout.StringSize(vtable,
                                            unchecked((uint)(stringLength+1)));
                RegisterNewObject(size);
            }
            return result;
        }

#endregion

#region Accounting

        internal override void RegisterHeapSize(ulong heapSize)
        {
            base.RegisterHeapSize(heapSize);
            if (minHeapSize < heapSize) {
                minHeapSize = heapSize;
            }
            lastLiveHeapSize = heapSize;
            bytesSinceGC = 0;
        }

        internal override void RegisterNewObject(ulong objectSize)
        {
            base.RegisterNewObject(objectSize);
            bytesAllocated += objectSize;
            objectsAllocated++;
            if (VTable.enableGCAccurateHeapSize) {
                bytesSinceGC += objectSize;
                if (lastLiveHeapSize + bytesSinceGC > minHeapSize) {
                    GC.Collect();
                }
            }
        }

        internal override void PrintAllocations()
        {
            if (VTable.enableGCProfiling) {
#if !SINGULARITY
                Console.Error.WriteLine("Objects allocated: "+
                                        objectsAllocated);
                Console.Error.WriteLine("Total bytes allocated (KB): "+
                                        (bytesAllocated >> 10));
                Console.Error.WriteLine("Min. heap size (KB): "+
                                        (minHeapSize >> 10));
#endif
            }
            base.PrintAllocations();
        }

        private  static ulong       lastLiveHeapSize;
        private  static ulong       minHeapSize;
        private  static ulong       bytesSinceGC;
        private  static ulong       bytesAllocated;
        private  static ulong       objectsAllocated;

#endregion

    }

}
