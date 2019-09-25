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

    using Microsoft.Bartok.Runtime;
    using System.Runtime.CompilerServices;
    using System.Threading;

    internal abstract class CopyScan
    {

        protected PageType pageType;
        protected BumpAllocator allocator;

        internal virtual void Initialize(PageType pageType)
        {
            this.pageType = pageType;
            this.allocator = new BumpAllocator(pageType);
        }

        internal abstract void Cleanup();

        internal virtual void TruncateAllocationArea()
        {
            this.allocator.Truncate();
        }

        protected abstract bool HaveWork { get; }

        protected abstract void AddWork(UIntPtr start, UIntPtr limit);

        protected abstract UIntPtr GetWork(out UIntPtr value2);

        internal Object Copy(Object obj)
        {
            UIntPtr size = ObjectLayout.Sizeof(obj);
            if (GenerationalGCData.IsLargeObjectSize(size)) {
                return CopyLarge(obj, size);
            } else {
                return CopySmall(obj, size);
            }
        }

        private Object CopyLarge(Object obj, UIntPtr size)
        {
            // Don't copy large objects.
            // Change the page type instead.
            UIntPtr startAddr = Magic.addressOf(obj) - PreHeader.Size;
            UIntPtr startPage = PageTable.Page(startAddr);
            UIntPtr endPage = PageTable.Page(startAddr+size-1)+1;
            VTable.Assert(this.pageType ==
                          PageTable.ZombieToLive(PageTable.Type(startPage)));
            PageTable.SetType(startPage, (endPage - startPage),
                              this.pageType);
            UIntPtr sizeOfPages = PageTable.PageSize * (endPage-startPage);
            Trace.Log(Trace.Area.Pointer,
                      "FwdRef: large object: {0} gen: {1} pagesize: {2}",
                      __arglist(Magic.addressOf(obj), this.pageType,
                                sizeOfPages));
            GenerationalGCData.gcPromotedTable[(int)this.pageType-1] +=
                sizeOfPages;
            this.AddWork(startAddr, startAddr + size);
            return obj;
        }

        private unsafe Object CopySmall(Object obj, UIntPtr size)
        {
            uint alignment = obj.vtable.baseAlignment;
            UIntPtr newObjectAddr =
                this.allocator.AllocateFast(size, alignment);
            if (newObjectAddr == UIntPtr.Zero) {
                int threadIndex = StopTheWorldGCData.collectorThreadIndex;
                Thread thread = Thread.threadTable[threadIndex];
                UIntPtr oldAllocNew = this.allocator.AllocNew;
                newObjectAddr =
                    this.allocator.AllocateSlow(size, alignment, thread);
                UIntPtr allocNew = this.allocator.AllocNew;
                if (oldAllocNew != allocNew) {
                    UIntPtr limitPtr = this.allocator.ReserveLimit;
                    this.NewAllocationRange(newObjectAddr, allocNew, limitPtr);
                }
            }
            this.NewObject(newObjectAddr, size);
            UIntPtr srcAddr = Magic.addressOf(obj) - PreHeader.Size;
            UIntPtr dstAddr = newObjectAddr - PreHeader.Size;
            Trace.Log(Trace.Area.Pointer,
                      "FwdRef: {0} -> {1}, gen={2}, size={3}",
                      __arglist(Magic.addressOf(obj), newObjectAddr,
                                this.pageType, size));
            VTable.Assert(this.pageType ==
                          PageTable.Type(PageTable.Page(dstAddr)));
            GenerationalGCData.gcPromotedTable[(int)this.pageType-1] +=
                size;
            Util.MemCopy(dstAddr, srcAddr, size);
            *obj.VTableFieldAddr = newObjectAddr;
            return Magic.fromAddress(newObjectAddr);
        }

        protected abstract void NewAllocationRange(UIntPtr objectAddr,
                                                   UIntPtr rangeStart,
                                                   UIntPtr rangeLimit);

        protected abstract void NewObject(UIntPtr objAddr, UIntPtr size);

        [Inline]
        internal abstract bool Scan(NonNullReferenceVisitor visitor);

    }

    internal abstract class CopyScanQueue : CopyScan
    {

        private UIntPtrQueue workList;

        internal override void Initialize(PageType pageType)
        {
            base.Initialize(pageType);
            this.workList = new UIntPtrQueue();
        }

        protected override bool HaveWork{
            get { return !this.workList.IsEmpty; }
        }

        protected override void AddWork(UIntPtr start, UIntPtr limit)
        {
            this.workList.Write(start, limit);
        }

        protected override UIntPtr GetWork(out UIntPtr value2)
        {
            return this.workList.Read(out value2);
        }

        internal override void Cleanup()
        {
            this.workList.Cleanup(false);
        }

    }
        

    internal abstract class CopyScanStack : CopyScan
    {

        private UIntPtrStack workList;

        internal override void Initialize(PageType pageType)
        {
            base.Initialize(pageType);
            this.workList = new UIntPtrStack();
        }

        protected override bool HaveWork {
            get { return !this.workList.IsEmpty; }
        }

        protected override void AddWork(UIntPtr start, UIntPtr limit)
        {
            this.workList.Write(start, limit);
        }

        protected override UIntPtr GetWork(out UIntPtr value2)
        {
            return this.workList.Read(out value2);
        }

        internal override void Cleanup()
        {
            this.workList.Cleanup(false);
        }

    }
        

    internal class CheneyScan : CopyScanQueue
    {

        private UIntPtr destinationLow;
        private UIntPtr destinationHigh;

        protected override void NewAllocationRange(UIntPtr objectAddr,
                                                   UIntPtr rangeStart,
                                                   UIntPtr rangeLimit)
        {
            if (rangeStart != destinationHigh) {
                // Switching to a new allocation range
                if (destinationLow != destinationHigh) {
                    this.AddWork(destinationLow, destinationHigh);
                }
                destinationLow = rangeStart;
            }
            destinationHigh = rangeLimit;
        }

        protected override void NewObject(UIntPtr objAddr, UIntPtr size)
        {
            // We don't need to do anything for individual objects
        }

        [Inline]
        internal override bool Scan(NonNullReferenceVisitor visitor)
        {
            bool localRepeat = false;
            bool globalRepeat = false;
            while (true) {
                while (this.HaveWork) {
                    localRepeat = true;
                    UIntPtr lowAddr, highAddr;
                    lowAddr = this.GetWork(out highAddr);
                    lowAddr += PreHeader.Size;
                    lowAddr =
                        BumpAllocator.SkipNonObjectData(lowAddr, highAddr);
                    while (lowAddr < highAddr) {
                        Object obj = Magic.fromAddress(lowAddr);
                        lowAddr += visitor.VisitReferenceFields(obj);
                        lowAddr =
                            BumpAllocator.SkipNonObjectData(lowAddr, highAddr);
                    }
                }
                if (this.destinationLow != this.allocator.AllocPtr) {
                    localRepeat = true;
                    UIntPtr lowAddr = this.destinationLow;
                    UIntPtr highAddr = this.allocator.AllocPtr;
                    this.destinationLow = highAddr;
                    this.AddWork(lowAddr, highAddr);
                }
                if (!localRepeat) {
                    // Exit the loop if we have done nothing this time around
                    break;
                }
                globalRepeat = true;
                localRepeat = false;
            }
            return globalRepeat;
        }

        internal override void Initialize(PageType pageType)
        {
            base.Initialize(pageType);
            this.destinationLow = UIntPtr.Zero;
            this.destinationHigh = UIntPtr.Zero;
        }

        internal override void Cleanup()
        {
            VTable.Assert(!this.HaveWork, "Cheney Scan: work left at cleanup");
            base.Cleanup();
        }

        internal override void TruncateAllocationArea()
        {
            UIntPtr lowAddr = this.destinationLow;
            UIntPtr highAddr = this.allocator.AllocPtr;
            if (lowAddr != highAddr) {
                this.AddWork(lowAddr, highAddr);
            }
            base.TruncateAllocationArea();
            this.destinationLow = UIntPtr.Zero;
            this.destinationHigh = UIntPtr.Zero;
        }
    }

    internal class HierarchicalScan : CopyScanQueue
    {

        private UIntPtr destinationLow;
        private UIntPtr destinationHigh;
        private UIntPtr sourceHigh;

        protected override unsafe void NewAllocationRange(UIntPtr objectAddr,
                                                          UIntPtr rangeStart,
                                                          UIntPtr rangeLimit)
        {
            UIntPtr preObjectAddr = objectAddr - PreHeader.Size;
            if (preObjectAddr >= destinationLow &&
                preObjectAddr <= destinationHigh) {
                // Extending the current allocation range
                VTable.Assert(rangeStart == destinationHigh);
                if (destinationLow != preObjectAddr) {
                    this.AddWork(destinationLow, preObjectAddr);
                }
            } else {
                // Switching to a new allocation range
                if (destinationLow != destinationHigh) {
                    this.AddWork(destinationLow, destinationHigh);
                }
            }
            this.sourceHigh = UIntPtr.Zero;
            destinationLow = preObjectAddr;
            destinationHigh = rangeLimit;
        }

        protected override void NewObject(UIntPtr objAdr, UIntPtr size)
        {
            // We don't need to do anything for individual objects
        }

        [Inline]
        internal override bool Scan(NonNullReferenceVisitor visitor)
        {
            bool globalRepeat = false;
            while (true) {
                UIntPtr lowAddr, highAddr;
                if (this.destinationLow != this.allocator.AllocPtr) {
                    lowAddr = this.destinationLow;
                    highAddr = this.allocator.AllocPtr;
                    this.destinationLow = highAddr;
                } else if (!this.HaveWork) {
                    // No more work to do
                    break;
                } else {
                    lowAddr = this.GetWork(out highAddr);
                }
                globalRepeat = true;
                this.sourceHigh = highAddr;
                lowAddr += PreHeader.Size;
                lowAddr =
                    BumpAllocator.SkipNonObjectData(lowAddr, highAddr);
                while (lowAddr < this.sourceHigh) {
                    Object obj = Magic.fromAddress(lowAddr);
                    lowAddr += visitor.VisitReferenceFields(obj);
                    lowAddr =
                        BumpAllocator.SkipNonObjectData(lowAddr, highAddr);
                }
                if (lowAddr < highAddr) {
                    // The scanning must have been aborted early due to
                    // overflow into a new page.  Put the rest of the
                    // range on the work list.
                    this.AddWork(lowAddr - PreHeader.Size, highAddr);
                }
            }
            return globalRepeat;
        }

        internal override void Initialize(PageType pageType)
        {
            base.Initialize(pageType);
            this.destinationLow = UIntPtr.Zero;
            this.destinationHigh = UIntPtr.Zero;
        }

        internal override void Cleanup()
        {
            VTable.Assert(!this.HaveWork,
                          "Hierarchical Scan: work left at cleanup");
            base.Cleanup();
        }

        internal override void TruncateAllocationArea()
        {
            UIntPtr lowAddr = this.destinationLow;
            UIntPtr highAddr = this.allocator.AllocPtr;
            if (lowAddr != highAddr) {
                this.AddWork(lowAddr, highAddr);
            }
            base.TruncateAllocationArea();
            this.destinationLow = UIntPtr.Zero;
            this.destinationHigh = UIntPtr.Zero;
        }
    }

    internal class NestedHierarchicalScan : CopyScanStack
    {

        protected UIntPtr destinationLow;
        protected UIntPtr destinationHigh;
        protected UIntPtr sourceHigh;

        protected override unsafe void NewAllocationRange(UIntPtr objectAddr,
                                                          UIntPtr rangeStart,
                                                          UIntPtr rangeLimit)
        {
            // BUGBUG:
        }

        protected override void NewObject(UIntPtr objAddr, UIntPtr size)
        {
            // BUGBUG:
        }

        [Inline]
        internal override bool Scan(NonNullReferenceVisitor visitor)
        {
            // BUGBUG:
            return false;
        }

        internal override void TruncateAllocationArea()
        {
            // BUGBUG:
        }

    }

}
