////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PhysicalHeap.cs - a simple heap
//
//  Note:
//
//  This heap manages physical memory so as to be able to satisfy requests
//  for blocks of contiguous memory. This is used for the restricted
//  purpose of allocating I/O memory to processes that need, for example,
//  to perform DMA to hardware.
//
//  The implementation of the heap assumes that the contiguous range of
//  memory that it is pointed to at initialization is always mapped.
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;

using Microsoft.Singularity;

namespace Microsoft.Singularity.Memory
{
    [NoCCtor]
    [CLSCompliant(false)]
    public struct PhysicalHeap
    {
        /////////////////////////////////////
        // CONSTANTS
        /////////////////////////////////////

        // We maintain a table of our heap's available pages, one 16-bit
        // half-word per page. The 16 bits simply indicate the PID of the
        // process owning the page, or zero if the page is free.
        private const uint BytesPerTableEntry = 2;
        private const ushort FreePage = 0x0000;
        private const ushort KernelPage = 0x0001;

        /////////////////////////////////////
        // FIELDS
        /////////////////////////////////////

        // When allocating block of this size or smaller, we will
        // start from the tail of the freeList instead of the head.
        // The freeList is kept sorted by size.
        private const uint    SmallSize = MemoryManager.PageSize;

        // The start and end of heap pages *that can be used for data*
        // (the page table resides immediately *before* this range!)
        private UIntPtr startAddr;
        private UIntPtr heapLimit;

        // A count of the *data pages* in the heap (doesn't count the
        // pages consumed by the page table)
        private UIntPtr pageCount;

        // The address of the page table
        private unsafe ushort* pageTable;

        // Protects access to the heap
        private SpinLock heapLock;

        // A chained list of free blocks, sorted by block size.
        private FreeList freeList;


        /////////////////////////////////////
        // PUBLIC METHODS
        /////////////////////////////////////

        public unsafe PhysicalHeap(UIntPtr start, UIntPtr limit)
        {
            DebugStub.Assert(MemoryManager.IsPageAligned(start));
            DebugStub.Assert(MemoryManager.IsPageAligned(limit));

            // Note that this wastes a little bit of memory by allocating
            // table space to describe page-table memory!
            UIntPtr numPages = MemoryManager.PagesFromBytes(limit - start);
            UIntPtr bytesForTable = numPages * BytesPerTableEntry;
            bytesForTable = MemoryManager.PagePad(bytesForTable);
            UIntPtr pagesForTable = MemoryManager.PagesFromBytes(bytesForTable);

            pageCount = numPages - pagesForTable;
            startAddr = start  + bytesForTable;
            heapLimit = limit;
            pageTable = (ushort*)start;
            heapLock = new SpinLock(SpinLock.Types.PhysicalHeap);

            // The entire heap is free to start out with
            freeList = new FreeList();

            // Initialize the page table
            SetPages(startAddr, pageCount, FreePage);

            fixed (PhysicalHeap* thisPtr = &this) {
                freeList.CreateAndInsert(thisPtr, startAddr, pageCount);
            }

            CheckConsistency();
        }

        // We always hand out blocks consisting of complete
        // pages of memory.
        [NoStackLinkCheckTrans]
        public unsafe UIntPtr Allocate(UIntPtr bytes, Process process)
        {
            return Allocate(0, bytes, 0, process);
        }

        [NoStackLinkCheckTrans]
        public unsafe UIntPtr Allocate(UIntPtr limitAddr,
                                       UIntPtr bytes,
                                       UIntPtr alignment,
                                       Process process)
        {
            ushort tag = process != null ? (ushort)process.ProcessId : KernelPage;
            UIntPtr blockPtr;
            bool iflag = Lock();

            if (alignment < MemoryManager.PageSize) {
                alignment = MemoryManager.PageSize;
            }

            try {
                CheckConsistency();

                // Find an appropriately-sized block
                FreeNode *foundNode = freeList.FindGoodFit(bytes, alignment);

                if (foundNode == null) {
                    return UIntPtr.Zero;
                }

                DebugStub.Assert(MemoryManager.IsPageAligned((UIntPtr)foundNode));

                // Respect alignment within the node
                blockPtr = MemoryManager.Pad((UIntPtr)foundNode, alignment);
                UIntPtr alignedSize = bytes + SpaceToAlign((UIntPtr)foundNode, alignment);
                DebugStub.Assert(alignedSize == (blockPtr + bytes) - (UIntPtr)foundNode);
                DebugStub.Assert(foundNode->bytes >= alignedSize);

                // Give back any extra pages
                UIntPtr numPages = MemoryManager.PagesFromBytes(MemoryManager.PagePad(alignedSize));
                UIntPtr chunkPages = MemoryManager.PagesFromBytes(foundNode->bytes);

                DebugStub.Assert(chunkPages >= numPages);
                UIntPtr extraPages = chunkPages - numPages;

                if (extraPages > 0) {
                    // Give back the extra memory
                    UIntPtr remainderPtr = (UIntPtr)foundNode + (numPages * MemoryManager.PageSize);

                    fixed (PhysicalHeap* thisPtr = &this) {
                        freeList.CreateAndInsert(thisPtr, remainderPtr, extraPages);
                    }
                }

                SetPages((UIntPtr)foundNode, numPages, tag);
                CheckConsistency();
            }
            finally {
                Unlock(iflag);
            }

            // TODO: Flexible limit specification not yet implemented
            if (limitAddr > UIntPtr.Zero) {
                DebugStub.Assert(blockPtr < limitAddr);
            }

            return blockPtr;
        }

        [NoStackLinkCheckTrans]
        public unsafe void Free(UIntPtr addr, UIntPtr bytes, Process process)
        {
            if (addr == UIntPtr.Zero) {
                // Silently accept freeing null
                return;
            }

            // We always hand out memory in page-size chunks, so round up what
            // the caller thinks their block size is
            bytes = MemoryManager.PagePad(bytes);

            // Our blocks always start on page boundaries
            DebugStub.Assert(MemoryManager.IsPageAligned(addr));
            ushort tag = process != null ? (ushort)process.ProcessId : KernelPage;
            bool iflag = Lock();

            try {
                CheckConsistency();

                UIntPtr numPages = MemoryManager.PagesFromBytes(bytes);
                VerifyOwner(addr, numPages, tag);

                FreeNode *nextBlock = null;
                FreeNode *prevBlock = null;

                if ((addr + bytes) < heapLimit) {
                    fixed (PhysicalHeap* thisPtr = &this) {
                        nextBlock = FreeNode.GetNodeAt(thisPtr, addr + bytes);
                    }
                }

                if (addr > startAddr) {
                    fixed (PhysicalHeap* thisPtr = &this) {
                        prevBlock = LastNode.GetNodeFromLast(thisPtr, addr - MemoryManager.PageSize);
                    }
                }

                // Don't mark pages as free until we're done discovering the
                // previous and next blocks, or the attempt to discover
                // the previous and next blocks gets confused to find itself
                // adjacent to a free block.
                SetPages(addr, numPages, FreePage);

                // Coalesce with the preceding region
                if (prevBlock != null) {
                    addr = (UIntPtr)prevBlock;
                    bytes += prevBlock->bytes;
                    freeList.Remove(prevBlock);
                }

                // Coalesce with the following region
                if (nextBlock != null) {
                    bytes += nextBlock->bytes;
                    freeList.Remove(nextBlock);
                }

                // Blocks should always be integral numbers of pages
                DebugStub.Assert(MemoryManager.IsPageAligned(bytes));

                // Create the free node.
                fixed (PhysicalHeap* thisPtr = &this) {
                    freeList.CreateAndInsert(thisPtr, addr, bytes / MemoryManager.PageSize);
                }

                CheckConsistency();
            }
            finally {
                Unlock(iflag);
            }
        }

        /////////////////////////////////////
        // PRIVATE METHODS
        /////////////////////////////////////

        private unsafe UIntPtr FreePageCountFromList()
        {
            UIntPtr retval = 0;
            FreeNode* entry = freeList.head;
            FreeNode* prev = null;

            while (entry != null) {
                DebugStub.Assert(MemoryManager.IsPageAligned(entry->bytes));
                retval += MemoryManager.PagesFromBytes(entry->bytes);
                DebugStub.Assert(entry->prev == prev);
                prev = entry;
                entry = entry->next;
            }

            return retval;
        }

        private unsafe void CheckConsistency()
        {
#if SELF_TEST
            UIntPtr freePagesByTable = 0;

            for (UIntPtr i = 0; i < pageCount; i++) {
                UIntPtr pageAddr = startAddr + (MemoryManager.PageSize * i);

                if (PageWord(i) == FreePage) {
                    // Validate this block's free information
                    FreeNode* thisBlock = (FreeNode*)pageAddr;
                    DebugStub.Assert(thisBlock->signature == FreeNode.Signature);

                    if (thisBlock->last != null) {
                        // Multi-page free block; validate and skip ahead
                        DebugStub.Assert(thisBlock->last->node == thisBlock);
                        DebugStub.Assert(thisBlock->last->signature == LastNode.Signature);
                        UIntPtr numBytes = (UIntPtr)thisBlock->last - (UIntPtr)pageAddr +
                            MemoryManager.PageSize;
                        DebugStub.Assert(numBytes == thisBlock->bytes);
                        DebugStub.Assert(MemoryManager.IsPageAligned(numBytes));
                        UIntPtr numPages = MemoryManager.PagesFromBytes(numBytes);

                        for (UIntPtr j = i; j < i + numPages; j++) {
                            DebugStub.Assert(PageWord(j) == FreePage);
                        }

                        i += numPages - 1;
                        freePagesByTable += numPages;

                    }
                    else {
                        // Single-page free block
                        if (i != pageCount - 1) {
                            DebugStub.Assert(PageWord(i + 1) != FreePage);
                        }
                        freePagesByTable++;
                    }
                }
            }

            // Now make sure all free pages are accounted for
            UIntPtr freePagesByList = FreePageCountFromList();
            DebugStub.Assert(freePagesByList == freePagesByTable);
#endif
        }

        [NoStackLinkCheckTrans]
        private unsafe void SetPages(UIntPtr addr, UIntPtr pageCount, ushort tag)
        {
            UIntPtr idx = PageIndex(addr);
            ushort* descriptor = pageTable + (ulong)idx;

            while (pageCount > 0) {
                *descriptor++ = tag;
                pageCount--;
            }
        }

        [NoStackLinkCheckTrans]
        private unsafe void VerifyOwner(UIntPtr addr, UIntPtr pages, ushort tag)
        {
            UIntPtr idx = PageIndex(addr);

            for (UIntPtr i = 0; i < pages; i++) {
                DebugStub.Assert
                    ((*(pageTable + (ulong)idx + (ulong)i)) == tag,
                     "PhysicalHeap.VerifyOwner addr={0} i={1} tag={2}",
                     __arglist(addr, i, tag));
            }
        }

        [Inline]
        private UIntPtr PageIndex(UIntPtr pageAddr)
        {
            DebugStub.Assert(MemoryManager.IsPageAligned(pageAddr));
            DebugStub.Assert(pageAddr >= startAddr && pageAddr <= heapLimit,
                             "PhysicalHeap.PageIndex pageAddr = {0:x} Range = {1:x} ... {2:x}",
                             __arglist(pageAddr, startAddr, heapLimit));
            DebugStub.Assert(pageAddr < heapLimit);

            return MemoryManager.PagesFromBytes(pageAddr - startAddr);
        }

        [Inline]
        private unsafe ushort PageWord(UIntPtr pageIdx)
        {
            DebugStub.Assert(pageIdx < pageCount,
                             "PhysicalHeap.PageWord pageIdx {0} >= pageCount {1}",
                             __arglist(pageIdx, pageCount));
            return *(pageTable + (ulong)pageIdx);
        }

        [NoStackLinkCheckTrans]
        private bool Lock()
        {
            bool enabled = Processor.DisableInterrupts();
#if SINGULARITY_MP
            heapLock.Acquire(Thread.CurrentThread);
#endif // SINGULARITY_MP
            return enabled;
        }

        [NoStackLinkCheckTrans]
        private void Unlock(bool iflag)
        {
#if SINGULARITY_MP
            heapLock.Release(Thread.CurrentThread);
#endif // SINGULARITY_MP
            Processor.RestoreInterrupts(iflag);
        }

        /////////////////////////////////////
        // HELPER CLASSES
        /////////////////////////////////////

        [StructLayout(LayoutKind.Sequential)]
        private struct FreeList
        {
            internal unsafe FreeNode* head;
            internal unsafe FreeNode* tail;

            [NoStackLinkCheckTrans]
            internal unsafe void CreateAndInsert(PhysicalHeap* inHeap,
                                                 UIntPtr addr,
                                                 UIntPtr pages)
            {
                DebugStub.Assert(MemoryManager.IsPageAligned(addr),
                                 "PhysicalHeap.CreateAndInsert non page-aligned addr={0:x}",
                                 __arglist(addr));

                FreeNode * node = FreeNode.Create(inHeap, addr, pages);

                DebugStub.Assert(MemoryManager.IsPageAligned(node->bytes),
                                 "PhysicalHeap.CreateAndInsert non page-sized node->bytes={0:x}",
                                 __arglist(node->bytes));

                InsertBySize(node);
            }

            internal unsafe void Remove(FreeNode* node)
            {
                if (node->prev != null) {
                    node->prev->next = node->next;
                }
                else {
                    DebugStub.Assert(head == node);
                    head = node->next;
                }

                if (node->next != null) {
                    node->next->prev = node->prev;
                }
                else {
                    DebugStub.Assert(tail == node);
                    tail = node->prev;
                }

                node->Remove();
            }

            private unsafe void InsertAsHead(FreeNode* node)
            {
                if (head != null) {
                    head->prev = node;
                }

                node->next = head;
                head = node;
            }

            private unsafe void InsertAsTail(FreeNode* node)
            {
                if (tail != null) {
                    tail->next = node;
                }

                node->prev = tail;
                tail = node;
            }

            private unsafe void InsertAsNext(FreeNode* target, FreeNode* node)
            {
                DebugStub.Assert(target != null);

                if (target == tail) {
                    InsertAsTail(node);
                }
                else {
                    node->next = target->next;
                    node->prev = target;
                    target->next = node;

                    if (node->next != null) {
                        node->next->prev = node;
                    }
                }
            }

            private unsafe void InsertAsPrev(FreeNode* target, FreeNode* node)
            {
                DebugStub.Assert(target != null);

                if (target == head) {
                    InsertAsHead(node);
                }
                else {
                    node->prev = target->prev;
                    node->next = target;
                    target->prev = node;

                    if (node->prev != null) {
                        node->prev->next = node;
                    }
                }
            }

            [NoStackLinkCheckTrans]
            internal unsafe void InsertBySize(FreeNode* node)
            {
                if (head == null) {
                    // Empty list
                    DebugStub.Assert(tail == null);
                    head = node;
                    tail = node;
                }
                else {
                    if (node->bytes <= SmallSize) {
                        // If the size is pretty small, we insert from the back of the list...
                        for (FreeNode *step = tail; step != null; step = step->prev) {
                            if (step->bytes >= node->bytes) {
                                InsertAsNext(step, node);
                                return;
                            }
                        }

                        // Every entry in the list is smaller than us. Therefore, we're the
                        // new head.
                        InsertAsHead(node);
                    }
                    else {
                        // Insert a region into the list by size.
                        for (FreeNode *step = head; step != null; step = step->next) {
                            if (step->bytes <= node->bytes) {
                                InsertAsPrev(step, node);
                                return;
                            }
                        }

                        // Every entry in the list is larger than us. Therefore, we're
                        // the new tail.
                        InsertAsTail(node);
                    }
                }
            }

            [NoStackLinkCheckTrans]
            internal unsafe FreeNode * FindGoodFit(UIntPtr bytes, UIntPtr alignment)
            {
                DebugStub.Assert(alignment >= MemoryManager.PageSize);

                // If it is a small allocation, we try to accelerate the search.
                if (bytes <= SmallSize) {
                    for (FreeNode *node = tail; node != null; node = node->prev) {
                        UIntPtr alignedSize = SpaceToAlign((UIntPtr)node, alignment) + bytes;

                        if (alignedSize <= node->bytes) {
                            Remove(node);
                            return node;
                        }
                    }

                    return null;
                }
                else {
                    // First try to find a region closest in size to bytes...
                    FreeNode *best = null;

                    for (FreeNode *node = head; node != null; node = node->next) {
                        UIntPtr alignedSize = SpaceToAlign((UIntPtr)node, alignment) + bytes;

                        if (alignedSize <= node->bytes) {
                            // If we find a candidate, remember it.
                            best = node;
                            if (bytes == node->bytes) {
                                // Stop if it is the ideal region.
                                break;
                            }
                        }
                        else {
                            // Stop if we've reached smaller regions
                            break;
                        }
                    }

                    if (best != null) {
                        Remove(best);
                    }

                    return best;
                }
            }
        }

        [Inline]
        private static UIntPtr SpaceToAlign(UIntPtr data, UIntPtr size)
        {
            return MemoryManager.Pad(data, size) - data;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct FreeNode
        {
            internal const uint Signature   = 0x22aaaa22;
            internal const uint Removed     = 0x11eeee11;

            internal uint signature;
            internal unsafe FreeNode * prev;
            internal unsafe FreeNode * next;
            internal unsafe LastNode * last;
            internal UIntPtr bytes;

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * Create(PhysicalHeap* inHeap,
                                                     UIntPtr addr, UIntPtr pages)
            {
                DebugStub.Assert(addr >= inHeap->startAddr);
                DebugStub.Assert((addr + (pages * MemoryManager.PageSize)) <= inHeap->heapLimit);
                FreeNode * node = (FreeNode *)addr;

                // This had better be a free page in the main table
                DebugStub.Assert(inHeap->PageWord(inHeap->PageIndex(addr)) == FreePage,
                                 "Creating a FreeNode for non-free page {0:x}",
                                 __arglist(addr));

                node->signature = FreeNode.Signature;
                node->bytes = pages * MemoryManager.PageSize;
                node->prev = null;
                node->next = null;
                node->last = null;

                if (pages > 1) {
                    node->last = LastNode.Create(inHeap, addr, node);
                }

                return node;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * GetNodeAt(PhysicalHeap* inHeap,
                                                        UIntPtr addr)
            {
                UIntPtr idx = inHeap->PageIndex(addr);

                if (inHeap->PageWord(idx) != FreePage) {
                    // This address designates a page that is in use.
                    return null;
                }

                if ((idx > 0) && (inHeap->PageWord(idx - 1) == FreePage)) {
                    // This address is in the middle of a free block; it does
                    // not designate the beginning of a free block.
                    return null;
                }

                DebugStub.Assert(((FreeNode*)addr)->signature == Signature);
                return (FreeNode*)addr;
            }

            internal unsafe void Remove()
            {
                signature = Removed;

                prev = null;
                next = null;

                if (last != null) {
                    last->Remove();
                }
            }
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct LastNode
        {
            internal const uint Signature   = 0xaa2222aa;
            internal const uint Removed     = 0xee1111ee;

            internal uint signature;
            internal unsafe FreeNode * node;

            [NoStackLinkCheckTrans]
            internal static unsafe LastNode * Create(PhysicalHeap* inHeap,
                                                     UIntPtr addr, FreeNode *node)
            {
                LastNode *last = (LastNode *)(addr + node->bytes - MemoryManager.PageSize);
                DebugStub.Assert((UIntPtr)last >= inHeap->startAddr);
                DebugStub.Assert((UIntPtr)last <= inHeap->heapLimit);
                DebugStub.Assert(MemoryManager.IsPageAligned((UIntPtr)last));
                last->signature = LastNode.Signature;
                last->node = node;
                return last;
            }

            [NoStackLinkCheckTrans]
            internal unsafe void Remove()
            {
                signature = Removed;
                node = null;
            }

            [NoStackLinkCheckTrans]
            internal static unsafe FreeNode * GetNodeFromLast(PhysicalHeap* inHeap,
                                                              UIntPtr addr)
            {
                UIntPtr idx = inHeap->PageIndex(addr);

                // addr must specify a free page
                if (inHeap->PageWord(idx) != FreePage) {
                    // addr does not specify a LastNode
                    return null;
                }

                // addr must specify a page such that the next page (if there
                // is one) is not free
                if ((idx != inHeap->pageCount - 1) &&
                     (inHeap->PageWord(idx + 1) == FreePage)) {
                    return null;
                }

                if (idx == 0) {
                    // This is a one-page block
                    DebugStub.Assert(((FreeNode*)addr)->signature == FreeNode.Signature);
                    return (FreeNode*)addr;
                }

                // If the preceding page is free, then addr specifies
                // the last page in a multi-page block, otherwise it
                // specifies the only page in a one-page block.
                if (inHeap->PageWord(idx - 1) == FreePage) {
                    DebugStub.Assert(((LastNode*)addr)->signature == Signature);
                    return ((LastNode *)addr)->node;
                }
                else {
                    DebugStub.Assert(((FreeNode*)addr)->signature == FreeNode.Signature);
                    return (FreeNode*)addr;
                }
            }
        }
    }
}
