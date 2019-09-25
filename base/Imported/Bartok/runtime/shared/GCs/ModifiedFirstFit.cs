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

    using System.Threading;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    internal class ModifiedFirstFit {
        private const uint minimumBlockSize = 12;

        private static UIntPtr osCommitSize;

        private UIntPtr head;
        private UIntPtr tail;
        private UIntPtr last;

        private UIntPtr totalMemory;

        [PreInitRefCounts]
        internal static void Initialize() {
            osCommitSize = MemoryManager.OperatingSystemCommitSize;
            UIntPtr heapCommitSize = new UIntPtr(1 << 20);
            VTable.Assert(heapCommitSize > osCommitSize,
                          @"heapCommitSize > osCommitSize");

            PageManager.Initialize(osCommitSize, heapCommitSize);
        }

        [Inline]
        [ManualRefCounts]
        internal UIntPtr AllocateBlock(UIntPtr blockSize,
                                       Thread t) {
            UIntPtr prev;

            if (head == UIntPtr.Zero) { // Free list exhausted
                                        // or no free list yet.
                prev = growFreeList(blockSize, t);
            } else {
                VTable.Assert(tail >= head,
                              @"tail >= head");

                // Perform a first-fit search from the last
                // free block that served up an allocation
                // request, or the free block after that if
                // it was fully served (next fit).

                prev = last;

                UIntPtr desiredBlockSize = blockSize+minimumBlockSize;

                while (getBlockSize(prev) < desiredBlockSize) {
                    prev = getNextBlock(prev);

                    if (prev == last) { // Search has wrapped around.
                        prev = growFreeList(blockSize, t);
                        break;
                    }
                }
            }

            // At this point, either the block pointed by "prev"
            // has a size that exceeds the requested size by
            // at least "minimumBlockSize", or precedes a block
            // whose size equals the requested size or exceeds
            // it by at least "minimumBlockSize".

            UIntPtr prevBlockSize = getBlockSize(prev);
            VTable.Assert(prevBlockSize >= blockSize+
                          minimumBlockSize ||
                          getBlockSize(getNextBlock(prev)) ==
                          blockSize ||
                          getBlockSize(getNextBlock(prev)) >=
                          blockSize+minimumBlockSize,
                          @"prevBlockSize >= blockSize+
                          minimumBlockSize ||
                          getBlockSize(getNextBlock(prev)) ==
                          blockSize ||
                          getBlockSize(getNextBlock(prev)) >=
                          blockSize+minimumBlockSize");

            UIntPtr resultAddr;

            if (prevBlockSize >=
                blockSize+minimumBlockSize) { // Break block.
                setBlockSize(prev, prevBlockSize-blockSize);
                resultAddr = prev+(prevBlockSize-blockSize);
                last = prev;
            } else { // Process request from the next block.
                UIntPtr curr = getNextBlock(prev);
                UIntPtr currBlockSize = getBlockSize(curr);

                if (currBlockSize >= blockSize+minimumBlockSize) {
                    setBlockSize(curr, currBlockSize-blockSize);
                    resultAddr = curr+(currBlockSize-blockSize);
                    last = curr;
                } else { // Return entire block.
                    VTable.Assert(currBlockSize == blockSize,
                                  @"currBlockSize == blockSize");

                    resultAddr = curr;
                    if (prev == curr) { // Free list becomes empty.
                        head = UIntPtr.Zero;
                        tail = UIntPtr.Zero;
                        last = UIntPtr.Zero;
                    } else { // Skip a block in the free list.
                        if (curr == head) {
                            curr = getNextBlock(curr);
                            setNextBlock(prev, curr);
                            head = curr;
                        } else if (curr == tail) {
                            curr = head;
                            setNextBlock(prev, curr);
                            tail = prev;
                        } else {
                            curr = getNextBlock(curr);
                            setNextBlock(prev, curr);
                        }
                        last = curr;
                    }
                }
            }

            // Wipe out old contents.
            Util.MemClear(resultAddr, blockSize);

            // Adjust memory audit figure.
            totalMemory -= blockSize;

            return resultAddr;
        }

        // Free lists used in this implementation have the invariant
        // that their blocks are linked in increasing order of
        // addresses. FreeBlock preserves this invariant. It also
        // coalesces the inserted block with abutting free blocks.
        //
        // It returns the block just before the point of insertion.

        [Inline]
        [ManualRefCounts]
        internal UIntPtr FreeBlock(UIntPtr block, UIntPtr size) {
            VTable.Assert(block != UIntPtr.Zero,
                          @"block != UIntPtr.Zero");
            VTable.Assert(head <= tail,
                          @"head <= tail");
            VTable.Assert(size > 0,
                          @"size > 0");

            // Adjust memory audit figure.
            totalMemory += size;

            UIntPtr below;

            if (block < head) {
                VTable.Assert(head != UIntPtr.Zero,
                              @"head != UIntPtr.Zero");
                VTable.Assert(tail != UIntPtr.Zero,
                              @"tail != UIntPtr.Zero");
                VTable.Assert(block+size <= head,
                              @"block+size <= head");

                if (block+size == head) {
                    setBlockSize(block, size+getBlockSize(head));

                    if (head == tail) {
                        tail = block;
                    } else {
                        setNextBlock(block, getNextBlock(head));
                    }
                    if (last == head) {
                        last = block;
                    }
                } else {
                    setBlockSize(block, size);
                    setNextBlock(block, head);
                }
                below = tail;
                setNextBlock(below, block);
                head = block;
            } else if (head == UIntPtr.Zero) {
                VTable.Assert(tail == UIntPtr.Zero,
                              @"tail == UIntPtr.Zero");
                VTable.Assert(last == UIntPtr.Zero,
                              @"last == UIntPtr.Zero");

                tail = block;
                setBlockSize(block, size);
                setNextBlock(block, block);
                below = block;
                head = block;
                last = block;
            } else if (block > tail) {
                VTable.Assert(tail != UIntPtr.Zero,
                              @"tail != UIntPtr.Zero");

                below = tail;
                UIntPtr lastBlockSize = getBlockSize(below);
                VTable.Assert(below+lastBlockSize <= block,
                              @"below+lastBlockSize <= block");

                if (below+lastBlockSize == block) {
                    setBlockSize(below, lastBlockSize+size);
                } else {
                    setNextBlock(below, block);
                    setBlockSize(block, size);
                    setNextBlock(block, head);
                    tail = block;
                }
            } else {
                VTable.Assert(UIntPtr.Zero < head,
                              @"UIntPtr.Zero < head");
                VTable.Assert(head < block,
                              @"head < block");
                VTable.Assert(block < tail,
                              @"block < tail");

                // UIntPtr.Zero < head < block < tail.

                // The blocks referenced by "below" and "above"
                // ultimately straddle the inserted block.

                below = head;
                UIntPtr above = getNextBlock(below);

                while (above < block) {
                    below = above;
                    above = getNextBlock(below);
                }
                // At this point, below < block < above.
                VTable.Assert(below < block,
                              @"below < block");
                VTable.Assert(below+getBlockSize(below) <= block,
                              @"below+getBlockSize(below) <= block");
                VTable.Assert(block < above,
                              @"block < above");
                VTable.Assert(block+size <= above,
                              @"block+size <= above");

                // Coalesce blocks if possible.

                if (block+size == above) {
                    size += getBlockSize(above);
                    setBlockSize(block, size);
                    if (tail == above) {
                        tail = block;
                    }
                    if (last == above) {
                        last = block;
                    }
                    above = getNextBlock(above);
                } else {
                    setBlockSize(block, size);
                }
                setNextBlock(block, above);

                UIntPtr belowBlockSize = getBlockSize(below);
                if (below+belowBlockSize == block) {
                    setBlockSize(below, belowBlockSize+size);
                    setNextBlock(below, above);
                    if (tail == block) {
                        tail = below;
                    }
                    if (last == block) {
                        last = below;
                    }
                } else {
                    setNextBlock(below, block);
                }
            }

            return below;
        }

        internal UIntPtr TotalMemory {
            [Inline]
            [ManualRefCounts]
            get {
                 return totalMemory;
            }
        }

        [Inline]
        [ManualRefCounts]
        internal unsafe void CheckConsistency() {
            if (head == UIntPtr.Zero) {
                VTable.Assert(tail == UIntPtr.Zero,
                              @"tail == UIntPtr.Zero");
            } else if (tail == UIntPtr.Zero) {
                VTable.Assert(head == UIntPtr.Zero,
                              @"head == UIntPtr.Zero");
            } else {
                VTable.Assert(head <= tail,
                              @"head <= tail");
                VTable.Assert(getNextBlock(tail) == head,
                              @"getNextBlock(tail) == head");

                UIntPtr leastBlockSize = new UIntPtr(2*sizeof(uint));

                UIntPtr block = head;
                while (block != tail) {
                    UIntPtr blockSize = getBlockSize(block);
                    UIntPtr nextBlock = getNextBlock(block);

                    VTable.Assert(blockSize >= leastBlockSize,
                                  @"blockSize >= leastBlockSize");
                    VTable.Assert(block+blockSize < nextBlock,
                                  @"block+blockSize < nextBlock");

                    block = nextBlock;
                }

                VTable.Assert(getBlockSize(block) >= leastBlockSize,
                              @"getBlockSize(block) >= leastBlockSize");
            }
        }

        // Grow free list by allocating and inserting a block of
        // size at least "blockSize".

        [Inline]
        [ManualRefCounts]
        private UIntPtr growFreeList(UIntPtr blockSize, Thread t) {
            UIntPtr pageCount = PageTable.PageCount(blockSize);
            bool fCleanPages = true;
            UIntPtr startPage = PageManager.EnsurePages(t, pageCount,
                                                        PageType.Owner0,
                                                        ref fCleanPages);
            UIntPtr newBlockSize = PageTable.RegionSize(pageCount);
            UIntPtr newBlockAddr = PageTable.PageAddr(startPage);

            return FreeBlock(newBlockAddr, newBlockSize);
        }


        // Layout of a free block:
        //
        //        Low address ------> High address
        //        --------------------------------
        //        |   |   |                       |
        //        | A | B |                       |
        //        |   |   |                       |
        //        --------------------------------
        //        <-----------  size  ----------->
        //
        // A: UIntPtr field that contains a UIntPtr to the next block
        //    on the free list.
        //
        // B: UIntPtr field that contains the size of the free block.

        private unsafe static UIntPtr getNextBlock(UIntPtr block) {
            return *((UIntPtr*)block+0);
        }

        private unsafe static void setNextBlock(UIntPtr block,
                                                UIntPtr nextBlock) {
            *((UIntPtr*)block+0) = nextBlock;
        }

        private unsafe static UIntPtr getBlockSize(UIntPtr block) {
            return *((UIntPtr*)block+1);
        }

        private unsafe static void setBlockSize(UIntPtr block,
                                                UIntPtr size) {
            *((UIntPtr*)block+1) = size;
        }
    }
}
