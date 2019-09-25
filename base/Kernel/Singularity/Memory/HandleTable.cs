//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: HandleTable.cs - Shared region for process handles
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;

using Microsoft.Bartok.Runtime;

using Microsoft.Singularity;

namespace Microsoft.Singularity.Memory
{
    // <summary>
    // Reference-counted handles to object references that aren't garbage
    // collected so they can be handed out across GC domains.  The receiving
    // process is handle an actual pointer into the handle table.  We know
    // that the process can't forge a non-null pointer due to type safety.
    // Handle table pages for a process are not freed until the process
    // terminates because we hand out pointer within the page to the process.
    //
    // Each page of handles (and therefore each handle) is owned by one process.
    // The pages for a process may be quickly found and deleted upon
    // process death.  "Normal" handles never move between processes.
    // Handles related to endpoints can move between processes, but
    // they are owned by the kernel and cleaned up with reference counting
    // since we know that points to handles in channels can never leak.
    //
    // </summary>
    [NoCCtor]
    [CLSCompliant(false)]
    internal class HandleTable {

#if ISA_ARM
        [AccessedByRuntime("Referenced in interlocked.cpp")]
#endif
        internal struct HandlePage
        {
            private UIntPtr                 table;
            internal unsafe HandlePage *    next;

            [Inline]
            internal void SetTable(HandleTable ht)
            {
                table = Magic.addressOf(ht);
            }

            [Inline]
            internal HandleTable GetTable()
            {
                return (HandleTable)Magic.fromAddress(table);
            }
        }

#if ISA_ARM
        [AccessedByRuntime("Referenced in interlocked.cpp")]
#endif
        internal struct HandleEntry {
            internal UIntPtr                item;
            internal unsafe HandleEntry *   next;   // next free node, null if last or in use.

            [Inline]
            internal void Set(Object o)
            {
                item = Magic.addressOf(o);
            }

            [Inline]
            [NoHeapAllocation]
            internal Object Get()
            {
                return Magic.fromAddress(item);
            }

            [Inline]
            internal unsafe void Visit(DirectReferenceVisitor visitor)
            {
                if (item != UIntPtr.Zero) {
                    fixed (UIntPtr *loc = &item) {
                        visitor.Visit(loc);
                    }
                }
            }

        }

        // Per-class members
        private static int handlesPerPage;

        internal static unsafe void Initialize()
        {
            handlesPerPage = (int)((MemoryManager.PageSize / sizeof(HandleEntry)) - 1);
        }

        internal static void Finalize()
        {
        }

        internal static unsafe HandleTable FindOwner(HandleEntry *entry)
        {
            HandlePage * page = (HandlePage *)MemoryManager.PageAlign((UIntPtr)entry);
            return page->GetTable();
        }

        [Inline]
        internal static unsafe void SetHandle(UIntPtr handle, Object obj)
        {
            HandleEntry *entry = (HandleEntry *)handle;
            entry->Set(obj);
        }

        [Inline]
        internal static unsafe void ClrHandle(UIntPtr handle)
        {
            HandleEntry *entry = (HandleEntry *)handle;
            entry->Set(null);
        }

        [Inline]
        [NoHeapAllocation]
        internal static unsafe Object GetHandle(UIntPtr handle)
        {
            HandleEntry *entry = (HandleEntry *)handle;
            return entry->Get();
        }

        // Per-instance members
        private Process process;
        private unsafe HandlePage *    pages;
        private unsafe HandleEntry *   freeList;
        private int pageCount;

        internal unsafe HandleTable(Process process)
        {
            pages = null;
            freeList = null;
        }

        internal unsafe void VisitSpecialData(DirectReferenceVisitor visitor)
        {
            HandlePage *limit = null;
            HandlePage *began;
            do {
                // Repeat this loop as long as new pages appear.
                // REVIEW: I'm not sure this is needed, the write barrier might
                // take care of this for us.
                began = pages;
                for (HandlePage *page = began; page != limit; page = page->next) {

                    // Get the bounds.
                    HandleEntry *entry = ((HandleEntry *)(page + 1));
                    HandleEntry *elimit = entry + handlesPerPage;

                    for (; entry < elimit; entry++) {
                        entry->Visit(visitor);
                    }
                }
                limit = pages;
            } while (pages != began);
        }

        internal unsafe UIntPtr FreeAllPages()
        {
            // We assume that external code has insured thread safety.
            freeList = null;

            for (HandlePage *next; pages != null; pages = next) {
                next = pages->next;

                MemoryManager.KernelFree((UIntPtr)pages, 1, process);
            }

            return (UIntPtr)pageCount * MemoryManager.PageSize;
        }

        internal unsafe void FreeHandle(UIntPtr handle)
        {
            if (handle != UIntPtr.Zero) {
                FreeEntry((HandleEntry *)handle);
            }
        }

        internal unsafe void FreeEntry(HandleEntry *entry)
        {
            entry->Set(null);

            HandleEntry *next;
            do {
                next = freeList;
                entry->next = next;

                // Interlocked.CompareExchange only updates freeList if it hasn't
                // changed within this loop.
            } while (next != Interlocked.CompareExchange(ref freeList, entry, next));
        }

        internal unsafe UIntPtr AllocateHandle()
        {
            return (UIntPtr)AllocateEntry();
        }

        internal unsafe HandleEntry * AllocateEntry()
        {
            HandleEntry * entry = AllocateExisting();
            if (entry != null) {
                return entry;
            }

#if SINGULARITY_KERNEL
            Kernel.Waypoint(830);
#endif // SINGULARITY_KERNEL
            // Need to allocate a new page.
            HandlePage *page
                = (HandlePage*)MemoryManager.KernelAllocate(
                    1, process, 0, PageType.Shared);

#if SINGULARITY_KERNEL
            Kernel.Waypoint(831);
#endif // SINGULARITY_KERNEL

            if (page == null) {
                return null;
            }

            // Get the bounds.
            HandleEntry *beg = ((HandleEntry *)(page + 1));
            HandleEntry *end = beg + handlesPerPage - 1;

            // Save off the first entry to return.
            entry = beg++;
            entry->Set(null);
            entry->next = null;

            // Initialize the free list in the rest of the entries.
            for (HandleEntry *step = beg; step < end; step++) {
                step->Set(null);
                step->next = step + 1;
            }
            end->Set(null);
            end->next = null;

            // Initialize the page header and insert into the page list.
            page->SetTable(this);
            page->next = null;
            HandlePage *last;
            do {
                last = pages;
                page->next = last;

                // Interlocked.CompareExchange only updates pages if it hasn't
                // changed within this loop.
            } while (last != Interlocked.CompareExchange(ref pages, page, last));

            // Then insert into the free list.
            HandleEntry *next;
            do {
                next = freeList;
                end->next = next;

                // Interlocked.CompareExchange only updates freeList if it hasn't
                // changed with this loop.
            } while (next != Interlocked.CompareExchange(ref freeList, beg, next));

            Interlocked.Increment(ref pageCount);

            return entry;
        }

        internal unsafe HandleEntry * AllocateExisting()
        {
            HandleEntry * first;
            HandleEntry * second;

            do {
                //
                // Cache the contents of head pointer location (i.e. the
                // address of the first element on the list).
                //
                first = freeList;

                if (first == null) {
                    //
                    // No first element.  List is empty.
                    //
                    return null;
                }

                //
                // The first element contains the address of the second.
                //
                second = first->next;

                //
                // Called this way, Interlocked.CompareExchange will only
                // replace the contents of the head pointer location with
                // the address of the second element if the contents of the
                // the head pointer location (i.e. the first element's address)
                // hasn't changed since we cached it.  If the contents of
                // the head pointer have changed in the meantime, it means
                // some other thread has popped that element off the stack.
                // So we loop back and try it all over again.
                //

            } while (first != Interlocked.CompareExchange(ref freeList, second, first));

            first->Set(null);
            first->next = null;
            return first;
        }

        [NoHeapAllocation]
        internal int GetPageCount()
        {
            return pageCount;
        }
    }
}
