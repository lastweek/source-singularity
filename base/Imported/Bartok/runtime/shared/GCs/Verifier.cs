//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

//#define DEBUG_OFFSETTABLE

namespace System.GCs {

    using Microsoft.Bartok.Runtime;
    using System.Threading;
    using System.Runtime.CompilerServices;

    [CCtorIsRunDuringStartup]
    internal class Verifier
    {

        internal abstract class StackVerifier {

            internal abstract
            void Verify(NonNullReferenceVisitor threadReferenceVisitor,
                        Thread thread);

        }

        private NonNullReferenceVisitor referenceVisitor;
        private NonNullReferenceVisitor threadReferenceVisitor;
        private ObjectLayout.ObjectVisitor objectVisitor;
        private StackVerifier stackVerifier;

        internal static readonly NonNullReferenceVisitor genericReferenceVisitor;
        internal static readonly ObjectLayout.ObjectVisitor genericObjectVisitor;
        internal static readonly NonNullReferenceVisitor genericThreadReferenceVisitor;
        internal static readonly StackVerifier genericStackVerifier;
        internal static readonly Verifier bumpAllocatorVerifier;
        internal static readonly Verifier segregatedFreeListVerifier;

        static Verifier() {
            genericReferenceVisitor = new GenericReferenceVisitor();
            genericThreadReferenceVisitor =
                new GenericThreadReferenceVisitor();
            genericObjectVisitor =
                new GenericObjectVisitor(genericReferenceVisitor);
            genericStackVerifier = new GenericStackVerifier();
            bumpAllocatorVerifier = new Verifier(genericReferenceVisitor,
                                                 genericThreadReferenceVisitor,
                                                 genericObjectVisitor,
                                                 genericStackVerifier);
            segregatedFreeListVerifier =
                new Verifier(genericReferenceVisitor,
                             genericThreadReferenceVisitor,
                             new SegregatedFreeList.ObjectVisitorWrapper(genericObjectVisitor),
                             genericStackVerifier);
        }

        internal Verifier(NonNullReferenceVisitor referenceVisitor,
                          NonNullReferenceVisitor threadReferenceVisitor,
                          ObjectLayout.ObjectVisitor objectVisitor,
                          StackVerifier stackVerifier) {
            this.referenceVisitor = referenceVisitor;;
            this.threadReferenceVisitor = threadReferenceVisitor;
            this.objectVisitor = objectVisitor;
            this.stackVerifier = stackVerifier;
        }

        public void VerifyHeap() {
            // Temporarily set the thread allocation point to the unused
            // space token, if necessary.
            Thread currentThread = Thread.CurrentThread;
            VerifyAllThreadsGCControlled(currentThread);
            // Do the real work
            VerifyPages(this.objectVisitor);
            StaticData.ScanStaticData(this.referenceVisitor);
            VTable.Deny(PageTable.IsUnusedPage(PageTable.Page(Magic.addressOf(Thread.threadTable))));
            for (int i = 0; i < Thread.threadTable.Length; i++) {
                Thread t = Thread.threadTable[i];
                if (t != null) {
                    VTable.Deny(PageTable.IsUnusedPage(PageTable.Page(Magic.addressOf(t))));
                      this.stackVerifier.Verify(this.threadReferenceVisitor,
                                                t);
                }
            }
        }

        private static void VerifyAllThreadsGCControlled(Thread thread) {
            int limit = Thread.threadTable.Length;
            for (int i = 0; i < limit; i++) {
                Thread t = Thread.threadTable[i];
                if (t != null && t != thread) {
#if !SINGULARITY
                    VTable.Assert(Transitions.UnderGCControl(t.threadIndex));
#endif
                }
            }
        }

        //=========================================
        // Verification of heap and page management

        internal static
        void VerifyPages(ObjectLayout.ObjectVisitor objectVisitor)
        {
            UIntPtr page = UIntPtr.Zero;
            while (page < PageTable.pageTableCount) {
                UIntPtr startPage = page;
                if (!PageTable.IsMyPage(startPage)) {
                    page++;
                    continue;
                }
                PageType pageType = PageTable.Type(page);
                uint pageProcess = PageTable.Process(page);
                do {
                    page++;
                } while (page < PageTable.pageTableCount &&
                         PageTable.Type(page) == pageType &&
                         PageTable.Process(page) == pageProcess);
                UIntPtr endPage = page;
                switch (pageType) {
                  case PageType.Unallocated:
                  case PageType.Unknown:
                  case PageType.Shared: {
                      // The region does not belong to us, so there is
                      // nothing to check.
                      break;
                  }
                  case PageType.UnusedClean:
                  case PageType.UnusedDirty: {
                      PageManager.VerifyUnusedRegion(startPage, endPage);
                      break;
                  }
                  case PageType.System: {
                      // We have looked at the region, but it is off-limits
                      // for the verifier.
                      break;
                  }
                  case PageType.NonGC: {
                      // Since there may be non-objects in the static data
                      // pages, we cannot apply the heapVerifier to the
                      // region.
                      break;
                  }
                  case PageType.Stack: {
                      // The page contains (part of) the activation record
                      // stack for one or more threads.
                      break;
                  }
                  default: {
                      // We have found a data region
                      VTable.Assert(PageTable.IsGcPage(startPage));
                      UIntPtr startAddr = PageTable.PageAddr(startPage);
                      UIntPtr endAddr = PageTable.PageAddr(endPage);
                      GC.installedGC.VisitObjects(objectVisitor,
                                                  startAddr, endAddr);
                      break;
                  }
                }
            }
        }

        private class GenericReferenceVisitor : NonNullReferenceVisitor
        {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsGcPage(pageType)) {
                    VTable.Assert(PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType));
                    return;
                }
                VTable.Assert(PageTable.IsMyPage(page));
                UIntPtr objectAddr = GC.installedGC.FindObjectAddr(addr);
                VTable.Assert(objectAddr == addr);
                UIntPtr vtableAddr =
                    Magic.addressOf(Magic.fromAddress(objectAddr).vtable);
                VTable.Assert(PageTable.IsNonGcPage(PageTable.Type(PageTable.Page(vtableAddr))));
                VTable.Assert(Magic.fromAddress(vtableAddr) is VTable);
            }

        }

        internal class GenericThreadReferenceVisitor : NonNullReferenceVisitor
        {

            internal unsafe override void Visit(UIntPtr *loc) {
                UIntPtr addr = *loc;
                UIntPtr page = PageTable.Page(addr);
                PageType pageType = PageTable.Type(page);
                if (!PageTable.IsGcPage(pageType)) {
                    VTable.Assert(PageTable.IsNonGcPage(pageType) ||
                                  PageTable.IsStackPage(pageType) ||
                                  PageTable.IsSharedPage(pageType));
                    return;
                }
                VTable.Assert(PageTable.IsMyPage(page));
                UIntPtr objectAddr = GC.installedGC.FindObjectAddr(addr);
                VTable.Assert(objectAddr <= addr);
                UIntPtr vtableAddr =
                    Magic.addressOf(Magic.fromAddress(objectAddr).vtable);
                VTable.Assert(PageTable.IsNonGcPage(PageTable.Type(PageTable.Page(vtableAddr))));
                VTable.Assert(Magic.fromAddress(vtableAddr) is VTable);
            }

        }

        internal class GenericObjectVisitor : ObjectLayout.ObjectVisitor {

            private NonNullReferenceVisitor referenceVisitor;
#if DEBUG_OFFSETTABLE
            private static UIntPtr lastObjPtr;
#endif                     

            internal
            GenericObjectVisitor(NonNullReferenceVisitor referenceVisitor)
            {
                this.referenceVisitor = referenceVisitor;
#if DEBUG_OFFSETTABLE
                lastObjPtr = UIntPtr.Zero;
#endif                     
            }

            internal override UIntPtr Visit(Object obj) {
#if DEBUG_OFFSETTABLE
                VTable.DebugPrint("visit obj {0:x8}\n", __arglist(Magic.addressOf(obj))); 
                if (lastObjPtr != UIntPtr.Zero) {
                     UIntPtr lastCard = CardTable.CardNo(lastObjPtr);
                     if (lastCard != CardTable.CardNo(Magic.addressOf(obj))) {
                        if (!OffsetTable.NoObjectPtrToTheCard(lastCard)) {
                              UIntPtr realOffst = lastObjPtr - CardTable.CardAddr(lastCard);
                              UIntPtr currOffst = OffsetTable.GetOffset(lastCard);
                              if (realOffst != currOffst ) {
                                 VTable.DebugPrint("Verifier: wrong offset. Card {0:x8} Offset {1:x8} Should be {2:x8}\n",
                                       __arglist(lastCard, currOffst, realOffst));
                                 VTable.Assert(false);
                              }
                         }
                     }
                }    
#endif                     
                return this.referenceVisitor.VisitReferenceFields(obj);
            }

        }

        internal class GenericStackVerifier : StackVerifier {

            internal override
            void Verify(NonNullReferenceVisitor threadReferenceVisitor,
                        Thread thread)
            {
                CallStack.ScanStack(thread, threadReferenceVisitor,
                                    threadReferenceVisitor);
            }

        }

    }

}
