//
// Copyright (c) Microsoft Corporation. All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

// #define DEBUG

namespace System.GCs {

  using Microsoft.Bartok.Options;
  using Microsoft.Bartok.Runtime;
  using System.Runtime.InteropServices;
  using System.Runtime.CompilerServices;
  using System.Threading;
  using System.Collections;

  [RequiredByBartok]
  internal class TrialDeletion {
      [PreInitRefCounts]
      public static void Initialize() {
          Object plcLinkObj = BootstrapMemory.Allocate(typeof(PLCLink));
          firstPLCLink =
              (PLCLink*)(Magic.addressOf(plcLinkObj)+PostHeader.Size);
          plcListVtable = ((RuntimeType)typeof(PLCLink[])).classVtable;
          plcListChunkBytes =
              ObjectLayout.ArraySize(plcListVtable, plcListChunkLength);
      }


      /*
       * Reserve bits in the RS field for marking purposes,
       * and for flagging acyclic objects.
       */
      [MixinConditional("TrialDeletion")]
      [Mixin(typeof(RCCollector.RSMasks))]
      internal new struct RSMasks {
          internal const uint markFlag =                0x40000000;
          internal const uint acyclicFlag =             0x20000000;
      }

      [MixinConditional("TrialDeletion")]
      [Mixin(typeof(Microsoft.Bartok.Runtime.PreHeader))]
      internal unsafe struct PreHeader {
          internal PLCLink* plcLink;
      }

      // Each link in the "potentially leaked cycles" list.
      internal unsafe struct PLCLink {
          // The next link in the list of potentially leaked cycles.
          public PLCLink* next;

          // Address of an object lying on a potentially leaked cycle;
          public UIntPtr objAddr;
      }

      private static unsafe PLCLink* getPLCLink(Object obj) {
          return ((PreHeader)(obj.preHeader)).plcLink;
      }

      private static unsafe void setPLCLink(Object obj, PLCLink* link) {
          ((PreHeader)(obj.preHeader)).plcLink = link;
      }

      private static InternalIncrementer internalIncrementer;
      private static InternalDecrementer internalDecrementer;
      private static InternalScanner internalScanner;
      private static InternalReclaimer internalReclaimer;

      private static PLCLink* firstPLCLink;
      private static VTable plcListVtable;
      private static UIntPtr plcListChunkBytes;
      private static PLCLink* plcListChunk;
      private static uint numPLCChunks;

      private const uint plcListChunkLength = 1 << 12;
      private const uint maxPLCChunks = 256;

      private static ulong maxCyclicGarbage;
      private static ulong totalCyclicGarbage;
      private static uint cycleCollections;
      private static bool forceCycleCollectionAtEnd {
          get { return false; }
      }

      [PreInitRefCounts]
      public static unsafe void Initialize() {
          internalIncrementer =
              (InternalIncrementer)BootstrapMemory.
              Allocate(typeof(InternalIncrementer));
          internalDecrementer =
              (InternalDecrementer)BootstrapMemory.
              Allocate(typeof(InternalDecrementer));
          internalScanner =
              (InternalScanner)BootstrapMemory.
              Allocate(typeof(InternalScanner));
          internalReclaimer =
              (InternalReclaimer)BootstrapMemory.
              Allocate(typeof(InternalReclaimer));
      }


      [Inline]
      [ManualRefCounts]
      private static unsafe void addToPLCList(Object obj) {
          // Check if free PLC links are available.
          if (plcListChunk == null) {
              if (numPLCChunks < maxPLCChunks) {
                  // Allocate a chunk of PLC links.
                  int threadIndex = Thread.GetCurrentThreadIndex();
                  Thread t = Thread.threadTable[threadIndex];
                  UIntPtr resultAddr =
                      t.segregatedFreeList.
                      Allocate(plcListChunkBytes,
                               plcListVtable.baseAlignment);
                  Object result = Magic.fromAddress(resultAddr);
                  result.REF_STATE = 2 & ~countingONFlagMask;
                  result.vtable = plcListVtable;
                  numPLCChunks++;

                  // Point <plcListChunk> to the first element
                  // in the allocated array of PLC links and string
                  // the elements into a free PLC links' list.
                  plcListChunk = (PLCLink*)
                      (resultAddr+PostHeader.Size+UIntPtr.Size);
                  for (PLCLink* link = plcListChunk;
                       link < plcListChunk+
                       plcListChunkLength-1;
                       link++) {
                      link->next = link+1;
                  }
              } else {
                  processPLCList();
              }
          }
          VTable.Assert(plcListChunk != null,
                        @"plcListChunk != null");

          // Insert object into the PLC list by moving a link
          // from the free PLC links' chunk.
          firstPLCLink->objAddr = Magic.addressOf(obj);
          PLCLink* currPLCLink = plcListChunk;
          plcListChunk = plcListChunk->next;
          currPLCLink->next = firstPLCLink;
          firstPLCLink = currPLCLink;
          firstPLCLink->objAddr = UIntPtr.Zero;

          // Point the object to its link in the PLC list.
          setPLCLink(obj, firstPLCLink);
      }

      [ManualRefCounts]
      private static unsafe void removeFromPLCList(PLCLink* pLinkAddr) {
          // The object needs to be removed from the PLC list.
          PLCLink* currPLCLink = pLinkAddr;
#if DEBUG
          VTable.Assert(currPLCLink->next != null,
                        @"currPLCLink->next != null");
#endif // DEBUG

          PLCLink* linkToSkip = currPLCLink->next;
          PLCLink* linkAfter = linkToSkip->next;
          currPLCLink->next = linkAfter;
          linkToSkip->next = plcListChunk;
          plcListChunk = linkToSkip;

          // Update the PLC link pointer in the following object.
          if (linkAfter != null) {
              UIntPtr nextObjAddr = linkAfter->objAddr;
              Object nextObj = Magic.fromAddress(nextObjAddr);
#if DEBUG
              VTable.Assert(getPLCLink(nextObj) == linkToSkip,
                            @"getPLCLink(nextObj) == linkToSkip");
#endif // DEBUG

              setPLCLink(nextObj, currPLCLink);
          }
      }

      [ManualRefCounts]
      private static unsafe void processPLCList() {
          int startTicks = 0;
          bool enableGCTiming = VTable.enableGCTiming;
          if (enableGCTiming) {
              VTable.enableGCTiming = false;
              startTicks = Environment.TickCount;
          }
          if (VTable.enableGCWatermarks) {
              MemoryAccounting.RecordHeapWatermarks();
          }

#if DEBUG
          VTable.Assert(firstPLCLink->objAddr == UIntPtr.Zero,
                        @"firstPLCLink->objAddr == UIntPtr.Zero");
#endif // DEBUG

          // Let S be the subgraph of heap objects reachable from
          // the PLC list. Decrement counts due to references in S.
          for (PLCLink* link = firstPLCLink->next; link != null;
               link = link->next) {
              UIntPtr objAddr = link->objAddr;
              VTable.Assert(objAddr != UIntPtr.Zero,
                            @"objAddr != UIntPtr.Zero");

              Object obj = Magic.fromAddress(objAddr);
              VTable.Assert((obj.REF_STATE &
                             countingONFlagMask) != 0,
                            @"(obj.REF_STATE &
                               countingONFlagMask) != 0");

              uint refState = obj.REF_STATE;
              if ((refState & markFlagMask) == 0) {
                  obj.REF_STATE = refState | markFlagMask;
                  internalDecrementer.Traverse(objAddr);
              }
          }

          // Objects that now have non-zero counts are those that
          // have references external to S incident on them.
          // Recompute counts due to reachability from such objects.
          for (PLCLink* link = firstPLCLink->next; link != null;
               link = link->next) {
              UIntPtr objAddr = link->objAddr;
              internalScanner.Traverse(objAddr);
          }

          // String together objects with reference count
          // of zero for reclamation.
          internalReclaimer.Initialize();
          for (PLCLink* link = firstPLCLink->next; link != null;
               link = link->next) {
              UIntPtr objAddr = link->objAddr;
              internalReclaimer.Traverse(objAddr);
          }
          ulong reclaimedBytes = 0;
          Object reclaimedObj = internalReclaimer.ReclaimedObjects;
          while (reclaimedObj != null) {
              if (VTable.enableGCProfiling) {
                  UIntPtr size = ObjectLayout.Sizeof(reclaimedObj);
                  reclaimedBytes += (ulong)size;
              }
              Object nextReclaimedObj = getNextLink(reclaimedObj);
              SegregatedFreeList.Free(reclaimedObj);
              reclaimedObj = nextReclaimedObj;
          }

          // Recycle the PLC list.
          if (firstPLCLink->next != null) {
              PLCLink* lastPLCLink = firstPLCLink;
              do {
                  lastPLCLink = lastPLCLink->next;
              } while (lastPLCLink->next != null);
              lastPLCLink->next = plcListChunk;
              plcListChunk = firstPLCLink->next;
              firstPLCLink->next = null;
          }

          // Release the memory used up by work lists.
          UIntPtrQueue.ReleaseStandbyPages(null);

          SegregatedFreeList.RecycleGlobalPages();
          SegregatedFreeList.CommitFreedData();
          GC.newBytesSinceGC = UIntPtr.Zero;

          if (enableGCTiming) {
              int elapsedTicks = Environment.TickCount - startTicks;
              System.GC.gcTotalTime += elapsedTicks;
              if (System.GC.maxPauseTime < elapsedTicks) {
                  System.GC.maxPauseTime = elapsedTicks;
              }
              System.GC.pauseCount++;
              VTable.enableGCTiming = true;
          }

          if (VTable.enableGCProfiling) {
              if (maxCyclicGarbage < reclaimedBytes) {
                  maxCyclicGarbage = reclaimedBytes;
              }
              totalCyclicGarbage += reclaimedBytes;
              cycleCollections++;
          }
      }


      private class InternalDecrementer : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal void Traverse(UIntPtr objAddr) {
              Object obj = Magic.fromAddress(objAddr);
              this.VisitReferenceFields(obj);
              while (!this.workList.IsEmpty) {
                  objAddr = this.workList.Read();
                  obj = Magic.fromAddress(objAddr);
                  this.VisitReferenceFields(obj);
              }
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);
              uint refState = obj.REF_STATE;
              if ((refState & countingONFlagMask) == 0) {
                  return;
              }
              uint refCount = refState & refCountMask;
              VTable.Assert(refCount > 0,
                            @"refCount > 0");

              refState--;
              if ((refState & markFlagMask) != 0) {
                  obj.REF_STATE = refState;
              } else {
                  obj.REF_STATE = refState | markFlagMask;
                  this.workList.Write(objAddr);
              }
          }

          private UIntPtrQueue workList;
      }

      private class InternalScanner : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal unsafe void Traverse(UIntPtr objAddr) {
              this.Visit(&objAddr);
              while (!this.workList.IsEmpty) {
                  objAddr = this.workList.Read();
                  Object obj = Magic.fromAddress(objAddr);
                  this.VisitReferenceFields(obj);
              }
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);
              uint refState = obj.REF_STATE;
              if ((refState & countingONFlagMask) == 0 ||
                  (refState & markFlagMask) == 0) {
                  return;
              }
              obj.REF_STATE = refState & ~markFlagMask;

              uint refCount = refState & refCountMask;
              if (refCount > 0) {
                  // This object isn't leaked data, so
                  // clear the PLC link in its header.
                  setPLCLink(obj, null);
                  internalIncrementer.Traverse(objAddr);
              } else {
                  this.workList.Write(objAddr);
              }
          }

          private UIntPtrQueue workList;
      }

      private class InternalIncrementer : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal void Traverse(UIntPtr objAddr) {
              Object obj = Magic.fromAddress(objAddr);
              this.VisitReferenceFields(obj);
              while (!this.workList.IsEmpty) {
                  objAddr = this.workList.Read();
                  obj = Magic.fromAddress(objAddr);
                  this.VisitReferenceFields(obj);
              }
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);
              uint refState = obj.REF_STATE;
              if ((refState & countingONFlagMask) == 0) {
                  return;
              }
              uint refCount = refState & refCountMask;
              VTable.Assert(refCount < refCountMask,
                            @"refCount < refCountMask");

              refState++;
              if ((refState & markFlagMask) != 0) {
                  // The object hasn't been visited either
                  // by the scanner or the incrementer.
                  obj.REF_STATE = refState & ~markFlagMask;
                  this.workList.Write(objAddr);
                  // This object isn't leaked data, so
                  // clear the PLC link in its header.
                  setPLCLink(obj, null);
              } else if ((refState & refCountMask) == 1) {
                  // The object has been visited in the
                  // past, but only by the scanner.
                  obj.REF_STATE = refState;
                  this.workList.Write(objAddr);
                  // This object isn't leaked data, so
                  // clear the PLC link in its header.
                  setPLCLink(obj, null);
              } else {
                  obj.REF_STATE = refState;
#if DEBUG
                  // The PLC link in this object's header
                  // should already be cleared.
                  PLCLink* pLinkAddr = getPLCLink(obj);
                  VTable.Assert(pLinkAddr == null,
                                @"pLinkAddr == UIntPtr.Zero");
#endif // DEBUG
              }
          }

          private UIntPtrQueue workList;
      }

      private class InternalReclaimer : NonNullReferenceVisitor {
          internal Object ReclaimedObjects;

          [ManualRefCounts]
          internal void Initialize() {
              this.ReclaimedObjects = null;
          }

          [ManualRefCounts]
          internal unsafe void Traverse(UIntPtr objAddr) {
              this.Visit(&objAddr);
              while (!this.workList.IsEmpty) {
                  objAddr = this.workList.Read();
                  Object obj = Magic.fromAddress(objAddr);
                  this.VisitReferenceFields(obj);
              }
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);
              uint refState = obj.REF_STATE;
              if ((refState & countingONFlagMask) == 0) {
                  return;
              }
              uint refCount = refState & refCountMask;
              if (refCount == 0) {
                  setNextLink(obj, this.ReclaimedObjects);
                  obj.REF_STATE = ~countingONFlagMask;
                  this.ReclaimedObjects = obj;
                  this.workList.Write(objAddr);
              }
          }

          private UIntPtrQueue workList;
      }
  }
}
