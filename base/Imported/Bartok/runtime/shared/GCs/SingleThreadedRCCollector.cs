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

  [NoCCtor]
  [RequiredByBartok]
  internal abstract class SingleThreadedRCCollector : RCCollector {
      [PreInitRefCounts]
      public new static void Initialize() {
          RCCollector.Initialize();

          if (VerificationMode) {
              backupInit =
                  (BackupInitializer)BootstrapMemory.
                  Allocate(typeof(BackupInitializer));
              backupRefCount =
                  (BackupRefCount)BootstrapMemory.
                  Allocate(typeof(BackupRefCount));
              incrementBackupRefCount =
                  (IncrementBackupRefCount)BootstrapMemory.
                  Allocate(typeof(IncrementBackupRefCount));
              rootsScanner =
                  (RootsScanner)BootstrapMemory.
                  Allocate(typeof(RootsScanner));
              resetRoots =
                  (ResetRoots)BootstrapMemory.
                  Allocate(typeof(ResetRoots));
              resetTraversal =
                  (ResetTraversal)BootstrapMemory.
                  Allocate(typeof(ResetTraversal));

              leakAccumulator =
                  (LeakAccumulator)BootstrapMemory.
                  Allocate(typeof(LeakAccumulator));
              leakedNodesDFS =
                  (LeakedNodesDFS)BootstrapMemory.
                  Allocate(typeof(LeakedNodesDFS));
              leakedCycleClosure =
                  (LeakedCycleClosure)BootstrapMemory.
                  Allocate(typeof(LeakedCycleClosure));
              dfsMarker =
                  (DFSMarker)BootstrapMemory.
                  Allocate(typeof(DFSMarker));
              cycleClosure =
                  (CycleClosure)BootstrapMemory.
                  Allocate(typeof(CycleClosure));
              bfsMarker =
                  (BFSMarker)BootstrapMemory.
                  Allocate(typeof(BFSMarker));
              leakedRoots =
                  (LeakedRoots)BootstrapMemory.
                  Allocate(typeof(LeakedRoots));
              leakedRootsCounter =
                  (LeakedRootsCounter)BootstrapMemory.
                  Allocate(typeof(LeakedRootsCounter));
          }
      }

      internal override bool IsOnTheFlyCollector {
          get {
              return false;
          }
      }

      internal override void CheckForNeededGCWork
          (Thread currentThread) {
      }

      internal override int GetGeneration(Object obj) {
          return MinGeneration;
      }

      internal override int MinGeneration {
          get {
              return (int)PageType.Owner0;
          }
      }

      internal override int MaxGeneration {
          get {
              return (int)PageType.Owner0;
          }
      }

      internal override int CollectionGeneration(int gen) {
          return MinGeneration;
      }

      internal override void NewThreadNotification(Thread newThread,
                                                   bool initial)
      {
          base.NewThreadNotification(newThread, initial);
          SegregatedFreeList.NewThreadNotification(newThread, initial);
      }

      internal override void DeadThreadNotification(Thread deadThread)
      {
          MultiUseWord.CollectFromThread(deadThread);
          SegregatedFreeList.DeadThreadNotification(deadThread);
          base.DeadThreadNotification(deadThread);
      }

      [NoInline]
      [ManualRefCounts]
      protected void preVerifyHeap(bool beforeCollection) {
          VTable.Assert(RCCollector.VerificationMode,
                        @"RCCollector.VerificationMode");

          // Ensure the integrity of the delayed deallocation list.
          deallocationListChecker();
      }

      [NoInline]
      [ManualRefCounts]
      protected void postVerifyHeap(bool beforeCollection) {
          VTable.Assert(RCCollector.VerificationMode,
                        @"RCCollector.VerificationMode");

          SegregatedFreeList.RecycleGlobalPages();
          SegregatedFreeList.CommitFreedData();
          GC.newBytesSinceGC = UIntPtr.Zero;

          // Initialize the "backup" reference count.
          SegregatedFreeList.VisitAllObjects(backupInit);

          // Count all references and managed pointers.
          rootsScanner.Initialize(backupRefCount);
          CallStack.ScanStacks(rootsScanner, rootsScanner);
          Thread.VisitBootstrapData(rootsScanner);
          StaticData.ScanStaticData(rootsScanner);
          MultiUseWord.VisitStrongRefs(rootsScanner, false);

          CallStack.ScanStacks(resetRoots, resetRoots);
          Thread.VisitBootstrapData(resetRoots);
          StaticData.ScanStaticData(resetRoots);

          SegregatedFreeList.VisitAllObjects(resetTraversal);

          // Actual leaks (refCount > 0 and backup refCount = 0).
          leakAccumulator.Initialize();
          SegregatedFreeList.VisitAllObjects(leakAccumulator);
          VTable.DebugPrint("Leaked storage: ");
          VTable.DebugPrint((int)leakAccumulator.Size);
          VTable.DebugPrint("B");

          if (VerifyLeakedCycles) {
              // Find leaked data that *should* have been reclaimed.
              // (If L is the set of all leaked nodes, and L' the
              // transitive closure of leaked cycles, then L-L' is
              // the set of nodes that should have been captured
              // by a pure RC collector.)
              SegregatedFreeList.VisitAllObjects(leakedNodesDFS);
              SegregatedFreeList.VisitAllObjects(resetTraversal);
              SegregatedFreeList.VisitAllObjects(leakedCycleClosure);
              SegregatedFreeList.VisitAllObjects(resetTraversal);
              leakAccumulator.Initialize();
              SegregatedFreeList.VisitAllObjects(leakAccumulator);
              VTable.DebugPrint(" (");
              VTable.DebugPrint((int)leakAccumulator.Size);
              VTable.DebugPrint("B acyclic)");
          }

          // Find the roots of leaked data.
          leakedRoots.Initialize();
          SegregatedFreeList.VisitAllObjects(leakedRoots);
          leakedRootsCounter.Initialize();
          SegregatedFreeList.VisitAllObjects(leakedRootsCounter);
          SegregatedFreeList.VisitAllObjects(resetTraversal);
          VTable.DebugPrint("; leaked heap roots: ");
          VTable.DebugPrint((int)leakedRootsCounter.Total);
          VTable.DebugPrint("\n");
      }


      [Inline]
      [ManualRefCounts]
      [RequiredByBartok]
      protected static void UpdateReferentRefCounts
          (UIntPtr objAddr,
           VTable vtable,
           NonNullReferenceVisitor updater) {
          updater.VisitReferenceFields(objAddr, vtable);
      }

      [Inline]
      [ManualRefCounts]
      [RequiredByBartok]
      protected static unsafe void UpdateReferentRefCounts
          (UIntPtr objAddr,
           VTable vtable,
           int start,
           int span,
           NonNullReferenceVisitor updater) {
          uint pointerTracking = (uint)vtable.pointerTrackingMask;
          uint objTag = pointerTracking & 0xf;

          switch (objTag) {
              case ObjectLayout.PTR_VECTOR_TAG: {
                  uint length = *(uint*)(objAddr+PostHeader.Size);
                  VTable.Assert(span <= length,
                                @"span <= length");

                  UIntPtr* elemAddress = (UIntPtr*)(objAddr+
                      vtable.baseLength-PreHeader.Size)+start;
                  for (int i = 0; i < span; i++, elemAddress++) {
                      updater.Visit(elemAddress);
                  }
                  break;
              }

              case ObjectLayout.OTHER_VECTOR_TAG: {
                  uint length = *(uint*)(objAddr+PostHeader.Size);
                  VTable.Assert(span <= length,
                                @"span <= length");

                  if (vtable.arrayOf == StructuralType.Struct) {
                      int elemSize = vtable.arrayElementSize;
                      UIntPtr elemAddress = objAddr+vtable.baseLength-
                          PreHeader.Size-PostHeader.Size+elemSize*start;
                      VTable elemVTable = vtable.arrayElementClass;
                      for (int i = 0; i < span; i++,
                           elemAddress += elemSize) {
                          updater.VisitReferenceFields(elemAddress,
                                                       elemVTable);
                      }
                  }
                  break;
              }

              case ObjectLayout.PTR_ARRAY_TAG: {
                  uint length =
                      *(uint*)(objAddr+PostHeader.Size+sizeof(uint));
                  VTable.Assert(span <= length,
                                @"span <= length");

                  UIntPtr* elemAddress = (UIntPtr*)
                      (objAddr+vtable.baseLength-PreHeader.Size)+start;
                  for (int i = 0; i < span; i++, elemAddress++) {
                      updater.Visit(elemAddress);
                  }
                  break;
              }

              case ObjectLayout.OTHER_ARRAY_TAG: {
                  uint length =
                      *(uint*)(objAddr+PostHeader.Size+sizeof(uint));
                  VTable.Assert(span <= length,
                                @"span <= length");

                  if (vtable.arrayOf == StructuralType.Struct) {
                      int elemSize = vtable.arrayElementSize;
                      UIntPtr elemAddress = objAddr+vtable.baseLength-
                          PreHeader.Size-PostHeader.Size+elemSize*start;
                      VTable elemVTable = vtable.arrayElementClass;
                      for (int i = 0; i < span; i++,
                           elemAddress += elemSize) {
                          updater.VisitReferenceFields(elemAddress,
                                                       elemVTable);
                      }
                  }
                  break;
              }

              case ObjectLayout.STRING_TAG: {
                  break;
              }

              default: {
                  VTable.NotReached("An unsupported tag found!");
                  break;
              }
          }
      }


      [NoInline]
      [ManualRefCounts]
      protected static void deallocationListChecker() {
          // Check for nonzero reference counts and for
          // loops in the delayed deallocation list.
          for (Object block = delayedDeallocationList;
               block != null; block = getNextLink(block)) {
              UIntPtr objAddr = Magic.addressOf(block);
              UIntPtr page = PageTable.Page(objAddr);
              if (!PageTable.IsGcPage(page)) {
                  VTable.DebugPrint("Non-GC memory for freeing!\n");
                  VTable.DebugBreak();
              }
              uint refState = block.REF_STATE;
              if ((refState & RSMasks.refCount) != 0) {
                  VTable.DebugPrint("Non-zero reference count!\n");
                  VTable.DebugBreak();
              }
              block.REF_STATE = refState+1;
          }
          // Make another pass to reset reference counts.
          for (Object block = delayedDeallocationList;
               block != null; block = getNextLink(block)) {
              block.REF_STATE--;
          }
      }

      [NoInline]
      [ManualRefCounts]
      protected static void purgeDeallocationList
          (NonNullReferenceVisitor decrementer) {
          while (beingDeallocatedBlock != null ||
                 delayedDeallocationList != null) {
              deallocateObjects(decrementer);
          }
      }

      [Inline]
      [ManualRefCounts]
      protected static void deallocateLazily(Object obj) {
          setNextLink(obj, delayedDeallocationList);
          delayedDeallocationList = obj;
          delayedDeallocationLength++;
      }

      [Inline]
      [ManualRefCounts]
      protected static void deallocateObjects
          (NonNullReferenceVisitor decrementer) {
          int startTicks = 0;
          bool enableGCTiming = VTable.enableGCTiming;
          if (enableGCTiming) {
              VTable.enableGCTiming = false;
              startTicks = Environment.TickCount;
          }
          if (VTable.enableGCWatermarks) {
              MemoryAccounting.RecordHeapWatermarks();
          }

          // Set up a block to deallocate, if one doesn't exist.
          if (beingDeallocatedBlock == null &&
              delayedDeallocationList != null) {
              beingDeallocatedBlock = delayedDeallocationList;
              delayedDeallocationList =
                  getNextLink(delayedDeallocationList);
              delayedDeallocationLength--;

              UIntPtr objAddr = Magic.addressOf(beingDeallocatedBlock);
              VTable vtable = beingDeallocatedBlock.vtable;
              initIncrementalDecrement(objAddr, vtable);
          }

          // Perform up to a constant number of work chunks on the
          // block being deallocated. A "work chunk" is either
          // decrementing up to a fixed number of references held in
          // an object, decrementing up to a fixed number of slots
          // if the object is an array, or reclaiming the object
          // after all decrements on its internal contents are done.
          for (uint workDone = 0; beingDeallocatedBlock != null &&
               workDone < deallocationSpan; workDone++) {
               // Continue work on block.
              UIntPtr objAddr = Magic.addressOf(beingDeallocatedBlock);
 #if DEBUG
              UIntPtr page = PageTable.Page(objAddr);
              VTable.Assert(PageTable.IsGcPage(page),
                            @"PageTable.IsGcPage(page)");
 #endif // DEBUG

              VTable vtable = beingDeallocatedBlock.vtable;
              if (incrementalDecrement(objAddr, vtable,
                                       decrementer) != 0) {
                  continue;
              }

              // All decrements on contained references are over.
              Object obj = beingDeallocatedBlock;
              VTable.Assert((obj.REF_STATE & RSMasks.refCount) == 0,
                            @"(obj.REF_STATE & RSMasks.refCount) == 0");
#if DEBUG
              PLCLink* plcLinkAddr = GetPLCLink(obj);
              VTable.Assert(plcLinkAddr == null,
                            @"plcLinkAddr == null");
#endif // DEBUG

              SegregatedFreeList.Free(obj);

              // Set up block to work on next.
              beingDeallocatedBlock = delayedDeallocationList;
              if (delayedDeallocationList != null) {
                  delayedDeallocationList =
                      getNextLink(delayedDeallocationList);
                  delayedDeallocationLength--;

                  objAddr = Magic.addressOf(beingDeallocatedBlock);
                  vtable = beingDeallocatedBlock.vtable;
                  initIncrementalDecrement(objAddr, vtable);
              }
          }

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
      }

      [Inline]
      [ManualRefCounts]
      protected static unsafe uint incrementalDecrement
          (UIntPtr objAddr,
           VTable vtable,
           NonNullReferenceVisitor decrementer) {
          uint pointerTracking = (uint)vtable.pointerTrackingMask;
          uint objTag = pointerTracking & 0xf;
          uint workDone = 0;

          switch (objTag) {
              case ObjectLayout.SPARSE_TAG: {
                  UIntPtr* sparseObject = (UIntPtr*)objAddr;
                  uint lastPointerTracking = getLastTracked(objAddr);
                  for (pointerTracking = lastPointerTracking;
                       pointerTracking != 0 &&
                       workDone < decrementSpan; workDone++) {
                      uint index = pointerTracking & 0xf;
                      pointerTracking >>= 4;
                      UIntPtr* loc = sparseObject+(int)index;
                      UIntPtr addr = *loc;
                      if (addr != UIntPtr.Zero) {
                          decrementer.Visit(addr);
                      }
                  }
                  setLastTracked(objAddr, pointerTracking);
                  break;
              }

              case ObjectLayout.DENSE_TAG: {
                  UIntPtr* denseObject = (UIntPtr*)
                      (objAddr+PostHeader.Size);
                  int lastIndex =
                      unchecked((int)getLastTracked(objAddr));
                  pointerTracking >>= lastIndex+4;
                  for (denseObject += lastIndex; pointerTracking != 0 &&
                       workDone < decrementSpan; workDone++,
                       lastIndex++, denseObject++) {
                      if ((pointerTracking & 0x1) != 0 &&
                          *denseObject != UIntPtr.Zero) {
                          decrementer.Visit(denseObject);
                      }
                      pointerTracking >>= 1;
                  }
                  setLastTracked(objAddr, unchecked((uint)lastIndex));
                  break;
              }

              case ObjectLayout.PTR_VECTOR_TAG: {
                  uint length = *(uint*)(objAddr+PostHeader.Size);
                  UIntPtr* elemAddress = (UIntPtr*)
                      (objAddr+vtable.baseLength-PreHeader.Size);
                  uint lastIndex = getLastTracked(objAddr);
                  for (elemAddress += lastIndex; lastIndex < length &&
                       workDone < decrementSpan; workDone++,
                       lastIndex++, elemAddress++) {
                      if (*elemAddress != UIntPtr.Zero) {
                          decrementer.Visit(elemAddress);
                      }
                  }
                  setLastTracked(objAddr, lastIndex);
                  break;
              }

              case ObjectLayout.OTHER_VECTOR_TAG: {
                  if (vtable.arrayOf == StructuralType.Struct) {
                      uint length = *(uint*)(objAddr+PostHeader.Size);
                      UIntPtr elemAddress = objAddr+vtable.baseLength-
                          PreHeader.Size-PostHeader.Size;
                      VTable elemVTable = vtable.arrayElementClass;
                      int elemSize = vtable.arrayElementSize;
                      uint lastIndex = getLastTracked(objAddr);
                      for (elemAddress += (UIntPtr)(elemSize*lastIndex);
                           lastIndex < length &&
                           workDone < decrementSpan; workDone++,
                           lastIndex++, elemAddress += elemSize) {
                          decrementer.VisitReferenceFields(elemAddress,
                                                           elemVTable);
                      }
                      setLastTracked(objAddr, lastIndex);
                  }
                  break;
              }

              case ObjectLayout.PTR_ARRAY_TAG: {
                  uint length =
                      *(uint*)(objAddr+PostHeader.Size+sizeof(uint));
                  UIntPtr* elemAddress = (UIntPtr*)
                      (objAddr+vtable.baseLength-PreHeader.Size);
                  uint lastIndex = getLastTracked(objAddr);
                  for (elemAddress += lastIndex; lastIndex < length &&
                       workDone < decrementSpan; workDone++,
                       lastIndex++, elemAddress++) {
                      if (*elemAddress != UIntPtr.Zero) {
                          decrementer.Visit(elemAddress);
                      }
                  }
                  setLastTracked(objAddr, lastIndex);
                  break;
              }

              case ObjectLayout.OTHER_ARRAY_TAG: {
                  if (vtable.arrayOf == StructuralType.Struct) {
                      uint length =
                          *(uint*)(objAddr+
                                   PostHeader.Size+sizeof(uint));
                      UIntPtr elemAddress = objAddr+vtable.baseLength-
                          PreHeader.Size-PostHeader.Size;
                      VTable elemVTable = vtable.arrayElementClass;
                      int elemSize = vtable.arrayElementSize;
                      uint lastIndex = getLastTracked(objAddr);
                      for (elemAddress += (UIntPtr)(elemSize*lastIndex);
                           lastIndex < length &&
                           workDone < decrementSpan; workDone++,
                           lastIndex++, elemAddress += elemSize) {
                          decrementer.VisitReferenceFields(elemAddress,
                                                           elemVTable);
                      }
                      setLastTracked(objAddr, lastIndex);
                  }
                  break;
              }

              case ObjectLayout.STRING_TAG: {
                  break;
              }

              default: {
                  VTable.Assert((objTag & 0x1) == 0,
                                @"(objTag & 0x1) == 0");

                  UIntPtr* largeObject = (UIntPtr*)objAddr;
                  int* pointerDescription =
                      (int*)vtable.pointerTrackingMask;
                  int lastCount =
                      unchecked((int)getLastTracked(objAddr));
                  for (int count = *pointerDescription;
                       lastCount <= count && workDone < decrementSpan;
                       workDone++, lastCount++) {
                      UIntPtr* loc = largeObject+
                          *(pointerDescription+lastCount);
                      if (*loc != UIntPtr.Zero) {
                          decrementer.Visit(loc);
                      }
                  }
                  setLastTracked(objAddr, unchecked((uint)lastCount));
                  break;
              }
          }

          return workDone;
      }

      [ManualRefCounts]
      protected static unsafe void initIncrementalDecrement
          (UIntPtr objAddr,
           VTable vtable) {
          uint pointerTracking = (uint)vtable.pointerTrackingMask;
          uint objTag = pointerTracking & 0xf;

          switch (objTag) {
              case ObjectLayout.SPARSE_TAG: {
                  setLastTracked(objAddr, pointerTracking >> 4);
                  break;
              }

              case ObjectLayout.DENSE_TAG: {
                  setLastTracked(objAddr, 0);
                  break;
              }

              case ObjectLayout.PTR_VECTOR_TAG:
              case ObjectLayout.OTHER_VECTOR_TAG:
              case ObjectLayout.PTR_ARRAY_TAG:
              case ObjectLayout.OTHER_ARRAY_TAG: {
                  setLastTracked(objAddr, 0);
                  break;
              }

              case ObjectLayout.STRING_TAG : {
                  break;
              }

              default: {
                 setLastTracked(objAddr, 1);
                 break;
              }
          }
      }


      [Inline]
      [ManualRefCounts]
      protected static Object getNextLink(Object obj) {
          return Magic.fromAddress(obj.preHeader.muw.value);
      }

      [Inline]
      [ManualRefCounts]
      protected static void setNextLink(Object obj, Object next) {
          obj.preHeader.muw.value = Magic.addressOf(next);
      }

      [Inline]
      [ManualRefCounts]
      protected static uint getLastTracked(UIntPtr objAddr) {
          Object obj = Magic.fromAddress(objAddr);
          return (uint)obj.preHeader.muw.value;
      }

      [Inline]
      [ManualRefCounts]
      protected static void setLastTracked(UIntPtr objAddr, uint last) {
          Object obj = Magic.fromAddress(objAddr);
          obj.preHeader.muw.value = (UIntPtr)last;
      }

      [Inline]
      [ManualRefCounts]
      protected static UIntPtr getBackupRefcount(Object obj) {
          return ((RCGCVerificationObject)obj).preHeader.
                 backupRefcount;
      }

      [Inline]
      [ManualRefCounts]
      protected static void setBackupRefcount(Object obj,
                                              UIntPtr count) {
          ((RCGCVerificationObject)obj).preHeader.backupRefcount =
              count;
      }

      [Inline]
      [ManualRefCounts]
      protected static UIntPtr getDfsDiscoveryTime(Object obj) {
          return ((RCGCVerificationObject)obj).preHeader.
                 dfsDiscoveryTime;
      }

      [Inline]
      [ManualRefCounts]
      protected static void setDfsDiscoveryTime(Object obj,
                                                UIntPtr time) {
          ((RCGCVerificationObject)obj).preHeader.dfsDiscoveryTime =
              time;
      }

      [Inline]
      [ManualRefCounts]
      protected static UIntPtr getDfsFinishingTime(Object obj) {
          return ((RCGCVerificationObject)obj).preHeader.
                 dfsFinishingTime;
      }

      [Inline]
      [ManualRefCounts]
      protected static void setDfsFinishingTime(Object obj,
                                                UIntPtr time) {
          ((RCGCVerificationObject)obj).preHeader.dfsFinishingTime =
              time;
      }


      protected abstract class ObjectVisitor :
          SegregatedFreeList.ObjectVisitor {
          [ManualRefCounts]
          internal override void VisitSmall(Object obj,
                                            UIntPtr memAddr) {
              this.Visit(obj);
          }

          [ManualRefCounts]
          internal override UIntPtr VisitLarge(Object obj) {
              return this.Visit(obj);
          }

          internal abstract override UIntPtr Visit(Object obj);
      }


      protected class ResetTraversal : ObjectVisitor {
          [ManualRefCounts]
          internal override unsafe UIntPtr Visit(Object obj) {
              obj.GcMark(UIntPtr.Zero);
              VTable vtable = obj.vtable;
              UIntPtr size =
                  ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);

              return size;
          }
      }


      private class BackupInitializer : ObjectVisitor {
          [ManualRefCounts]
          internal override UIntPtr Visit(Object obj) {
              setBackupRefcount(obj, UIntPtr.Zero);

              return ObjectLayout.ObjectSize(Magic.addressOf(obj),
                                             obj.vtable);
          }
      }

      private class BackupRefCount : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr addr = *loc;

              UIntPtr page = PageTable.Page(addr);
              if (!PageTable.IsGcPage(page)) {
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack,
                                @"pageType == PageType.NonGC ||
                                pageType == PageType.Stack");

                  return;
              }

              UIntPtr objAddr = SegregatedFreeList.Find(addr);
              incrementBackupRefCount.Traverse(objAddr);
          }
      }

      private class IncrementBackupRefCount : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal void Traverse(UIntPtr objAddr) {
              Object obj = Magic.fromAddress(objAddr);
              UIntPtr count = getBackupRefcount(obj);
              setBackupRefcount(obj, count+1);
              if (obj.GcMark((UIntPtr)1)) {
                  this.VisitReferenceFields(obj);
              }
              while (!this.workList.IsEmpty) {
                  objAddr = this.workList.Read();
                  obj = Magic.fromAddress(objAddr);
                  this.VisitReferenceFields(obj);
              }
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr addr = *loc;

              UIntPtr page = PageTable.Page(addr);
              if (!PageTable.IsGcPage(page)) {
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack,
                                @"pageType == PageType.NonGC ||
                                pageType == PageType.Stack");

                  return;
              }

              UIntPtr objAddr = SegregatedFreeList.Find(addr);
              Object obj = Magic.fromAddress(objAddr);
              UIntPtr count = getBackupRefcount(obj);
              setBackupRefcount(obj, count+1);
              if (obj.GcMark((UIntPtr)1)) {
                  this.workList.Write(objAddr);
              }
          }

          private UIntPtrQueue workList;
      }

      private class RootsScanner : NonNullReferenceVisitor {
          internal void Initialize(NonNullReferenceVisitor v) {
              this.visitor = v;
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr pageLoc = PageTable.Page((UIntPtr)loc);
              PageType pageType = PageTable.Type(pageLoc);
              if (pageType != PageType.NonGC &&
                  pageType != PageType.Stack) {
                  VTable.Assert(PageTable.IsGcPage(pageLoc),
                                @"PageTable.IsGcPage(pageLoc)");

                  return;
              }

              uint addr = (uint)*loc;
              if (pageType == PageType.NonGC || (addr & 0x03) == 0) {
                  this.visitor.Visit(loc);
              }
              if (pageType == PageType.Stack) {
                  *loc = (UIntPtr)(addr | 0x01);
              }
          }

          NonNullReferenceVisitor visitor;
      }

      private class ResetRoots : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr pageLoc = PageTable.Page((UIntPtr)loc);
              PageType pageType = PageTable.Type(pageLoc);
              if (pageType != PageType.NonGC &&
                  pageType != PageType.Stack) {
                  VTable.Assert(PageTable.IsGcPage(pageLoc),
                                @"PageTable.IsGcPage(pageLoc)");

                  return;
              }

              if (pageType == PageType.Stack) {
                  *loc = (UIntPtr)((uint)*loc & 0xfffffffc);
              }
          }
      }

      private class LeakAccumulator : ObjectVisitor {
          internal UIntPtr Size;

          internal void Initialize() {
              this.Size = UIntPtr.Zero;
          }

          [ManualRefCounts]
          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr size =
                  ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & RSMasks.refCount);
              if ((refState & RSMasks.countingFlag) != 0 &&
                  refCount > 0) {
                  // This object is considered live by the
                  // RC collector.
                  UIntPtr count = getBackupRefcount(obj);
                  if (count == 0) {
                      // But it is actually unreachable.
                      this.Size += size;
                  }
              }

              return size;
          }
      }

      private class LeakedNodesDFS : ObjectVisitor {
          [ManualRefCounts]
          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr size =
                  ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & RSMasks.refCount);
              if ((refState & RSMasks.countingFlag) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefcount(obj);
                  if (count == 0) {
                      UIntPtr objAddr = Magic.addressOf(obj);
                      dfsMarker.Visit(&objAddr);
                  }
              }

              return size;
          }
      }

      private class DFSMarker : NonNullReferenceVisitor {
          internal void Initialize() {
              this.time = UIntPtr.Zero;
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;

              UIntPtr page = PageTable.Page(objAddr);
              if (!PageTable.IsGcPage(page)) {
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack,
                                @"pageType == PageType.NonGC ||
                                pageType == PageType.Stack");

                  return;
              }

              Object obj = Magic.fromAddress(objAddr);
              if (obj.GcMark((UIntPtr)1)) {
                  this.time = this.time+1;
                  setDfsDiscoveryTime(obj, this.time);

                  UIntPtr vtableAddr = Magic.addressOf(obj.vtable);
                  this.Visit(&vtableAddr);
                  this.VisitReferenceFields(obj);

                  this.time = this.time+1;
                  setDfsFinishingTime(obj, this.time);
              }
          }

          private UIntPtr time;
      }

      private class LeakedCycleClosure : ObjectVisitor {
          [ManualRefCounts]
          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr size =
                  ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & RSMasks.refCount);
              if ((refState & RSMasks.countingFlag) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefcount(obj);
                  if (count == 0) {
                      UIntPtr dTime = getDfsDiscoveryTime(obj);
                      UIntPtr fTime = getDfsFinishingTime(obj);
                      cycleClosure.Initialize(dTime, fTime);
                      cycleClosure.VisitReferenceFields(obj);
                  }
              }

              return size;
          }
      }

      private class CycleClosure : NonNullReferenceVisitor {
          internal void Initialize(UIntPtr dTime, UIntPtr fTime) {
              this.predDiscoveryTime = dTime;
              this.predFinishingTime = fTime;
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;

              UIntPtr page = PageTable.Page(objAddr);
              if (!PageTable.IsGcPage(page)) {
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack,
                                @"pageType == PageType.NonGC ||
                                pageType == PageType.Stack");

                  return;
              }

              Object obj = Magic.fromAddress(objAddr);
              UIntPtr dTime = getDfsDiscoveryTime(obj);
              UIntPtr fTime = getDfsFinishingTime(obj);
              VTable.Assert(this.predDiscoveryTime > UIntPtr.Zero &&
                            this.predFinishingTime > UIntPtr.Zero &&
                            dTime > UIntPtr.Zero &&
                            fTime > UIntPtr.Zero,
                            @"this.predDiscoveryTime > UIntPtr.Zero &&
                            this.predFinishingTime > UIntPtr.Zero &&
                            dTime > UIntPtr.Zero &&
                            fTime > UIntPtr.Zero");

              if (dTime < this.predDiscoveryTime &&
                  this.predDiscoveryTime < this.predFinishingTime &&
                  this.predFinishingTime < fTime) {
                  // A back edge is incident on this node;
                  // therefore, the node is part of a cycle.
                  backupRefCount.Visit(&objAddr);
              }
          }

          private UIntPtr predDiscoveryTime;
          private UIntPtr predFinishingTime;
      }

      private class BFSMarker : NonNullReferenceVisitor {
          internal void Initialize(bool isVisited) {
              this.isVisited = (UIntPtr)(isVisited ? 1 : 0);
          }

          [ManualRefCounts]
          internal void Traverse(Object obj) {
              this.VisitReferenceFields(obj);
              while (!this.workList.IsEmpty) {
                  UIntPtr objAddr = this.workList.Read();
                  obj = Magic.fromAddress(objAddr);
                  this.VisitReferenceFields(obj);
              }
          }

          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr addr = *loc;

              UIntPtr page = PageTable.Page(addr);
              if (!PageTable.IsGcPage(page)) {
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack,
                                @"pageType == PageType.NonGC ||
                                pageType == PageType.Stack");

                  return;
              }

              UIntPtr objAddr = SegregatedFreeList.Find(addr);
              Object obj = Magic.fromAddress(objAddr);
              if (obj.GcMark(this.isVisited)) {
                  this.workList.Write(objAddr);
              }
          }

          private UIntPtr isVisited;
          private UIntPtrQueue workList;
      }

      private class LeakedRoots : ObjectVisitor {
          internal void Initialize() {
              bfsMarker.Initialize(true);
          }

          [ManualRefCounts]
          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr size =
                  ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & RSMasks.refCount);
              if ((refState & RSMasks.countingFlag) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefcount(obj);
                  if (count == 0 && obj.GcMark() == UIntPtr.Zero) {
                      bfsMarker.Traverse(obj);
                  }
              }

              return size;
          }
      }

      private class LeakedRootsCounter : ObjectVisitor {
          internal uint Total;

          internal void Initialize() {
              this.Total = 0;
          }

          [ManualRefCounts]
          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr size =
                  ObjectLayout.ObjectSize(Magic.addressOf(obj),
                                          vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & RSMasks.refCount);
              if ((refState & RSMasks.countingFlag) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefcount(obj);
                  if (count == 0 && obj.GcMark() == UIntPtr.Zero) {
                      this.Total++;
                  }
              }

              return size;
          }
      }


      private static Object delayedDeallocationList;
      private static Object beingDeallocatedBlock;
      private static uint delayedDeallocationLength;
      private const uint collectionTrigger = 1 << 15;
      private const uint deallocationSpan = 1 << 20;
      private const uint decrementSpan = 1 << 8;

      // Used only in verification mode.
      private static BackupInitializer backupInit;
      private static BackupRefCount backupRefCount;
      private static IncrementBackupRefCount incrementBackupRefCount;
      private static RootsScanner rootsScanner;
      private static NonNullReferenceVisitor resetRoots;
      private static ObjectVisitor resetTraversal;
      private static LeakAccumulator leakAccumulator;
      private static LeakedNodesDFS leakedNodesDFS;
      private static LeakedCycleClosure leakedCycleClosure;
      private static CycleClosure cycleClosure;
      private static DFSMarker dfsMarker;
      private static BFSMarker bfsMarker;
      private static LeakedRootsCounter leakedRootsCounter;
      private static LeakedRoots leakedRoots;
  }
}


