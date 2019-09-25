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
  using System.Runtime.CompilerServices;
  using Microsoft.Bartok.Runtime;

  internal class MemoryAccounting {
      private static BumpAllocator localArea;

      private static ManagedPtrAccounting traceablePtrs;
      private static ManagedPtrAccounting traceablePinnedPtrs;
      private static StaticPtrAccounting staticPtrs;

      private static AssertRTypeHeaders assertRTypeHeaders;
      private static ObjectLayout.ObjectVisitor forGCAssertRTypeHeaders;
      private static RuntimeTypeReckoner runtimeTypeReckoner;
      private static ObjectLayout.ObjectVisitor forGCRuntimeTypeReckoner;
      private static RuntimeTypeMapper runtimeTypeMapper;
      private static ObjectLayout.ObjectVisitor forGCRuntimeTypeMapper;
      private static InstanceReckoner instanceReckoner;
      private static ObjectLayout.ObjectVisitor forGCInstanceReckoner;

      private const int TABLE_SIZE = 1024;
      private static RuntimeTypeAccounting[] table;

      private static UIntPtr totalSize;

      private static bool initialized;

      internal static long MaxHeapWatermark;
      internal static double AvgHeapSize;
      internal static long Records;

      internal unsafe static void Initialize(GCType gcType) {
          traceablePtrs = new ManagedPtrAccounting();
          traceablePinnedPtrs = new ManagedPtrAccounting();
          staticPtrs = new StaticPtrAccounting();

          assertRTypeHeaders = new AssertRTypeHeaders();
          forGCAssertRTypeHeaders = assertRTypeHeaders;
          runtimeTypeReckoner = new RuntimeTypeReckoner();
          forGCRuntimeTypeReckoner = runtimeTypeReckoner;
          runtimeTypeMapper = new RuntimeTypeMapper();
          forGCRuntimeTypeMapper = runtimeTypeMapper;
          instanceReckoner = new InstanceReckoner();
          forGCInstanceReckoner = instanceReckoner;

          switch(gcType) {
            case GCType.MarkSweepCollector: {
                forGCAssertRTypeHeaders = new SegregatedFreeList.ObjectVisitorWrapper(assertRTypeHeaders);
                forGCRuntimeTypeReckoner = new SegregatedFreeList.ObjectVisitorWrapper(runtimeTypeReckoner);
                forGCRuntimeTypeMapper = new SegregatedFreeList.ObjectVisitorWrapper(runtimeTypeMapper);
                forGCInstanceReckoner = new SegregatedFreeList.ObjectVisitorWrapper(instanceReckoner);
                break;
            }
          }

          table = new RuntimeTypeAccounting[TABLE_SIZE];

          MemoryAccounting.initialized = true;
      }

      internal unsafe static void Report(GCType gcType) {
          if(!MemoryAccounting.initialized) {
              VTable.DebugPrint("MemoryAccounting invoked before"
                                + " initialization was completed!\n");
              return;
          }

          VTable.DebugPrint("\nCollector: ");
          switch(gcType) {
              case GCType.AdaptiveCopyingCollector: {
                  VTable.DebugPrint("Adaptive Copying\n");
                  break;
              }
              case GCType.MarkSweepCollector: {
                  VTable.DebugPrint("Mark-Sweep\n");
                  break;
              }
              case GCType.SemispaceCollector: {
                  VTable.DebugPrint("Semispace\n");
                  break;
              }
              case GCType.SlidingCollector: {
                  VTable.DebugPrint("Sliding\n");
                  break;
              }
              case GCType.ConcurrentMSCollector: {
                  VTable.DebugPrint("Concurrent Mark-Sweep\n");
                  break;
              }
              case GCType.ReferenceCountingCollector: {
                  VTable.DebugPrint("Reference Counting\n");
                  VTable.NotImplemented();
                  return; // Not supported yet.
              }
#if !SINGULARITY
              case GCType.DeferredReferenceCountingCollector: {
                  VTable.DebugPrint("Deferred Reference Counting\n");
                  VTable.NotImplemented();
                  return; // Not supported yet.
              }
#endif
              default: {
                  VTable.NotReached("Unknown GC type: "+gcType);
                  break;
              }
          }

          uint pageSize = (uint)(PageTable.PageSize >> 10);
          VTable.DebugPrint("\nPage size: {0}KB\nVM size: {1} KB\n",
                            __arglist(pageSize,
                                      pageSize*(uint)PageTable.pageTableCount));

          ReportNonGCDetails();
          ReportStackDetails();
          ReportHeapDetails();
      }

      internal unsafe static void ReportNonGCDetails() {
          VTable.DebugPrint("\nNon-GC data details:\n");
          uint totalPageCount = TotalNumPages(PageType.NonGC);
          VTable.DebugPrint("\tTotal number of pages: {0}",
                            __arglist(totalPageCount));

          VTable.DebugPrint("\n\tMemory accounting storage: {0}B",
                            __arglist((uint)totalSize));

          staticPtrs.Initialize();
          uint staticSize = StaticData.ScanStaticPointerData(staticPtrs);
          VTable.DebugPrint("\n\tCompile-time allocated data: {0}B",
                            __arglist(staticSize));
          VTable.DebugPrint("\n\tNumber of pointers: {0}",
                            __arglist(staticPtrs.PtrCount));
          uint bootstrapPageCount = totalPageCount -
              (uint)PageTable.PageCount((UIntPtr)staticSize);
          VTable.DebugPrint("\n\tNumber of bootstrap pages: {0}\n",
                            __arglist(bootstrapPageCount));
      }

      internal unsafe static void ReportStackDetails() {
          VTable.DebugPrint("\nStack details:\n");
          VTable.DebugPrint("\tTotal number of reserved pages: {0}",
                            __arglist(TotalNumPages(PageType.Stack)));

          for (int i = 0; i < Thread.threadTable.Length; i++) {
              traceablePtrs.Initialize();
              traceablePinnedPtrs.Initialize();

              Thread t = Thread.threadTable[i];
              if (t == null) {
                  continue;
              }

              uint numStackFrames =
                  CallStack.ScanStack(t, traceablePtrs,
                                      traceablePinnedPtrs);

              VTable.DebugPrint("\n\tThread: {0}",
                                __arglist(i));
              VTable.DebugPrint("\n\t\tStack frame count: {0}",
                                __arglist(numStackFrames));
              VTable.DebugPrint("\n\t\tManaged ptrs to static data: {0}",
                                __arglist
                                (traceablePtrs.managedPtrsToStaticData));
              VTable.DebugPrint("\n\t\tManaged ptrs to stack: {0}",
                                __arglist(traceablePtrs.managedPtrsToStack));
              VTable.DebugPrint("\n\t\tExterior managed heap ptrs: {0}",
                                __arglist
                                (traceablePtrs.exteriorManagedHeapPtrs));
              VTable.DebugPrint("\n\t\tInterior managed heap ptrs: {0}",
                                __arglist
                                (traceablePtrs.interiorManagedHeapPtrs));

#if !SINGULARITY
              UIntPtr stackTop = (UIntPtr) CallStack.StackMarker(t);
              uint stackSize = 0;
              if (stackTop != UIntPtr.Zero) {
                  VTable.Assert(CallStack.StackBase(t) > stackTop,
                                @"t.asmStackBase > stackTop");

                  stackSize = (uint)(CallStack.StackBase(t)-stackTop);
              }
              VTable.DebugPrint("\n\t\tApprox. stack size: {0}B",
                                __arglist(stackSize));
#endif

              // REVIEW: Why are these here?
              VTable.Assert(traceablePinnedPtrs.
                            managedPtrsToStaticData == 0,
                            @"traceablePinnedPtrs.
                            managedPtrsToStaticData == 0");
              VTable.Assert(traceablePinnedPtrs.
                            managedPtrsToStack == 0,
                            @"traceablePinnedPtrs.
                            managedPtrsToStack == 0");

              VTable.DebugPrint("\n\t\tPinned managed heap ptrs: {0}",
                                __arglist
                                (traceablePinnedPtrs.exteriorManagedHeapPtrs +
                                 traceablePinnedPtrs.interiorManagedHeapPtrs));
          }

          VTable.DebugPrint("\n");
      }

      internal static void ReportHeapDetails() {
          VTable.DebugPrint("\nHeap details:\n");
          uint pageCount = 0;
          for (UIntPtr i = UIntPtr.Zero; i < PageTable.pageTableCount;
               i++) {
              if (PageTable.IsMyGcPage(i)) {
                  pageCount++;
              }
          }
          VTable.DebugPrint("\tTotal number of heap pages: {0}",
                            __arglist(pageCount));

          // The following obtains counts of heap objects against types.
          UIntPtr lowPage = UIntPtr.Zero;
          UIntPtr highPage = PageTable.pageTableCount;
          assertRuntimeTypeHeaders(lowPage, highPage);

          // First count the RuntimeType instances for heap objects.
          runtimeTypeReckoner.Initialize(true);
          visitAllObjects(forGCRuntimeTypeReckoner, lowPage, highPage);

          // Next, create a table for RuntimeType instance accounting.
          // NOTE: Storage for the table is marked "non-GC". Since
          // static data accounting is done before this, it's okay.
          int numSlots = runtimeTypeReckoner.Count;
          if(numSlots > TABLE_SIZE) {
              VTable.DebugPrint("Need {0} slots, have {1}\n",
                                __arglist(numSlots, TABLE_SIZE));
              VTable.NotReached("MemoryAccounting table not large enough");
          }

          // Associate a table slot for each RuntimeType instance.
          runtimeTypeMapper.Initialize(false, MemoryAccounting.table);
          visitAllObjects(forGCRuntimeTypeMapper, lowPage, highPage);

          // Map each relevant RuntimeType instance to its table slot.
          for (uint i = 0; i < numSlots; i++) {
              RuntimeType rType = MemoryAccounting.table[i].RuntimeTypeObject;
              VTable.Assert(!MultiUseWord.IsMarked(rType),
                            @"!MultiUseWord.IsMarked(rType)");
              MemoryAccounting.table[i].SavedMUW =
                  MultiUseWord.GetForObject(rType);
              MultiUseWord.SetValForObject(rType, (UIntPtr)i);
          }

          // Count heap object instances by RuntimeType using table.
          instanceReckoner.Initialize(MemoryAccounting.table);
          visitAllObjects(forGCInstanceReckoner, lowPage, highPage);

          // Bubble sort the table in decreasing order of total size.
          for (int i = 0; i < numSlots; i++) {
              for (int j = numSlots-1; j > i; j--) {
                  if (MemoryAccounting.table[j].TotalSize
                      > MemoryAccounting.table[j-1].TotalSize) {
                      // Swap contents.
                      RuntimeTypeAccounting temp = MemoryAccounting.table[j];
                      MemoryAccounting.table[j] = MemoryAccounting.table[j-1];
                      MemoryAccounting.table[j-1] = temp;
                  }
              }
          }

          // Display table.
          VTable.DebugPrint("\n\tCounts of objects against types:\n");
          for (uint i = 0; i < numSlots; i++) {
              if((uint)MemoryAccounting.table[i].TotalSize < 1024) {
                  continue;
              }
              VTable.DebugPrint
                  ("\t\t{0,36} instances: {1,6}, bytes: {2,10}\n",
                   __arglist(MemoryAccounting.table[i].RuntimeTypeObject.Name,
                             (uint)MemoryAccounting.table[i].Count,
                             (uint)MemoryAccounting.table[i].TotalSize));
          }

          // Reset book-keeping information maintained in headers and the global
          // table.
          for (uint i = 0; i < numSlots; i++) {
              RuntimeType rType = MemoryAccounting.table[i].RuntimeTypeObject;
              MultiUseWord.SetForObject
                  (rType, MemoryAccounting.table[i].SavedMUW);
              VTable.Assert(!MultiUseWord.IsMarked(rType),
                            "@!MultiUseWord.IsMarked(rType)");

              MemoryAccounting.table[i].RuntimeTypeObject = null;
              MemoryAccounting.table[i].SavedMUW =
                  new MultiUseWord(new UIntPtr(0));
              MemoryAccounting.table[i].TotalSize = new UIntPtr(0);
              MemoryAccounting.table[i].Count = 0;
          }
      }

      internal static void ReportHeapWatermarks() {
          VTable.DebugPrint("Max. Heap: {0}KB ",
                            __arglist(MaxHeapWatermark >> 10));
          VTable.DebugPrint("Avg. Heap: {0}KB ",
                            __arglist(((ulong)AvgHeapSize) >> 10));
          VTable.DebugPrint("\n");
      }

      [ManualRefCounts]
      internal static long RecordHeapWatermarks() {
          long totalMemory = GC.installedGC.TotalMemory;
          if (totalMemory > MaxHeapWatermark) {
              MaxHeapWatermark = totalMemory;
          }
          Records++;
          AvgHeapSize = (AvgHeapSize*Records+totalMemory)/Records;

          return totalMemory;
      }

      internal static uint TotalNumPages(PageType kind) {
          uint pageCount = 0;
          for (UIntPtr i = UIntPtr.Zero; i < PageTable.pageTableCount;
               i++) {
              if (PageTable.IsMyPage(i)) {
                  PageType pageType = PageTable.Type(i);
                  if (pageType == kind) {
                      pageCount++;
                  }
              }
          }

          return pageCount;
      }

      private static void visitAllObjects(ObjectLayout.ObjectVisitor visitor,
                                          UIntPtr lowPage, UIntPtr highPage)
      {
          for (UIntPtr first = lowPage; first < highPage; first++) {
              if (PageTable.IsMyGcPage(first)) {
                  UIntPtr last = first+1;
                  while (last < highPage) {
                      if (!PageTable.IsMyGcPage(last)) {
                          break;
                      }
                      last++;
                  }
                  UIntPtr start = PageTable.PageAddr(first);
                  UIntPtr end = PageTable.PageAddr(last);
                  GC.installedGC.VisitObjects(visitor, start, end);
                  first = last;
              }
          }
      }

      [System.Diagnostics.Conditional("DEBUG")]
      private static void assertRuntimeTypeHeaders(UIntPtr lowPage,
                                                   UIntPtr highPage) {
          visitAllObjects(forGCAssertRTypeHeaders, lowPage, highPage);
      }


      private class ManagedPtrAccounting : NonNullReferenceVisitor {
          internal uint managedPtrsToStaticData;
          internal uint managedPtrsToStack;
          internal uint interiorManagedHeapPtrs;
          internal uint exteriorManagedHeapPtrs;

          internal void Initialize() {
              managedPtrsToStaticData = 0;
              managedPtrsToStack = 0;
              interiorManagedHeapPtrs = 0;
              exteriorManagedHeapPtrs = 0;
          }

          internal override unsafe void Visit(UIntPtr* loc) {
              // <loc> is a traceable pointer; its referent
              // either resides in the heap, the stack or in
              // the static data area.
              UIntPtr addr = *loc;

              UIntPtr page = PageTable.Page(addr);
              VTable.Assert(PageTable.IsMyPage(page),
                            "MemoryAccounting: !IsMyPage");
              if (!PageTable.IsGcPage(page)) {
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack ||
                                pageType == PageType.Shared,
                                "unexpected page type");

                  if (pageType == PageType.NonGC) {
                      // A managed pointer into the static data area.
                      managedPtrsToStaticData++;
                  } else {
                      // A managed pointer into the stack area.
                      managedPtrsToStack++;
                  }
                  return;
              }

              UIntPtr objAddr = GC.installedGC.FindObjectAddr(addr);
              if (objAddr != addr) {
                  // A "truly" interior pointer into a heap object.
                  interiorManagedHeapPtrs++;
              } else {
                  exteriorManagedHeapPtrs++;
              }
          }
      }

      private class StaticPtrAccounting : NonNullReferenceVisitor {
          internal uint PtrCount;

          internal void Initialize() {
              PtrCount = 0;
          }

          internal override unsafe void Visit(UIntPtr* loc) {
              // <loc> is an address of a reference location
              // in the static data area.
              UIntPtr page = PageTable.Page((UIntPtr)loc);
              PageType pageType = PageTable.Type(page);
              VTable.Assert(pageType == PageType.NonGC,
                            @"pageType == PageType.NonGC");

              PtrCount++;
          }
      }

      private struct RuntimeTypeAccounting {
          // Reference to the accounted RuntimeType object.
          internal RuntimeType RuntimeTypeObject;

          // Copy of the accounted RuntimeType MultiUseWord.
          internal MultiUseWord SavedMUW;

          // Total size of all instances having this RuntimeType.
          internal UIntPtr TotalSize;

          // Number of instances having this RuntimeType.
          internal uint Count;
      }

      private class AssertRTypeHeaders : ObjectLayout.ObjectVisitor {
          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              RuntimeType rType = vtable.vtableType;
              VTable.Assert(!MultiUseWord.IsMarked(rType),
                            "@!MultiUseWord.IsMarked(rType)");
              return ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);
          }
      }

      private class RuntimeTypeReckoner : ObjectLayout.ObjectVisitor {
          internal int Count;

          internal void Initialize(bool isVisitedFlag) {
              this.isVisitedFlag = isVisitedFlag;
              this.Count = 0;
          }

          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              RuntimeType rType = vtable.vtableType;
              if (MultiUseWord.IsMarked(rType) != this.isVisitedFlag) {
                  this.Count++;
                  MultiUseWord.SetMark(rType, this.isVisitedFlag);
              }

              return ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);
          }

          private bool isVisitedFlag;
      }

      private class RuntimeTypeMapper : ObjectLayout.ObjectVisitor {
          internal void Initialize(bool isVisitedFlag,
                                   RuntimeTypeAccounting[] table) {
              this.isVisitedFlag = isVisitedFlag;
              this.tableIndex = 0;
              this.accounts = table;
          }

          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              RuntimeType rType = vtable.vtableType;
              if (MultiUseWord.IsMarked(rType) != this.isVisitedFlag) {
                  VTable.Assert(this.tableIndex <
                                this.accounts.Length,
                                @"this.tableIndex <
                                  this.accounts.Length");

                  this.accounts[this.tableIndex].RuntimeTypeObject =
                      rType;
                  this.accounts[this.tableIndex].TotalSize =
                      UIntPtr.Zero;
                  this.accounts[this.tableIndex].Count = 0;
                  MultiUseWord.SetMark(rType, this.isVisitedFlag);
                  this.tableIndex++;
              }

              return ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);
          }

          private bool isVisitedFlag;
          private uint tableIndex;
          private RuntimeTypeAccounting[] accounts;
      }

      private class InstanceReckoner : ObjectLayout.ObjectVisitor {
          internal void Initialize(RuntimeTypeAccounting[] table) {
              this.accounts = table;
          }

          internal override unsafe UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              RuntimeType rType = vtable.vtableType;
              uint tableIndex = (uint) MultiUseWord.GetValForObject(rType);
              UIntPtr objAddr = Magic.addressOf(obj);
              this.accounts[tableIndex].TotalSize +=
                  ObjectLayout.ObjectSize(objAddr, vtable);
              this.accounts[tableIndex].Count++;

              return ObjectLayout.ObjectSize(objAddr, vtable);
          }

          private RuntimeTypeAccounting[] accounts;
      }
  }
}
