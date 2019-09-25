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
// #define MEASURE_RCPHASES

namespace System.GCs {

  using Microsoft.Bartok.Options;
  using Microsoft.Bartok.Runtime;
  using System.Runtime.InteropServices;
  using System.Runtime.CompilerServices;
  using System.Threading;
  using System.Collections;

  [NoCCtor]
  internal class DeferredReferenceCountingCollector :
      SingleThreadedCollector {
      // This is a compiler intrinsic whose value is controlled by
      // /StageControl.GCReferenceCountingVerifyRefCounts.
      internal static extern bool VerificationMode {
          [Intrinsic]
          get;
      }

      // This is a compiler intrinsic whose value is controlled by
      // /StageControl.RCCollectorVerifyLeakedCycles.
      internal static extern bool VerifyLeakedCycles {
          [Intrinsic]
          get;
      }

      // This is a compiler intrinsic whose value is controlled by
      // /StageControl.GCReferenceCountingGenerateProfile.
      internal static extern bool ProfilingMode {
          [Intrinsic]
          get;
      }

      [MixinConditional("DeferredReferenceCountingGC")]
      [Mixin(typeof(PreHeader))]
      [RequiredByBartok]
      internal struct PreHeaderDeferredRCGC {
          internal uint plcIndex;
      }

      [MixinConditional("DeferredReferenceCountingGC")]
      [Mixin(typeof(Object))]
      internal class DeferredRCGCObject : System.Object {
          internal new PreHeaderDeferredRCGC preHeader;
          [RequiredByBartok]
          internal new PostHeaderRC postHeader;

          internal new uint REF_STATE {
              [Inline]
              [ManualRefCounts]
              [MixinOverride]
              get {
                  return this.postHeader.refState;
              }
              [Inline]
              [ManualRefCounts]
              [MixinOverride]
              set {
                  this.postHeader.refState = value;
              }
          }
      }

      [MixinConditional("DeferredReferenceCountingGCVerification")]
      [Mixin(typeof(PreHeader))]
      [RequiredByBartok]
      internal unsafe struct PreHeaderDeferredRCGCVerification {
          internal UIntPtr backupRefCount;
          internal UIntPtr dfsDiscoveryTime;
          internal UIntPtr dfsFinishingTime;
      }

      [MixinConditional("DeferredReferenceCountingGCVerification")]
      [Mixin(typeof(Object))]
      internal class DeferredRCVerificationObject : System.Object {
          internal new PreHeaderDeferredRCGCVerification preHeader;
      }

      [Inline]
      [ManualRefCounts]
      internal static uint GetPLCIndex(Object obj) {
          return ((DeferredRCGCObject)obj).preHeader.plcIndex;
      }

      [Inline]
      [ManualRefCounts]
      internal static void SetPLCIndex(Object obj, uint index) {
          ((DeferredRCGCObject)obj).preHeader.plcIndex = index;
      }

      /*
       * Every object maintains a 32-bit "reference state" (RS).
       * The RS consists of a marking bit, a bit flagging alignment,
       * a bit flagging whether reference counting is enabled or
       * disabled on the object, and a 29-bit reference count (RC).
       *
       * Given a virtual memory size of 2GB and an object size of
       * at least 12 bytes (multi-use-word, RS field and the vtable),
       * there can't be more than 2^28 objects. The reference count
       * can be more, due to multiple references from an object
       * to the same target, but will be less than 2^29.
       */

      internal const int markFlagBit = 31;
      internal const int acyclicFlagBit = 30;
      internal const int countingONFlagBit = 29;

      internal const uint markFlagMask = 1U << markFlagBit;
      internal const uint acyclicFlagMask =  1U << acyclicFlagBit;
      internal const uint countingONFlagMask = 1U << countingONFlagBit;

      internal const uint refCountMask =
          ~(markFlagMask | acyclicFlagMask | countingONFlagMask);

      private static NonNullReferenceVisitor refCountIncrementer;
      private static NonNullReferenceVisitor refCountDecrementer;

      internal static DeferredReferenceCountingCollector instance;
      private static bool isInGC;

      private static Object delayedDeallocationList;
      private static Object objectBeingDeallocated;
      private static uint delayedDeallocationLength;
      private static uint releasedObjectCount;
      private static uint numCollections;

      private const uint collectionTrigger = 1 << 15;
      private const uint recycleTrigger = collectionTrigger << 4;
      private const int deallocationSpan = 1 << 20;
      private const int numCollectionsTrigger = 8;

      private static NonNullReferenceVisitor stackRefCountIncrementer;
      private static NonNullReferenceVisitor stackRefCountDecrementer;

      private const double triggerFraction = 0.90;

      // For cycle collection.
      private static InternalIncrementer internalIncrementer;
      private static InternalDecrementer internalDecrementer;
      private static InternalScanner internalScanner;
      private static InternalReclaimer internalReclaimer;

      private static UIntPtr plcRawSize, plcRawAddr;
      private static UIntPtr[] plcBuffer;
      private static uint freePLCHead;
      private const uint initialPLCNumEntries = 1 << 12;
      private const uint maxPLCNumEntries = 1 << 20;
      private static bool needCleanPLCBuffer;

      private static ulong maxCyclicGarbage;
      private static ulong totalCyclicGarbage;
      private static uint cycleCollections;
      private static bool forceCycleCollectionAtEnd {
          get { return true; }
      }

      // Used only in verification mode.
      private static bool canVerifyHeap;
      private static BackupInitializer backupInit;
      private static BackupRefCount backupRefCount;
      private static BackupReconciler backupReconciler;
      private static IncrementBackupRefCount incrementBackupRefCount;
      private static RootsScanner rootsScanner;
      private static NonNullReferenceVisitor resetRoots;
      private static ObjectVisitor resetTraversal;
      private static LeakAccumulator leakAccumulator;
      private static LeakedNodesDFS leakedNodesDFS;
      private static LeakedCycleClosure leakedCycleClosure;
      private static DFS dfs;
      private static CycleClosure cycleClosure;
      private static BFSMarker bfsMarker;
      private static LeakedRootsCounter leakedRootsCounter;
      private static LeakedRoots leakedRoots;

      // Used only in profiling mode.
      private static String[] methodNames;
      private static int[] increments;
      private static int[] decrements;
      private static int[] nonNullIncrements;
      private static int[] nonNullDecrements;
      private static int[] aIncrements;
      private static int[] aDecrements;
      private static int[] nonNullAIncrements;
      private static int[] nonNullADecrements;
      private static int[] vIncrements;
      private static int[] vDecrements;
      private static int[] rIncrements;
      private static int[] rDecrements;

      // Used to measure the cumulative times in the various RC phases.
#if MEASURE_RCPHASES
      private static bool ddListPhase;
      private static long ddListProcTime;
      private static long ddListProcCount;
      private static long ddListPLCProcTime;
      private static long ddListPLCProcCount;

      private static bool plcBufferPhase;
      private static long plcBufferProcTime;
      private static long plcBufferProcCount;
      private static long plcBufferDDListProcTime;
      private static long plcBufferDDListProcCount;

      private static long segFreeTime;
      private static long segCommitTime;

      private static long stackScanCount;
#endif // MEASURE_RCPHASES

      [PreInitRefCounts]
      public new static unsafe void Initialize() {
          SegregatedFreeList.Initialize();
          instance =
              (DeferredReferenceCountingCollector)BootstrapMemory.
              Allocate(typeof(DeferredReferenceCountingCollector));
          isInGC = false;

          ZeroCountTable.Initialize();

          refCountIncrementer =
              (RefCountIncrementer)BootstrapMemory.
              Allocate(typeof(RefCountIncrementer));
          refCountDecrementer =
              (RefCountDecrementer)BootstrapMemory.
              Allocate(typeof(RefCountDecrementer));
          stackRefCountIncrementer =
              (StackRefCountIncrementer)BootstrapMemory.
              Allocate(typeof(StackRefCountIncrementer));
          stackRefCountDecrementer =
              (StackRefCountDecrementer)BootstrapMemory.
              Allocate(typeof(StackRefCountDecrementer));

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

          allocatePLCBuffer(initialPLCNumEntries);
          stitchFreePLCSlots(1);
          needCleanPLCBuffer = false;

          canVerifyHeap = true;
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
              backupReconciler =
                  (BackupReconciler)BootstrapMemory.
                  Allocate(typeof(BackupReconciler));
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
              dfs =
                  (DFS)BootstrapMemory.
                  Allocate(typeof(DFS));
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


      [NoInline]
      [ManualRefCounts]
      internal override void CollectStoppable(int currentThreadIndex,
                                              int generation) {
          int startTicks = 0;
          bool enableGCTiming = VTable.enableGCTiming;
          if (enableGCTiming) {
              VTable.enableGCTiming = false;
              startTicks = Environment.TickCount;
#if MEASURE_RCPHASES
              stackScanCount++;
#endif
          }

          isInGC = true;
          CallStack.ScanStacks(stackRefCountIncrementer,
                               stackRefCountIncrementer);
          ZeroCountTable.ProcessZeroCountTable();
          if (needCleanPLCBuffer) {
              processPLCBuffer();
              needCleanPLCBuffer = false;
          }
          deallocateObjects();
          CallStack.ScanStacks(stackRefCountDecrementer,
                               stackRefCountDecrementer);
          StartGCCycle();
          isInGC = false;

          if (enableGCTiming) {
              int elapsedTicks = Environment.TickCount-startTicks;
              BaseCollector.RegisterPause(elapsedTicks);
              VTable.enableGCTiming = true;
          }
      }

      internal override int CollectionGeneration(int gen) {
          return MinGeneration;
      }

      [NoInline]
      [ManualRefCounts]
      internal override UIntPtr AllocateObjectMemory(UIntPtr numBytes,
                                                     uint alignment,
                                                     Thread currentThread) {
          // "numBytes" must be in multiples of double words
          // (four bytes). Note that it includes the space for
          // the object header field.

          VTable.Assert(Util.dwordAlign(numBytes) == numBytes,
                        @"Util.dwordAlign(numBytes) == numBytes");

          UIntPtr resultAddr;
          if (GC.HeapSizeConfigurable) {
              resultAddr = AllocateObjectMemoryFast(numBytes,
                                                    alignment,
                                                    currentThread);
              if (resultAddr == UIntPtr.Zero) {
                  resultAddr =
                      AllocateObjectMemorySlow(numBytes,
                                               alignment,
                                               currentThread);
              }
          } else { // Old collection-triggering scheme.
              if (delayedDeallocationLength > collectionTrigger) {
                  GC.Collect();
              }
              resultAddr = SegregatedFreeList.Allocate(currentThread,
                                                       numBytes,
                                                       alignment);
          }

          return resultAddr;
      }

      [Inline]
      [ManualRefCounts]
      private UIntPtr AllocateObjectMemoryFast(UIntPtr numBytes,
                                               uint alignment,
                                               Thread currentThread) {
          UIntPtr resultAddr =
              SegregatedFreeList.AllocateFast(currentThread,
                                              numBytes,
                                              alignment);
          return resultAddr;
      }

      [ManualRefCounts]
      [DisableNullChecks]
      private UIntPtr AllocateObjectMemorySlow(UIntPtr numBytes,
                                               uint alignment,
                                               Thread currentThread) {
          VTable.Assert(GC.HeapSizeConfigurable,
                        @"GC.HeapSizeConfigurable");

          // Allocate on "slow" path, noting levels before and after.
          uint before = (uint)SegregatedFreeList.AllocatedPages;
          UIntPtr resultAddr =
              SegregatedFreeList.AllocateSlow(currentThread,
                                              numBytes,
                                              alignment);
          uint after = (uint)SegregatedFreeList.AllocatedPages;

          // If page usage hasn't increased, simply return.
          if (!(after > before)) {
              return resultAddr;
          }

          // Otherwise, check if memory usage has crossed a threshold.
          uint zctPages =
              (uint)(ZeroCountTable.Size >> PageTable.PageBits);
          uint heapPages = after+zctPages;
          int maxHeapPages = GC.MaxHeapPages;
          if (heapPages > triggerFraction*maxHeapPages) {
              if (heapPages < maxHeapPages) {
                  GC.Collect();
                  if (++numCollections > numCollectionsTrigger) {
                      numCollections = 0;
                      recycleAllocator();
                  }
              } else {
                  Console.Error.Write("Heap size exceeds ");
                  Console.Error.Write(maxHeapPages <<
                                      (PageTable.PageBits-10));
                  Console.Error.WriteLine("KB!");
                  System.Environment.Exit(-2);
              }
          }

          return resultAddr;
      }

      [Inline]
      [ManualRefCounts]
      protected override void CreateObject(Object obj,
                                           VTable vtable,
                                           Thread currentThread) {
          base.CreateObject(obj, vtable, currentThread);
          obj.REF_STATE = vtable.isAcyclicRefType ? acyclicFlagMask : 0;
          ZeroCountTable.Add(obj);
      }

      internal override int GetGeneration(Object obj) {
          return MinGeneration;
      }

      internal override int MaxGeneration {
          get {
              return (int)PageType.Owner0;
          }
      }

      internal override int MinGeneration {
          get {
              return (int)PageType.Owner0;
          }
      }

      internal override long TotalMemory {
          get {
              UIntPtr allocatorPageCount =
                  SegregatedFreeList.AllocatedPages;
              UIntPtr zctPageCount =
                  (UIntPtr)(ZeroCountTable.Size >> PageTable.PageBits);
              UIntPtr pageCount = allocatorPageCount+zctPageCount;
              return (long)PageTable.RegionSize(pageCount);
          }
      }


      internal override void EnableHeap() {
          // Do nothing
      }

      [NoInline]
      [ManualRefCounts]
      internal override void DestructHeap() {
#if MEASURE_RCPHASES
          Console.Error.Write("DD list processing time (ms): ");
          Console.Error.WriteLine(ddListProcTime);
          Console.Error.Write("DD list processing count: ");
          Console.Error.WriteLine(ddListProcCount);
          Console.Error.Write("\tPLC buffer processing time (ms): ");
          Console.Error.WriteLine(ddListPLCProcTime);
          Console.Error.Write("\tPLC buffer processing count: ");
          Console.Error.WriteLine(ddListPLCProcCount);

          Console.Error.Write("PLC buffer processing time (ms): ");
          Console.Error.WriteLine(plcBufferProcTime);
          Console.Error.Write("PLC buffer processing count: ");
          Console.Error.WriteLine(plcBufferProcCount);
          Console.Error.Write("\tDD list processing time (ms): ");
          Console.Error.WriteLine(plcBufferDDListProcTime);
          Console.Error.Write("\tDD list processing count: ");
          Console.Error.WriteLine(plcBufferDDListProcCount);

          Console.Error.Write("Seg. free time (ms): ");
          Console.Error.WriteLine(segFreeTime);
          Console.Error.Write("Seg. commit time (ms): ");
          Console.Error.WriteLine(segCommitTime);

          Console.Error.Write("Stack scan count: ");
          Console.Error.WriteLine(stackScanCount);
#endif // MEASURE_RCPHASES

          if (VTable.enableGCVerify) {
              VerifyHeap(true);
          }
          base.DestructHeap();
          if (VTable.enableGCProfiling) {
              if (forceCycleCollectionAtEnd) {
                  processPLCBuffer();
              }

              Console.Error.Write("Cycle collections: ");
              Console.Error.WriteLine(cycleCollections);
              Console.Error.Write("Max. Cyclic garbage (B): ");
              Console.Error.WriteLine(maxCyclicGarbage);
              Console.Error.Write("Total Cyclic garbage (B): ");
              Console.Error.WriteLine(totalCyclicGarbage);

              if (DeferredReferenceCountingCollector.ProfilingMode) {
                  EmitRefCountsProfile();
              }
          }
      }

      [NoInline]
      [ManualRefCounts]
      internal override void VerifyHeap(bool beforeCollection) {
          VTable.Assert(DeferredReferenceCountingCollector.VerificationMode,
                        @"DeferredReferenceCountingCollector.VerificationMode");

          if (!canVerifyHeap) {
              return;
          }

          isInGC = true;

          CallStack.ScanStacks(stackRefCountIncrementer,
                               stackRefCountIncrementer);
          // Clean up ZeroCountTable
          ZeroCountTable.ProcessZeroCountTable();

          while (nonEmptyDDList()) {
              // Ensure the integrity of the delayed deallocation list.
              deallocationListChecker();

              // Deallocate objects on the delayed deallocation list.
              purgeDeallocationList();

              // Capture leaked cycles.
              processPLCBuffer();
          }

          // Recycle allocator.
          recycleAllocator();

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

          // Reconcile with actual reference count.
          SegregatedFreeList.VisitAllObjects(backupReconciler);

          // Actual leaks (refCount > 0 and backup refCount = 0).
          leakAccumulator.Initialize();
          SegregatedFreeList.VisitAllObjects(leakAccumulator);
          VTable.DebugPrint("Leaked storage: ");
          VTable.DebugPrint((int)leakAccumulator.Size);
          VTable.DebugPrint("B");

          if (VerifyLeakedCycles) {
              // Find leaked data that should have been reclaimed.
              // (If L is the set of all leaked nodes, and L' the
              // transitive closure of leaked cycles, then L-L' is
              // the set of nodes that should have been captured
              // by a pure reference counting collector.)
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

          CallStack.ScanStacks(stackRefCountDecrementer,
                               stackRefCountDecrementer);
          isInGC = false;
      }

      internal override UIntPtr FindObjectAddr(UIntPtr interiorPtr) {
          return SegregatedFreeList.Find(interiorPtr);
      }

      internal override
      void VisitObjects(ObjectLayout.ObjectVisitor objVisitor,
                        UIntPtr lowAddr,
                        UIntPtr highAddr) {
          UIntPtr lowPage = PageTable.Page(lowAddr);
          UIntPtr highPage = PageTable.Page(highAddr);
          SegregatedFreeList.VisitObjects(lowPage,
                                          highPage,
                                          objVisitor);
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      [GCAnnotation(GCOption.NOGC)]
      internal static unsafe void AccumulateRCUpdates(String methodName,
                                                      int methodIndex,
                                                      uint maxIndex,
                                                      int incCount,
                                                      int decCount,
                                                      int nIncCount,
                                                      int nDecCount,
                                                      int aIncCount,
                                                      int aDecCount,
                                                      int nAIncCount,
                                                      int nADecCount,
                                                      int vIncCount,
                                                      int vDecCount,
                                                      int rIncCount,
                                                      int rDecCount) {
          VTable.Assert(DeferredReferenceCountingCollector.ProfilingMode,
                        @"DeferredReferenceCountingCollector.ProfilingMode");

          // Return if the page table hasn't been set up yet.
          if (PageTable.pageTableCount == UIntPtr.Zero) {
              return;
          }

          if (methodNames == null) {
              VTable.Assert(increments == null,
                            @"increments == null");
              VTable.Assert(decrements == null,
                            @"decrements == null");
              VTable.Assert(nonNullIncrements == null,
                            @"nonNullIncrements == null");
              VTable.Assert(nonNullDecrements == null,
                            @"nonNullDecrements == null");
              VTable.Assert(aIncrements == null,
                            @"aIncrements == null");
              VTable.Assert(aDecrements == null,
                            @"aDecrements == null");
              VTable.Assert(nonNullAIncrements == null,
                            @"nonNullAIncrements == null");
              VTable.Assert(nonNullADecrements == null,
                            @"nonNullADecrements == null");
              VTable.Assert(vIncrements == null,
                            @"vIncrements == null");
              VTable.Assert(vDecrements == null,
                            @"vDecrements == null");
              VTable.Assert(rIncrements == null,
                            @"rIncrements == null");
              VTable.Assert(rDecrements == null,
                            @"rDecrements == null");

              // Allocate storage for the tables. Note that this is
              // requisitioned directly from the memory manager. Care
              // should be taken to ensure that AccumulateRCUpdates
              // does not indirectly call methods that may have
              // compiler-inserted RC updates.
              VTable strArrayVtable =
                  ((RuntimeType)typeof(String[])).classVtable;
              VTable intArrayVtable =
                  ((RuntimeType)typeof(int[])).classVtable;
              UIntPtr methodNamesSize =
                  ObjectLayout.ArraySize(strArrayVtable, maxIndex+1);
              UIntPtr incrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr decrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr nonNullIncrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr nonNullDecrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr aIncrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr aDecrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr nonNullAIncrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr nonNullADecrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr vIncrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr vDecrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr rIncrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr rDecrementsSize =
                  ObjectLayout.ArraySize(intArrayVtable, maxIndex+1);
              UIntPtr totalSize =
                  methodNamesSize+
                  incrementsSize+decrementsSize+
                  nonNullIncrementsSize+nonNullDecrementsSize+
                  aIncrementsSize+aDecrementsSize+
                  nonNullAIncrementsSize+nonNullADecrementsSize+
                  vIncrementsSize+vDecrementsSize+
                  rIncrementsSize+rDecrementsSize;

              BumpAllocator profileData =
                  new BumpAllocator(PageType.NonGC);
              UIntPtr profileDataStart =
                  MemoryManager.AllocateMemory(totalSize);
              profileData.SetZeroedRange(profileDataStart, totalSize);
              PageManager.SetStaticDataPages(profileDataStart,
                                             totalSize);

              methodNames =
                  (String[])AllocateArray(ref profileData,
                                          strArrayVtable,
                                          methodNamesSize);
              VTable.Assert(methodNames != null,
                            @"methodNames != null");

              increments =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       incrementsSize);
              VTable.Assert(increments != null,
                            @"increments != null");

              decrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       decrementsSize);
              VTable.Assert(decrements != null,
                            @"decrements != null");

              nonNullIncrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       nonNullIncrementsSize);
              VTable.Assert(nonNullIncrements != null,
                            @"nonNullIncrements != null");

              nonNullDecrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       nonNullDecrementsSize);
              VTable.Assert(nonNullDecrements != null,
                            @"nonNullDecrements != null");

              aIncrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       aIncrementsSize);
              VTable.Assert(aIncrements != null,
                            @"aIncrements != null");

              aDecrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       aDecrementsSize);
              VTable.Assert(aDecrements != null,
                            @"aDecrements != null");

              nonNullAIncrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       nonNullAIncrementsSize);
              VTable.Assert(nonNullAIncrements != null,
                            @"nonNullAIncrements != null");

              nonNullADecrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       nonNullADecrementsSize);
              VTable.Assert(nonNullADecrements != null,
                            @"nonNullADecrements != null");

              vIncrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       vIncrementsSize);
              VTable.Assert(vIncrements != null,
                            @"vIncrements != null");

              vDecrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       vDecrementsSize);
              VTable.Assert(vDecrements != null,
                            @"vDecrements != null");

              rIncrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       rIncrementsSize);
              VTable.Assert(rIncrements != null,
                            @"rIncrements != null");

              rDecrements =
                  (int[])AllocateArray(ref profileData, intArrayVtable,
                                       rDecrementsSize);
              VTable.Assert(rDecrements != null,
                            @"rDecrements != null");

              *(uint*)(Magic.addressOf(methodNames)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(increments)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(decrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(nonNullIncrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(nonNullDecrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(aIncrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(aDecrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(nonNullAIncrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(nonNullADecrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(vIncrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(vDecrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(rIncrements)+
                  PostHeader.Size) = maxIndex+1;
              *(uint*)(Magic.addressOf(rDecrements)+
                  PostHeader.Size) = maxIndex+1;
          }
          VTable.Assert(methodNames.Length == maxIndex+1,
                        @"methodNames.Length == maxIndex+1");
          VTable.Assert(increments.Length == maxIndex+1,
                        @"increments.Length == maxIndex+1");
          VTable.Assert(decrements.Length == maxIndex+1,
                        @"decrements.Length == maxIndex+1");
          VTable.Assert(nonNullIncrements.Length == maxIndex+1,
                        @"nonNullIncrements.Length == maxIndex+1");
          VTable.Assert(nonNullDecrements.Length == maxIndex+1,
                        @"nonNullDecrements.Length == maxIndex+1");
          VTable.Assert(aIncrements.Length == maxIndex+1,
                        @"aIncrements.Length == maxIndex+1");
          VTable.Assert(aDecrements.Length == maxIndex+1,
                        @"aDecrements.Length == maxIndex+1");
          VTable.Assert(nonNullAIncrements.Length == maxIndex+1,
                        @"nonNullAIncrements.Length == maxIndex+1");
          VTable.Assert(nonNullADecrements.Length == maxIndex+1,
                        @"nonNullADecrements.Length == maxIndex+1");
          VTable.Assert(vIncrements.Length == maxIndex+1,
                        @"vIncrements.Length == maxIndex+1");
          VTable.Assert(vDecrements.Length == maxIndex+1,
                        @"vDecrements.Length == maxIndex+1");
          VTable.Assert(rIncrements.Length == maxIndex+1,
                        @"rIncrements.Length == maxIndex+1");
          VTable.Assert(rDecrements.Length == maxIndex+1,
                        @"rDecrements.Length == maxIndex+1");

          if (methodNames[methodIndex] == null) {
              methodNames[methodIndex] = methodName;
          }
          // Not "methodNames[methodIndex] == methodName" because
          // the Equality operator carries compiler-inserted
          // RC updates!
          VTable.Assert(Magic.addressOf(methodNames[methodIndex]) ==
                        Magic.addressOf(methodName),
                        @"Magic.addressOf(methodNames[methodIndex]) ==
                        Magic.addressOf(methodName)");

          increments[methodIndex] += incCount;
          decrements[methodIndex] += decCount;
          nonNullIncrements[methodIndex] += nIncCount;
          nonNullDecrements[methodIndex] += nDecCount;
          aIncrements[methodIndex] += aIncCount;
          aDecrements[methodIndex] += aDecCount;
          nonNullAIncrements[methodIndex] += nAIncCount;
          nonNullADecrements[methodIndex] += nADecCount;
          vIncrements[methodIndex] += vIncCount;
          vDecrements[methodIndex] += vDecCount;
          rIncrements[methodIndex] += rIncCount;
          rDecrements[methodIndex] += rDecCount;
      }

      [ManualRefCounts]
      internal static Object AllocateArray(ref BumpAllocator profileData,
                                           VTable vtable,
                                           UIntPtr numBytes) {
          UIntPtr resultAddr =
              profileData.AllocateFast(numBytes, vtable.baseAlignment);
          Object result = Magic.fromAddress(resultAddr);
          uint refState = markFlagMask;
          result.REF_STATE = vtable.isAcyclicRefType ?
              (acyclicFlagMask | refState) : refState;
          result.vtable = vtable;
          return result;
      }

      [NoInline]
      [ManualRefCounts]
      internal static void EmitRefCountsProfile() {
          VTable.Assert(DeferredReferenceCountingCollector.ProfilingMode,
                        @"DeferredReferenceCountingCollector.ProfilingMode");

          if (methodNames == null) { // No RC updates present.
              return;
          }
          VTable.Assert(increments != null,
                        @"increments != null");
          VTable.Assert(decrements != null,
                        @"decrements != null");
          VTable.Assert(nonNullIncrements != null,
                        @"nonNullIncrements != null");
          VTable.Assert(nonNullDecrements != null,
                        @"nonNullDecrements != null");
          VTable.Assert(aIncrements != null,
                        @"aIncrements != null");
          VTable.Assert(aDecrements != null,
                        @"aDecrements != null");
          VTable.Assert(nonNullAIncrements != null,
                        @"nonNullAIncrements != null");
          VTable.Assert(nonNullADecrements != null,
                        @"nonNullADecrements != null");
          VTable.Assert(vIncrements != null,
                        @"vIncrements != null");
          VTable.Assert(vDecrements != null,
                        @"vDecrements != null");
          VTable.Assert(rIncrements != null,
                        @"rIncrements != null");
          VTable.Assert(rDecrements != null,
                        @"rDecrements != null");

          // Bubble sort in decreasing order of sums.
          for (int i = 0; i < methodNames.Length; i++) {
              for (int j = methodNames.Length-1; j > i; j--) {
                  if (increments[j]+decrements[j]+
                      nonNullIncrements[j]+nonNullDecrements[j]+
                      aIncrements[j]+aDecrements[j]+
                      nonNullAIncrements[j]+nonNullADecrements[j] >
                      increments[j-1]+decrements[j-1]+
                      nonNullIncrements[j-1]+nonNullDecrements[j-1]+
                      aIncrements[j-1]+aDecrements[j-1]+
                      nonNullAIncrements[j-1]+nonNullADecrements[j-1]) {
                      // Swap contents.
                      int temp = increments[j];
                      increments[j] = increments[j-1];
                      increments[j-1] = temp;

                      temp = decrements[j];
                      decrements[j] = decrements[j-1];
                      decrements[j-1] = temp;

                      temp = nonNullIncrements[j];
                      nonNullIncrements[j] = nonNullIncrements[j-1];
                      nonNullIncrements[j-1] = temp;

                      temp = nonNullDecrements[j];
                      nonNullDecrements[j] = nonNullDecrements[j-1];
                      nonNullDecrements[j-1] = temp;

                      temp = aIncrements[j];
                      aIncrements[j] = aIncrements[j-1];
                      aIncrements[j-1] = temp;

                      temp = aDecrements[j];
                      aDecrements[j] = aDecrements[j-1];
                      aDecrements[j-1] = temp;

                      temp = nonNullAIncrements[j];
                      nonNullAIncrements[j] = nonNullAIncrements[j-1];
                      nonNullAIncrements[j-1] = temp;

                      temp = nonNullADecrements[j];
                      nonNullADecrements[j] = nonNullADecrements[j-1];
                      nonNullADecrements[j-1] = temp;

                      temp = vIncrements[j];
                      vIncrements[j] = vIncrements[j-1];
                      vIncrements[j-1] = temp;

                      temp = vDecrements[j];
                      vDecrements[j] = vDecrements[j-1];
                      vDecrements[j-1] = temp;

                      temp = rIncrements[j];
                      rIncrements[j] = rIncrements[j-1];
                      rIncrements[j-1] = temp;

                      temp = rDecrements[j];
                      rDecrements[j] = rDecrements[j-1];
                      rDecrements[j-1] = temp;

                      String s = methodNames[j];
                      methodNames[j] = methodNames[j-1];
                      methodNames[j-1] = s;
                  }
              }
          }

          VTable.DebugPrint("\n");
          VTable.DebugPrint("Incs\t\tDecs");
          VTable.DebugPrint("\t\tNIncs\t\tNDecs");
          VTable.DebugPrint("\t\tAIncs\t\tADecs");
          VTable.DebugPrint("\t\tNAIncs\t\tNADecs");
          VTable.DebugPrint("\t\tV+\t\tV-");
          VTable.DebugPrint("\t\tR+\t\tR-");
          VTable.DebugPrint("\t\tMethod\n");
          VTable.DebugPrint("----\t\t----");
          VTable.DebugPrint("\t\t-----\t\t-----");
          VTable.DebugPrint("\t\t-----\t\t-----");
          VTable.DebugPrint("\t\t------\t\t------");
          VTable.DebugPrint("\t\t--\t\t--");
          VTable.DebugPrint("\t\t--\t\t--");
          VTable.DebugPrint("\t\t------\n");
          VTable.DebugPrint("\n");
          for (int i = 0; i < methodNames.Length; i++) {
              if (increments[i]+nonNullIncrements[i]+
                  aIncrements[i]+nonNullAIncrements[i] == 0 &&
                  decrements[i]+nonNullDecrements[i]+
                  aDecrements[i]+nonNullADecrements[i] == 0) {
                  continue;
              }
              VTable.DebugPrint(increments[i]);
              if (increments[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(decrements[i]);
              if (decrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(nonNullIncrements[i]);
              if (nonNullIncrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(nonNullDecrements[i]);
              if (nonNullDecrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(aIncrements[i]);
              if (aIncrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(aDecrements[i]);
              if (aDecrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(nonNullAIncrements[i]);
              if (nonNullAIncrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(nonNullADecrements[i]);
              if (nonNullADecrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(vIncrements[i]);
              if (vIncrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(vDecrements[i]);
              if (vDecrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(rIncrements[i]);
              if (rIncrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(rDecrements[i]);
              if (rDecrements[i] < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(methodNames[i]);
              VTable.DebugPrint("\n");
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static unsafe void IndirectIncrementRefCount(UIntPtr loc) {
          UIntPtr pageLoc = PageTable.Page(loc);
          PageType pageType = PageTable.Type(pageLoc);
          if (pageType == PageType.Stack) {
              return;
          }

          UIntPtr objAddr = *(UIntPtr*)loc;
          Object obj = Magic.fromAddress(objAddr);
          if (obj != null) {
              NonNullIncrementRefCount(obj);
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static unsafe void IndirectDecrementRefCount(UIntPtr loc) {
          UIntPtr pageLoc = PageTable.Page(loc);
          PageType pageType = PageTable.Type(pageLoc);
          if (pageType == PageType.Stack) {
              return;
          }

          UIntPtr objAddr = *(UIntPtr*)loc;
          Object obj = Magic.fromAddress(objAddr);
          if (obj != null) {
              NonNullDecrementRefCount(obj);
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      [GCAnnotation(GCOption.NOGC)]
      internal static unsafe void nonNullLocalIncrementRefCount(Object obj) {
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
          } else {
              obj.REF_STATE = refState+1;

              // Exclude the object from leaked cycle processing.
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  // If the object is present in the PLC ("potentially
                  // leaked cycle") buffer, remove it.
                  if (index != 0) {
                      // Reset the PLC index in the object.
                      SetPLCIndex(obj, 0);
                      removeFromPLCBuffer(index);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void IncrementRefCount(Object obj) {
          if (obj == null) {
              return;
          }

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
              // Include the object for leaked cycle processing.
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  // Insert the object into the PLC buffer only
                  // if it hasn't already been inserted.
                  if (index == 0) {
                      addToPLCBuffer(obj);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
          } else {
              obj.REF_STATE = refState+1;

              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index != 0) {
                      SetPLCIndex(obj, 0);
                      removeFromPLCBuffer(index);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void NonNullIncrementRefCount(Object obj) {
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index == 0) {
                      addToPLCBuffer(obj);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
          } else {
              obj.REF_STATE = refState+1;

              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index != 0) {
                      SetPLCIndex(obj, 0);
                      removeFromPLCBuffer(index);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
          }
      }

      [Inline]
      [ManualRefCounts]
      [RequiredByBartok]
      [GCAnnotation(GCOption.NOGC)]
      internal static void AcyclicIncrementRefCount(Object obj) {
          if (obj == null) {
              return;
          }

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
          } else {
              obj.REF_STATE = refState+1;
          }

#if DEBUG
          uint index = GetPLCIndex(obj);
          VTable.Assert(index == 0,
                        @"index == 0");
#endif // DEBUG
      }

      [Inline]
      [ManualRefCounts]
      [RequiredByBartok]
      [GCAnnotation(GCOption.NOGC)]
      internal static void NonNullAcyclicIncrementRefCount(Object obj) {
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
          } else {
              obj.REF_STATE = refState+1;
          }

#if DEBUG
          uint index = GetPLCIndex(obj);
          VTable.Assert(index == 0,
                        @"index == 0");
#endif // DEBUG
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      [GCAnnotation(GCOption.NOGC)]
      internal static void PLCFreeNonNullLocalIncrementRefCount(Object obj) {
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
          } else {
              obj.REF_STATE = refState+1;
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void PLCFreeIncrementRefCount(Object obj) {
          if (obj == null) {
              return;
          }

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index == 0) {
                      addToPLCBuffer(obj);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
          } else {
              obj.REF_STATE = refState+1;
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void PLCFreeNonNullIncrementRefCount(Object obj) {
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) < refCountMask,
                        @"(refState & refCountMask) < refCountMask");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");

          if ((refState & markFlagMask) != 0) {
              ZeroCountTable.Remove(obj);
              refState = obj.REF_STATE;
              VTable.Assert((refState & markFlagMask) == 0,
                            @"(refState & markFlagMask) == 0");

              obj.REF_STATE = 1 | (refState & ~refCountMask);
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index == 0) {
                      addToPLCBuffer(obj);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
          } else {
              obj.REF_STATE = refState+1;
          }
      }

      [NoInline]
      [ManualRefCounts]
      internal static void nonNullLocalDecrementRefCount(Object obj)  {
          VTable.Assert(isInGC,
                        @"isInGC");
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) >= 0,
                        @"(refState & refCountMask) >= 0");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");
          VTable.Assert((refState & markFlagMask) == 0,
                        @"(refState & markFlagMask) == 0");

          if ((refState & refCountMask) == 1) {
              MultiUseWord muw = MultiUseWord.GetForObject(obj);
              if (muw.IsMonitorOrInflatedTag()) {
                  MultiUseWord.RefCountGCDeadObjHook(muw);
              }

              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index != 0) {
                      SetPLCIndex(obj, 0);
                      removeFromPLCBuffer(index);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG

              deallocateLazily(obj);
              obj.REF_STATE--;
          } else {
              VTable.Assert((refState & refCountMask) > 0,
                            @"(refState & refCountMask) > 0");

              // Include the object for leaked cycle processing.
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index == 0) {
                      addToPLCBuffer(obj);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG
              obj.REF_STATE--;
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void DecrementRefCount(Object obj) {
          if (obj == null) {
              return;
          }

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) >= 0,
                        @"(refState & refCountMask) >= 0");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }

          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");
          VTable.Assert((refState & markFlagMask) == 0,
                        @"(refState & markFlagMask) == 0");

          if ((refState & refCountMask) == 1) {
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index != 0) {
                      SetPLCIndex(obj, 0);
                      removeFromPLCBuffer(index);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG

              ZeroCountTable.Add(obj);
          } else {
              VTable.Assert((refState & refCountMask) > 1,
                            @"(refState & refCountMask) > 1");

              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index == 0) {
                      addToPLCBuffer(obj);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG

              // May GC, reload refState, and check again
              refState = obj.REF_STATE;
              if ((refState & refCountMask) == 1) {
                  if ((refState & acyclicFlagMask) == 0) {
                      uint index = GetPLCIndex(obj);
                      if (index != 0) {
                          SetPLCIndex(obj, 0);
                          removeFromPLCBuffer(index);
                      }
                  }
#if DEBUG
                  else {
                      uint index = GetPLCIndex(obj);
                      VTable.Assert(index == 0,
                                    @"index == 0");
                  }
#endif // DEBUG

                  ZeroCountTable.Add(obj); // should not GC
              } else  {
                  obj.REF_STATE = refState-1;
              }
          }
      }

      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void NonNullDecrementRefCount(Object obj) {
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) >= 0,
                        @"(refState & refCountMask) >= 0");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }

          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");
          VTable.Assert((refState & markFlagMask) == 0,
                        @"(refState & markFlagMask) == 0");

          if ((refState & refCountMask) == 1) {
              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index != 0) {
                      SetPLCIndex(obj, 0);
                      removeFromPLCBuffer(index);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG

              ZeroCountTable.Add(obj);
          } else {
              VTable.Assert((refState & refCountMask) > 1,
                            @"(refState & refCountMask) > 1");

              if ((refState & acyclicFlagMask) == 0) {
                  uint index = GetPLCIndex(obj);
                  if (index == 0) {
                      addToPLCBuffer(obj);
                  }
              }
#if DEBUG
              else {
                  uint index = GetPLCIndex(obj);
                  VTable.Assert(index == 0,
                                @"index == 0");
              }
#endif // DEBUG

              // May GC, reload refState, and check again
              refState = obj.REF_STATE;
              if ((refState & refCountMask) == 1) {
                  if ((refState & acyclicFlagMask) == 0) {
                      uint index = GetPLCIndex(obj);
                      if (index != 0) {
                          SetPLCIndex(obj, 0);
                          removeFromPLCBuffer(index);
                      }
                  }
#if DEBUG
                  else {
                      uint index = GetPLCIndex(obj);
                      VTable.Assert(index == 0,
                                    @"index == 0");
                  }
#endif // DEBUG

                  ZeroCountTable.Add(obj); // should not GC
              } else  {
                  obj.REF_STATE = refState-1;
              }
          }
      }

      [Inline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void AcyclicDecrementRefCount(Object obj) {
          if (obj == null) {
              return;
          }

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) >= 0,
                        @"(refState & refCountMask) >= 0");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }

          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");
          VTable.Assert((refState & markFlagMask) == 0,
                        @"(refState & markFlagMask) == 0");

          if ((refState & refCountMask) == 1) {
#if DEBUG
              uint index = GetPLCIndex(obj);
              VTable.Assert(index == 0,
                            @"index == 0");
#endif // DEBUG

              ZeroCountTable.Add(obj);
          } else {
              VTable.Assert((refState & refCountMask) > 1,
                            @"(refState & refCountMask) > 1");

#if DEBUG
              uint index = GetPLCIndex(obj);
              VTable.Assert(index == 0,
                            @"index == 0");
#endif // DEBUG

              // May GC, reload refState, and check again
              refState = obj.REF_STATE;
              if ((refState & refCountMask) == 1) {
                  ZeroCountTable.Add(obj); // should not GC
              } else {
                  obj.REF_STATE = refState-1;
              }
          }
      }

      [Inline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void NonNullAcyclicDecrementRefCount(Object obj) {
          VTable.Assert(obj != null,
                        @"obj != null");

          uint refState = obj.REF_STATE;
          VTable.Assert((refState & refCountMask) >= 0,
                        @"(refState & refCountMask) >= 0");

          if ((refState & countingONFlagMask) == 0) {
              return;
          }

          VTable.Assert((refState & refCountMask) > 0,
                        @"(refState & refCountMask) > 0");
          VTable.Assert((refState & markFlagMask) == 0,
                        @"(refState & markFlagMask) == 0");

          if ((refState & refCountMask) == 1) {
#if DEBUG
              uint index = GetPLCIndex(obj);
              VTable.Assert(index == 0,
                            @"index == 0");
#endif // DEBUG

              ZeroCountTable.Add(obj);
          } else {
              VTable.Assert((refState & refCountMask) > 1,
                            @"(refState & refCountMask) > 1");

#if DEBUG
              uint index = GetPLCIndex(obj);
              VTable.Assert(index == 0,
                            @"index == 0");
#endif // DEBUG

              // May GC, reload refState, and check again
              refState = obj.REF_STATE;
              if ((refState & refCountMask) == 1) {
                  ZeroCountTable.Add(obj); // should not GC
              } else {
                  obj.REF_STATE = refState-1;
              }
          }
      }


      [RequiredByBartok]
      [DisableNullChecks]
      internal static void IncrementReferentRefCounts(UIntPtr objAddr,
                                                      VTable vtable) {
          refCountIncrementer.VisitReferenceFields(objAddr, vtable);
      }

      [RequiredByBartok]
      [DisableNullChecks]
      internal static void DecrementReferentRefCounts(UIntPtr objAddr,
                                                      VTable vtable) {
          refCountDecrementer.VisitReferenceFields(objAddr, vtable);
      }

      [ManualRefCounts]
      [DisableNullChecks]
      internal static unsafe void IncrementReferentRefCounts
          (UIntPtr objAddr,
           VTable vtable,
           int start,
           int span) {
          uint objTag = (uint)vtable.pointerTrackingMask & 0xf;

          switch (objTag) {
              case ObjectLayout.PTR_VECTOR_TAG:
              case ObjectLayout.PTR_ARRAY_TAG: {
#if DEBUG
                  Object obj = Magic.fromAddress(objAddr);
                  Array array = Magic.toArray(obj);
                  VTable.Assert(span <= array.Length,
                                @"span <= array.Length");
#endif // DEBUG

                  UIntPtr* baseAddr = (UIntPtr*)(objAddr+
                      vtable.baseLength-PreHeader.Size);
                  UIntPtr* begin = baseAddr+start;
                  UIntPtr* end = begin+span;
                  for (UIntPtr* el = begin; el < end; el++) {
                      UIntPtr addr = *el;
                      incrementRefCount(addr);
                  }
                  break;
              }

              case ObjectLayout.OTHER_VECTOR_TAG:
              case ObjectLayout.OTHER_ARRAY_TAG: {
                  if (vtable.arrayOf != StructuralType.Struct) {
                      break;
                  }
                  VTable elVTable = vtable.arrayElementClass;
                  uint elMask = (uint)elVTable.pointerTrackingMask;
                  if (elMask == ObjectLayout.SPARSE_TAG ||
                      elMask == ObjectLayout.DENSE_TAG) {
                      break;
                  }
#if DEBUG
                  Object obj = Magic.fromAddress(objAddr);
                  Array array = Magic.toArray(obj);
                  VTable.Assert(span <= array.Length,
                                @"span <= array.Length");
#endif // DEBUG

                  UIntPtr baseAddr = objAddr+vtable.baseLength-
                      PreHeader.Size-PostHeader.Size;
                  int elSize = vtable.arrayElementSize;
                  UIntPtr begin = baseAddr+elSize*start;
                  UIntPtr end = begin+elSize*span;
                  for (UIntPtr el = begin; el < end; el += elSize) {
                      refCountIncrementer.
                      VisitReferenceFields(el, elVTable);
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

      [ManualRefCounts]
      [DisableNullChecks]
      internal static unsafe void DecrementReferentRefCounts
          (UIntPtr objAddr,
           VTable vtable,
           int start,
           int span) {
          uint objTag = (uint)vtable.pointerTrackingMask & 0xf;

          switch (objTag) {
              case ObjectLayout.PTR_VECTOR_TAG:
              case ObjectLayout.PTR_ARRAY_TAG: {
#if DEBUG
                  Object obj = Magic.fromAddress(objAddr);
                  Array array = Magic.toArray(obj);
                  VTable.Assert(span <= array.Length,
                                @"span <= array.Length");
#endif // DEBUG

                  UIntPtr* baseAddr = (UIntPtr*)(objAddr+
                      vtable.baseLength-PreHeader.Size);
                  UIntPtr* begin = baseAddr+start;
                  UIntPtr* end = begin+span;
                  for (UIntPtr* el = begin; el < end; el++) {
                      UIntPtr addr = *el;
                      decrementRefCount(addr);
                  }
                  break;
              }

              case ObjectLayout.OTHER_VECTOR_TAG:
              case ObjectLayout.OTHER_ARRAY_TAG: {
                  if (vtable.arrayOf != StructuralType.Struct) {
                      break;
                  }
                  VTable elVTable = vtable.arrayElementClass;
                  uint elMask = (uint)elVTable.pointerTrackingMask;
                  if (elMask == ObjectLayout.SPARSE_TAG ||
                      elMask == ObjectLayout.DENSE_TAG) {
                      break;
                  }
#if DEBUG
                  Object obj = Magic.fromAddress(objAddr);
                  Array array = Magic.toArray(obj);
                  VTable.Assert(span <= array.Length,
                                @"span <= array.Length");
#endif // DEBUG

                  UIntPtr baseAddr = objAddr+vtable.baseLength-
                      PreHeader.Size-PostHeader.Size;
                  int elSize = vtable.arrayElementSize;
                  UIntPtr begin = baseAddr+elSize*start;
                  UIntPtr end = begin+elSize*span;
                  for (UIntPtr el = begin; el < end; el += elSize) {
                      refCountDecrementer.
                      VisitReferenceFields(el, elVTable);
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


      [Inline]
      [ManualRefCounts]
      internal static void deallocateLazily(Object obj) {
#if DEBUG
          uint index = GetPLCIndex(obj);
          VTable.Assert(index == 0,
                        @"index == 0");
#endif // DEBUG

          setNextLink(obj, delayedDeallocationList);
          delayedDeallocationList = obj;
          if (!GC.HeapSizeConfigurable) {
              delayedDeallocationLength++;
          }
      }

      [ManualRefCounts]
      private static void deallocateObjects() {
          int startTicks = 0;
          bool enableGCTiming = VTable.enableGCTiming;
          if (enableGCTiming) {
              VTable.enableGCTiming = false;
              startTicks = Environment.TickCount;
          }

#if MEASURE_RCPHASES
          int ddListTicks = 0;
          bool phaseFlag = ddListPhase;
          if (!phaseFlag) {
              ddListPhase = true;
              ddListTicks = Environment.TickCount;
          }
#endif // MEASURE_RCPHASES

          // Either continue working on old object, or extract
          // a new object from the delayed deallocation list.
          if (objectBeingDeallocated == null) {
              objectBeingDeallocated = extractObjectFromDDList();
          }
          int work = 0;
          Object obj = objectBeingDeallocated;
          while (obj != null) {
              UIntPtr objAddr = Magic.addressOf(obj);
              VTable vt = obj.vtable;
              uint ptrMask = (uint)vt.pointerTrackingMask;
              bool ongoing;
              do {
                  ongoing = incrementalDecrement(objAddr, vt, ptrMask,
                                                 ref work);
              } while (ongoing && work < deallocationSpan);

              if (!ongoing) { // Release object back to allocator.
                  releaseToAllocator(obj);
                  obj = extractObjectFromDDList();
              }
              if (work >= deallocationSpan) {
                  break;
              }
          }
          objectBeingDeallocated = obj;

#if MEASURE_RCPHASES
          if (!phaseFlag) {
              int elapsed = Environment.TickCount-ddListTicks;
              if (plcBufferPhase) {
                  plcBufferDDListProcTime += elapsed;
                  plcBufferDDListProcCount++;
              } else {
                  ddListProcTime += elapsed;
                  ddListProcCount++;
              }
              ddListPhase = false;
          }
#endif // MEASURE_RCPHASES

          if (enableGCTiming) {
              int elapsedTicks = Environment.TickCount-startTicks;
              BaseCollector.RegisterPause(elapsedTicks);
              VTable.enableGCTiming = true;
          }
      }

      [ManualRefCounts]
      private static Object extractObjectFromDDList() {
          Object obj = delayedDeallocationList;
          if (obj != null) {
              delayedDeallocationList = getNextLink(obj);
              if (!GC.HeapSizeConfigurable) {
                  delayedDeallocationLength--;
              }

              UIntPtr objAddr = Magic.addressOf(obj);
              initIncrementalDecrement(objAddr, obj.vtable);

#if DEBUG
              UIntPtr page = PageTable.Page(objAddr);
              VTable.Assert(PageTable.IsGcPage(page),
                            @"PageTable.IsGcPage(page)");
#endif // DEBUG
          }

          return obj;
      }

      [ManualRefCounts]
      [DisableNullChecks]
      private static unsafe void initIncrementalDecrement
          (UIntPtr objAddr,
           VTable vtable) {
          uint ptrMask = (uint)vtable.pointerTrackingMask;
          uint objTag = ptrMask & 0xf;

          switch (objTag) {
              case ObjectLayout.SPARSE_TAG:
              case ObjectLayout.DENSE_TAG:
              case ObjectLayout.STRING_TAG : {
                  break;
              }

              case ObjectLayout.PTR_VECTOR_TAG:
              case ObjectLayout.OTHER_VECTOR_TAG:
              case ObjectLayout.PTR_ARRAY_TAG:
              case ObjectLayout.OTHER_ARRAY_TAG: {
                  Object obj = Magic.fromAddress(objAddr);
                  Array array = Magic.toArray(obj);
                  setLastTracked(objAddr, array.Length);
                  break;
              }

              default: {
                  int* ptrDescriptor = (int*)ptrMask;
                  int initialCount = *ptrDescriptor;
                  setLastTracked(objAddr, initialCount);
                  break;
              }
          }
      }

      [ManualRefCounts]
      [DisableNullChecks]
      private static unsafe bool incrementalDecrement(UIntPtr objAddr,
                                                      VTable vtable,
                                                      uint ptrMask,
                                                      ref int work) {
          uint objTag = ptrMask & 0xf;
          bool ongoing = false;

          if (objTag == ObjectLayout.SPARSE_TAG) {
              UIntPtr* sparseObj = (UIntPtr*)objAddr;
              work += 7;
              for (ptrMask >>= 4; ptrMask != 0; ptrMask >>= 4) {
                  uint index = ptrMask & 0xf;
                  UIntPtr* loc = sparseObj+unchecked((int)index);
                  UIntPtr addr = *loc;
                  localDecrementRefCount(addr);
              }
          } else if (objTag == ObjectLayout.DENSE_TAG) {
              UIntPtr* denseObj = (UIntPtr*)(objAddr+PostHeader.Size);
              work += 28;
              for (ptrMask >>= 4; ptrMask != 0; ptrMask >>= 1) {
                  if ((ptrMask & 0x1) != 0) {
                      UIntPtr addr = *denseObj;
                      localDecrementRefCount(addr);
                  }
                  denseObj++;
              }
          } else if (objTag == ObjectLayout.OTHER_VECTOR_TAG ||
                     objTag == ObjectLayout.OTHER_ARRAY_TAG) {
              if (vtable.arrayOf != StructuralType.Struct) {
                  return ongoing;
              }
              VTable elVTable = vtable.arrayElementClass;
              uint elMask = (uint)elVTable.pointerTrackingMask;
              if (elMask == ObjectLayout.SPARSE_TAG ||
                  elMask == ObjectLayout.DENSE_TAG) {
                  return ongoing;
              }
              uint elObjTag = elMask & 0xf;
              VTable.Assert(elObjTag == ObjectLayout.SPARSE_TAG ||
                            elObjTag == ObjectLayout.DENSE_TAG,
                            @"elObjTag == ObjectLayout.SPARSE_TAG ||
                            elObjTag == ObjectLayout.DENSE_TAG");
              VTable.Assert(work < deallocationSpan,
                            @"work < deallocationSpan");

              int prev = getLastTracked(objAddr);
              int elShift = elObjTag == ObjectLayout.SPARSE_TAG ? 2 : 4;
              int workChunk = ((deallocationSpan-work) >> elShift)+1;
              int last = prev > workChunk ? prev-workChunk : 0;
              ongoing = last != 0;
              if (ongoing) {
                  setLastTracked(objAddr, last);
              }

              UIntPtr baseAddr = objAddr+vtable.baseLength-
                  PreHeader.Size-PostHeader.Size;
              int size = vtable.arrayElementSize;
              UIntPtr begin = baseAddr+(UIntPtr)(size*(prev-1));
              UIntPtr end = baseAddr+(UIntPtr)(size*last);
              for (UIntPtr el = begin; el >= end; el -= size) {
                  incrementalDecrement(el, elVTable, elMask, ref work);
              }
          } else if (objTag != ObjectLayout.STRING_TAG) {
              VTable.Assert(work < deallocationSpan,
                            @"work < deallocationSpan");

              int prev = getLastTracked(objAddr);
              int workChunk = deallocationSpan-work;
              int last = prev > workChunk ? prev-workChunk : 0;
              ongoing = last != 0;
              if (ongoing) {
                  setLastTracked(objAddr, last);
              }
              work += prev-last;

              if (objTag == ObjectLayout.PTR_VECTOR_TAG ||
                  objTag == ObjectLayout.PTR_ARRAY_TAG) {
                  UIntPtr baseAddr =
                      objAddr+vtable.baseLength-PreHeader.Size;
                  UIntPtr* begin = (UIntPtr*)baseAddr+prev-1;
                  UIntPtr* end = (UIntPtr*)baseAddr+last;
                  for (UIntPtr* el = begin; el >= end; el--) {
                      UIntPtr addr = *el;
                      localDecrementRefCount(addr);
                  }
              } else {
                  VTable.Assert((objTag & 0x1) == 0,
                                @"(objTag & 0x1) == 0");

                  UIntPtr* largeObj = (UIntPtr*)objAddr;
                  int* ptrDescriptor = (int*)ptrMask;
                  for (int index = prev; index > last; index--) {
                      UIntPtr* loc = largeObj+*(ptrDescriptor+index);
                      UIntPtr addr = *loc;
                      localDecrementRefCount(addr);
                  }
              }
          }

          return ongoing;
      }

      [Inline]
      [ManualRefCounts]
      private static void localDecrementRefCount(UIntPtr objAddr) {
          if (objAddr != UIntPtr.Zero) {
              nonNullLocalDecrementRefCount(Magic.fromAddress(objAddr));
          }
      }

      [Inline]
      [ManualRefCounts]
      private static void incrementRefCount(UIntPtr objAddr) {
          if (objAddr != UIntPtr.Zero) {
              NonNullIncrementRefCount(Magic.fromAddress(objAddr));
          }
      }

      [Inline]
      [ManualRefCounts]
      private static void decrementRefCount(UIntPtr objAddr) {
          if (objAddr != UIntPtr.Zero) {
              NonNullDecrementRefCount(Magic.fromAddress(objAddr));
          }
      }


      [ManualRefCounts]
      [DisableNullChecks]
      private static Object getNextLink(Object obj) {
          return Magic.fromAddress(MultiUseWord.GetValForObject(obj));
      }

      [ManualRefCounts]
      [DisableNullChecks]
      private static void setNextLink(Object obj, Object next) {
          MultiUseWord.SetValForObject(obj, Magic.addressOf(next));
      }

      [ManualRefCounts]
      [DisableNullChecks]
      private static int getLastTracked(UIntPtr objAddr) {
          Object obj = Magic.fromAddress(objAddr);
          return unchecked((int)(uint)MultiUseWord.GetValForObject(obj));
      }

      [ManualRefCounts]
      [DisableNullChecks]
      private static void setLastTracked(UIntPtr objAddr, int last) {
          Object obj = Magic.fromAddress(objAddr);
          MultiUseWord.SetValForObject(obj, (UIntPtr)unchecked((uint)last));
      }

      [ManualRefCounts]
      private static UIntPtr getBackupRefCount(Object obj) {
          return ((DeferredRCVerificationObject)obj).preHeader.
                 backupRefCount;
      }

      [ManualRefCounts]
      private static void setBackupRefCount(Object obj, UIntPtr count) {
          ((DeferredRCVerificationObject)obj).preHeader.
          backupRefCount = count;
      }

      [ManualRefCounts]
      private static UIntPtr getDfsDiscoveryTime(Object obj) {
          return ((DeferredRCVerificationObject)obj).preHeader.
                 dfsDiscoveryTime;
      }

      [ManualRefCounts]
      private static void setDfsDiscoveryTime(Object obj,
                                              UIntPtr time) {
          ((DeferredRCVerificationObject)obj).preHeader.
          dfsDiscoveryTime = time;
      }

      [ManualRefCounts]
      private static UIntPtr getDfsFinishingTime(Object obj) {
          return ((DeferredRCVerificationObject)obj).preHeader.
                 dfsFinishingTime;
      }

      [ManualRefCounts]
      private static void setDfsFinishingTime(Object obj,
                                              UIntPtr time) {
          ((DeferredRCVerificationObject)obj).preHeader.
          dfsFinishingTime = time;
      }

      [ManualRefCounts]
      private static void allocatePLCBuffer(uint count) {
          VTable vtable = ((RuntimeType)typeof(UIntPtr[])).classVtable;

          plcRawSize = ObjectLayout.ArraySize(vtable, count);
          plcRawAddr = MemoryManager.AllocateMemory(plcRawSize);
          PageManager.SetStaticDataPages(plcRawAddr, plcRawSize);

          BumpAllocator pool = new BumpAllocator(PageType.NonGC);
          pool.SetZeroedRange(plcRawAddr, plcRawSize);
          uint alignment = vtable.baseAlignment;
          UIntPtr addr = pool.AllocateFast(plcRawSize, alignment);
          Array result = Magic.toArray(Magic.fromAddress(addr));

          result.InitializeVectorLength(unchecked((int)count));
          result.REF_STATE = 1 & ~countingONFlagMask;
          result.vtable = vtable;

          plcBuffer = Magic.toUIntPtrVector(result);
      }

      [ManualRefCounts]
      [DisableBoundsChecks]
      private static void reallocatePLCBuffer() {
          UIntPtr oldPLCRawSize = plcRawSize;
          UIntPtr oldPLCRawAddr = plcRawAddr;
          UIntPtr[] oldPLCBuffer = plcBuffer;

          uint oldNumEntries = unchecked((uint)oldPLCBuffer.Length);
          uint newNumEntries = oldNumEntries << 1;
          allocatePLCBuffer(newNumEntries);

          UIntPtr[] newPLCBuffer = plcBuffer;
          for (uint i = 0; i < oldNumEntries; i++) {
              newPLCBuffer[i] = oldPLCBuffer[i];
          }

          MemoryManager.FreeMemory(oldPLCRawAddr, oldPLCRawSize);
      }

      [ManualRefCounts]
      [DisableBoundsChecks]
      private static void stitchFreePLCSlots(uint firstFreeSlot) {
          UIntPtr[] plcBuffer =
              DeferredReferenceCountingCollector.plcBuffer;

          int plcNumEntries = plcBuffer.Length;
          for (uint i = firstFreeSlot; i < plcNumEntries-1; i++) {
              plcBuffer[i] = (UIntPtr)(markFlagMask | (i+1));
          }
          plcBuffer[plcNumEntries-1] = (UIntPtr)markFlagMask;
          freePLCHead = firstFreeSlot;
      }

      [ManualRefCounts]
      [DisableBoundsChecks]
      private static void addToPLCBuffer(Object obj) {
          UIntPtr[] plcBuffer =
              DeferredReferenceCountingCollector.plcBuffer;
          uint freePLCHead =
              DeferredReferenceCountingCollector.freePLCHead;

          // Check if free PLC buffer entries are available.
          if (freePLCHead == 0) {
              uint plcNumEntries = unchecked((uint)plcBuffer.Length);
              if ((plcNumEntries < maxPLCNumEntries) || isInGC) {
                  reallocatePLCBuffer();
                  plcBuffer =
                      DeferredReferenceCountingCollector.plcBuffer;
                  stitchFreePLCSlots(plcNumEntries);

                  if (isInGC) {
                      // If in GC, you should not trigger another GC.
                      // Therefore allocate, and set a flag. PLC buffer
                      // will be cleaned up in next step of current GC.
                      needCleanPLCBuffer = true;
                  }
              } else {
                  // NOT in GC, then collect.
                  needCleanPLCBuffer = true;
                  GC.Collect();
              }
              freePLCHead =
                  DeferredReferenceCountingCollector.freePLCHead;
          }
          VTable.Assert((obj.REF_STATE & refCountMask) >= 1,
                        @"obj.REF_STATE & refCountMask >=1");
          VTable.Assert(!ZeroCountTable.isInZCT(obj),
                        @"!ZeroCountTable.isInZCT(obj)");

          // GC.Collect may already add it into the PLC buffer.
          uint index = GetPLCIndex(obj);
          if (index != 0) {
              return;
          }

          // Insert object into the PLC buffer.
          uint entry = (uint)plcBuffer[freePLCHead];
          uint newFreePLCHead = entry & ~markFlagMask;
          plcBuffer[freePLCHead] = Magic.addressOf(obj);

          // Point the object to its slot in the PLC buffer.
          SetPLCIndex(obj, freePLCHead);

          // Update the free PLC entries' head.
          DeferredReferenceCountingCollector.freePLCHead =
              newFreePLCHead;
      }

      [Inline]
      [ManualRefCounts]
      [DisableBoundsChecks]
      internal static void removeFromPLCBuffer(uint index) {
          // The object needs to be removed from the PLC buffer.
          plcBuffer[index] = (UIntPtr)(freePLCHead | markFlagMask);
          freePLCHead = index;
      }

      [ManualRefCounts]
      [DisableNullChecks]
      [DisableBoundsChecks]
      private static void processPLCBuffer() {
          int startTicks = 0;
          bool enableGCTiming = VTable.enableGCTiming;
          if (enableGCTiming) {
              VTable.enableGCTiming = false;
              startTicks = Environment.TickCount;
          }

#if MEASURE_RCPHASES
          int plcBufferTicks = 0;
          bool phaseFlag = plcBufferPhase;
          if (!phaseFlag) {
              plcBufferPhase = true;
              plcBufferTicks = Environment.TickCount;
          }
#endif // MEASURE_RCPHASES

          UIntPtr[] plcBuffer =
              DeferredReferenceCountingCollector.plcBuffer;

          int plcNumEntries = plcBuffer.Length;

          // Let S be the subgraph of heap objects reachable from
          // the PLC buffer. Decrement counts due to references in S.
          for (int i = 1; i < plcNumEntries; i++) {
              UIntPtr objAddr = plcBuffer[i];
              if (((uint)objAddr & markFlagMask) != 0) {
                  continue;
              }

              VTable.Assert(objAddr != UIntPtr.Zero,
                            @"objAddr != UIntPtr.Zero");

              Object obj = Magic.fromAddress(objAddr);
              uint refState = obj.REF_STATE;
              VTable.Assert((refState & countingONFlagMask) != 0,
                            @"(refState & countingONFlagMask) != 0");
              VTable.Assert((refState & acyclicFlagMask) == 0,
                            @"(refState & acyclicFlagMask) == 0");

              if ((refState & markFlagMask) == 0) {
                  obj.REF_STATE = refState | markFlagMask;
                  internalDecrementer.Traverse(objAddr);
              }
          }

          // Objects that now have non-zero counts are those that
          // have references external to S incident on them.
          // Recompute counts due to reachability from such objects.
          for (int i = 1; i < plcNumEntries; i++) {
              UIntPtr objAddr = plcBuffer[i];
              if (((uint)objAddr & markFlagMask) != 0) {
                  continue;
              }

              internalScanner.Traverse(objAddr);
          }

          // String together objects with reference count
          // of zero for reclamation.
          internalReclaimer.Initialize();
          for (int i = 1; i < plcNumEntries; i++) {
              UIntPtr objAddr = plcBuffer[i];
              if (((uint)objAddr & markFlagMask) != 0) {
                  continue;
              }

              Object obj = Magic.fromAddress(objAddr);
              uint refState = obj.REF_STATE;
              const uint mask = markFlagMask | acyclicFlagMask;
              VTable.Assert((refState & mask) == 0 ||
                            refState == ~countingONFlagMask,
                            @"(refState & mask) == 0 ||
                            refState == ~countingONFlagMask");

              if (refState == countingONFlagMask) {
                  internalReclaimer.Traverse(objAddr);
              } else {
                  SetPLCIndex(obj, 0);
              }
          }
          ulong reclaimedBytes = 0;
          Object reclaimedObj = internalReclaimer.ReclaimedObjects;
          while (reclaimedObj != null) {
              if (VTable.enableGCProfiling) {
                  UIntPtr size = ObjectLayout.Sizeof(reclaimedObj);
                  reclaimedBytes += (ulong)size;
              }
              Object nextReclaimedObj = getNextLink(reclaimedObj);
              releaseToAllocator(reclaimedObj);
              reclaimedObj = nextReclaimedObj;
          }

          // Recycle the PLC buffer.
          stitchFreePLCSlots(1);

          // Release the memory used up by work lists.
          UnmanagedPageList.ReleaseStandbyPages();

          if (VTable.enableGCProfiling) {
              if (maxCyclicGarbage < reclaimedBytes) {
                  maxCyclicGarbage = reclaimedBytes;
              }
              totalCyclicGarbage += reclaimedBytes;
              cycleCollections++;
          }

#if MEASURE_RCPHASES
          if (!phaseFlag) {
              int elapsed = Environment.TickCount-plcBufferTicks;
              if (ddListPhase) {
                  ddListPLCProcTime += elapsed;
                  ddListPLCProcCount++;
              } else {
                  plcBufferProcTime += elapsed;
                  plcBufferProcCount++;
              }
              plcBufferPhase = false;
          }
#endif // MEASURE_RCPHASES

          if (enableGCTiming) {
              int elapsedTicks = Environment.TickCount-startTicks;
              BaseCollector.RegisterPause(elapsedTicks);
              VTable.enableGCTiming = true;
          }
      }


      [NoInline]
      [ManualRefCounts]
      private static void deallocationListChecker() {
          // Check for nonzero reference counts.
          for (Object block = delayedDeallocationList;
               block != null; block = getNextLink(block)) {
              UIntPtr objAddr = Magic.addressOf(block);
              UIntPtr page = PageTable.Page(objAddr);
              if (!PageTable.IsGcPage(page)) {
                  VTable.DebugPrint("Non-GC memory for freeing!\n");
                  VTable.DebugBreak();
              }
              if ((block.REF_STATE & refCountMask) != 0) {
                  VTable.DebugPrint("Non-zero reference count!\n");
                  VTable.DebugBreak();
              }
          }

          // Check for loops in the delayed deallocation list.
          for (Object block = delayedDeallocationList;
               block != null; block = getNextLink(block)) {
              block.REF_STATE++;
          }
          for (Object block = delayedDeallocationList;
               block != null; block = getNextLink(block)) {
              if ((block.REF_STATE & refCountMask) != 1) {
                  VTable.DebugPrint("Loops in DD list!\n");
                  VTable.DebugBreak();
              }
          }
          for (Object block = delayedDeallocationList;
               block != null; block = getNextLink(block)) {
              block.REF_STATE--;
          }
      }

      [Inline]
      [ManualRefCounts]
      private static bool nonEmptyDDList() {
          return objectBeingDeallocated != null ||
                 delayedDeallocationList != null;
      }

      [NoInline]
      [ManualRefCounts]
      private static void purgeDeallocationList() {
          while (nonEmptyDDList()) {
              deallocateObjects();
          }
      }

      [Inline]
      [ManualRefCounts]
      private static void releaseToAllocator(Object obj) {
#if MEASURE_RCPHASES
          int segFreeTicks = Environment.TickCount;
#endif // MEASURE_RCPHASES

          UIntPtr objStart = Magic.addressOf(obj)-PreHeader.Size;
          UIntPtr page = PageTable.Page(objStart);
          PageType pageType = PageTable.Type(page);
          if (pageType == SegregatedFreeList.SMALL_OBJ_PAGE) {
              uint alignment = obj.vtable.baseAlignment;
              SegregatedFreeList.LocalFreeSmall(objStart, alignment);
          } else {
              VTable.Assert(pageType == SegregatedFreeList.
                            LARGE_OBJ_START,
                            @"pageType == SegregatedFreeList.
                            LARGE_OBJ_START");

              SegregatedFreeList.FreeLarge(obj);
          }

#if MEASURE_RCPHASES
          segFreeTime += Environment.TickCount-segFreeTicks;
#endif // MEASURE_RCPHASES

          if (!GC.HeapSizeConfigurable) {
              releasedObjectCount++;
              if (releasedObjectCount > recycleTrigger) {
                  recycleAllocator();
              }
          }
      }

      [Inline]
      [ManualRefCounts]
      private static void recycleAllocator() {
#if MEASURE_RCPHASES
          int segCommitTicks = Environment.TickCount;
#endif // MEASURE_RCPHASES

          if (!GC.HeapSizeConfigurable) {
              releasedObjectCount = 0;
          }
          SegregatedFreeList.LocalRecycleGlobalPages();
          SegregatedFreeList.CommitFreedData();

#if MEASURE_RCPHASES
          segCommitTime += Environment.TickCount-segCommitTicks;
#endif // MEASURE_RCPHASES
      }


      private class RefCountIncrementer : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              incrementRefCount(objAddr);
          }
      }

      private class RefCountDecrementer : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              decrementRefCount(objAddr);
          }
      }

      private class StackRefCountIncrementer: NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr *loc) {
              UIntPtr addr = *loc;

              UIntPtr page = PageTable.Page(addr);
              if (!PageTable.IsGcPage(page)) {
#if DEBUG
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack,
                                @"pageType == PageType.NonGC ||
                                pageType == PageType.Stack");
#endif // DEBUG

                  return;
              }

              UIntPtr objAddr = SegregatedFreeList.Find(addr);
              if (objAddr != UIntPtr.Zero) {
                  Object obj = Magic.fromAddress(objAddr);
                  nonNullLocalIncrementRefCount(obj);
              }
          }
      }

      private class StackRefCountDecrementer: NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr *loc) {
              UIntPtr addr = *loc;

              UIntPtr page = PageTable.Page(addr);
              if (!PageTable.IsGcPage(page)) {
#if DEBUG
                  PageType pageType = PageTable.Type(page);
                  VTable.Assert(pageType == PageType.NonGC ||
                                pageType == PageType.Stack,
                                @"pageType == PageType.NonGC ||
                                pageType == PageType.Stack");
#endif // DEBUG

                  return;
              }

              UIntPtr objAddr = SegregatedFreeList.Find(addr);
              Object obj = Magic.fromAddress(objAddr);
              if (obj != null) {
                  NonNullDecrementRefCount(obj);
              }
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
              const uint mask = markFlagMask | acyclicFlagMask;
              if ((refState & mask) == 0) {
                  refState |= markFlagMask;
                  this.workList.Write(objAddr);
              }
              obj.REF_STATE = refState;
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
          [DisableNullChecks]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);
              uint refState = obj.REF_STATE;
              const uint mask1 = countingONFlagMask | markFlagMask;
              const uint mask2 = mask1 | acyclicFlagMask;
              if ((refState & mask2) != mask1) {
                  return;
              }

              obj.REF_STATE = refState & ~markFlagMask;
              if (refState > mask1) {
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
              const uint mask1 = markFlagMask | acyclicFlagMask;
              const uint mask2 = countingONFlagMask | 1;
              if ((refState & mask1) == markFlagMask) {
                  // The object hasn't been visited either
                  // by the scanner or the incrementer.
                  refState &= ~markFlagMask;
                  this.workList.Write(objAddr);
              } else if (refState == mask2) {
                  // The object has been visited in the
                  // past, but only by the scanner.
                  this.workList.Write(objAddr);
              }
              obj.REF_STATE = refState;
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
              this.Reclaim(objAddr);
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
              const uint mask = countingONFlagMask | acyclicFlagMask;
              if (refState == mask) {
                  deallocateLazily(obj);
                  obj.REF_STATE = mask | markFlagMask;
              } else if (refState == countingONFlagMask) {
                  Reclaim(objAddr);
              }
          }

          [ManualRefCounts]
          internal void Reclaim(UIntPtr objAddr) {
              Object obj = Magic.fromAddress(objAddr);
              setNextLink(obj, this.ReclaimedObjects);
              obj.REF_STATE = ~countingONFlagMask;
              this.ReclaimedObjects = obj;
              this.workList.Write(objAddr);
          }

          private UIntPtrQueue workList;
      }

      private abstract class ObjectVisitor :
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

      private class BackupInitializer : ObjectVisitor {
          [ManualRefCounts]
          internal override UIntPtr Visit(Object obj) {
              setBackupRefCount(obj, UIntPtr.Zero);

              return ObjectLayout.Sizeof(obj);
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
              UIntPtr count = getBackupRefCount(obj);
              setBackupRefCount(obj, count+1);
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
              UIntPtr count = getBackupRefCount(obj);
              setBackupRefCount(obj, count+1);
              if (obj.GcMark((UIntPtr)1)) {
                  this.workList.Write(objAddr);
              }
          }

          private UIntPtrQueue workList;
      }

      private class BackupReconciler : ObjectVisitor {
          [ManualRefCounts]
          internal override UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr objAddr = Magic.addressOf(obj);
              UIntPtr size = ObjectLayout.ObjectSize(objAddr, vtable);

              uint refState = obj.REF_STATE;
              if ((refState & countingONFlagMask) != 0) {
                  UIntPtr refCount =
                      (UIntPtr)(refState & refCountMask);
                  UIntPtr count = getBackupRefCount(obj);
                  if (count > refCount) {
                      VTable.DebugPrint("count > refCount!\n");
                      VTable.DebugBreak();
                  }
              }

              return size;
          }
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
                  *loc = *loc & ~((UIntPtr)0x3);
              }
          }
      }

      private class LeakAccumulator : ObjectVisitor {
          internal UIntPtr Size;

          internal void Initialize() {
              this.Size = UIntPtr.Zero;
          }

          [ManualRefCounts]
          internal override UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr objAddr = Magic.addressOf(obj);
              UIntPtr size = ObjectLayout.ObjectSize(objAddr, vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & refCountMask);
              if ((refState & countingONFlagMask) != 0 &&
                  refCount > 0) {
                  // This object is considered live by the
                  // reference counting collector.
                  UIntPtr count = getBackupRefCount(obj);
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
              UIntPtr objAddr = Magic.addressOf(obj);
              UIntPtr size = ObjectLayout.ObjectSize(objAddr, vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & refCountMask);
              if ((refState & countingONFlagMask) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefCount(obj);
                  if (count == 0) {
                      dfs.Visit(&objAddr);
                  }
              }

              return size;
          }
      }

      private class DFS : NonNullReferenceVisitor {
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
                  setDfsDiscoveryTime(obj, this.time);
              }
          }

          private UIntPtr time;
      }

      private class LeakedCycleClosure : ObjectVisitor {
          [ManualRefCounts]
          internal override UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr objAddr = Magic.addressOf(obj);
              UIntPtr size = ObjectLayout.ObjectSize(objAddr, vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & refCountMask);
              if ((refState & countingONFlagMask) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefCount(obj);
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

      private class ResetTraversal : ObjectVisitor {
          [ManualRefCounts]
          internal override UIntPtr Visit(Object obj) {
              obj.GcMark(UIntPtr.Zero);
              VTable vtable = obj.vtable;
              UIntPtr objAddr = Magic.addressOf(obj);
              UIntPtr size = ObjectLayout.ObjectSize(objAddr, vtable);

              return size;
          }
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
          internal override UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr objAddr = Magic.addressOf(obj);
              UIntPtr size = ObjectLayout.ObjectSize(objAddr, vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & refCountMask);
              if ((refState & countingONFlagMask) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefCount(obj);
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
          internal override UIntPtr Visit(Object obj) {
              VTable vtable = obj.vtable;
              UIntPtr objAddr = Magic.addressOf(obj);
              UIntPtr size = ObjectLayout.ObjectSize(objAddr, vtable);

              uint refState = obj.REF_STATE;
              UIntPtr refCount = (UIntPtr)(refState & refCountMask);
              if ((refState & countingONFlagMask) != 0 &&
                  refCount > 0) {
                  UIntPtr count = getBackupRefCount(obj);
                  if (count == 0 && obj.GcMark() == UIntPtr.Zero) {
                      this.Total++;
                  }
              }

              return size;
          }
      }
  }
}
