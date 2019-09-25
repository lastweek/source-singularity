//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to the Bartok Depot and propagated to Singularity Depot.   */
/*******************************************************************/


namespace System {

  using Microsoft.Bartok.Runtime;
  using System.Threading;
  using System.Runtime.CompilerServices;
  using System.GCs;
#if SINGULARITY
  using Microsoft.Singularity;
#endif

  /// <summary>
  /// Finalizers are allocated for allocated objects that are finalizable.
  ///
  /// BUGBUG: During a garbage collection it should be possible to coalesce
  /// several FinalizerTable entries into a single entry. In order to
  /// facilitate this all indexes are currently allocated with reference to
  /// the first table. It should also be possible to compact the tables.
  /// </summary>
  [CCtorIsRunDuringStartup]
  [RequiredByBartok]
  internal struct Finalizer
  {
      // Objects are stored as their UIntPtr, asserted to have the low bit
      // clear.  Links in the free list are stored as the (index<<1 | 1).
      private static bool IsLink(int index)
      {
          return ((index & 1) != 0);
      }

      private static int LinkToIndex(int link)
      {
          VTable.Assert(IsLink(link));
          return (link >> 1);
      }

      private static int IndexToLink(int index)
      {
          return (index << 1) | 1;
      }

      /// <summary>
      /// Allocate a Finalizer entry for this object.
      /// </summary>
      [RequiredByBartok]
      internal static void RegisterCandidate(Object obj)
      {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          UIntPtr objPtr = Magic.addressOf(obj);
          UIntPtr page = PageTable.Page(objPtr);
          if (!PageTable.IsGcPage(page)) {
              return;
          }

          // It's tempting to do all manipulations of the CandidateTable with Interlocked
          // operations, but it would leave us open to the ABA problem.  For example,
          //
          //    candidateFreeList points to slot 5, which points to slot 7, and then 9.
          //    We start our CompareExchange loop based on these facts.
          //    Another thread intervenes.  It:
          //          Allocates slot 5 from the free list.
          //          Allocates slot 7 from the free list, so 9 is now at the top.
          //          It calls SuppressCandidate on #5, putting it back on the list,
          //                pointing at 9.
          //    Our thread performs the CompareExchange, removing 5 from the list &
          //          establishing 7 as the head.
          //
          // In order to avoid these (admittedly unlikely) corruptions, just use a
          // SpinLock to serialize all modifications of the CandidateTable.  But to
          // keep the SpinLock as a leaf lock and avoid deadlocks, ensure that we
          // never allocate or do anything else significant while holding the lock.

#if SINGULARITY
          bool disabled = Processor.DisableLocalPreemption();
#endif
          spinLock.Acquire();
          bool lockHeld = true;
          try {
restart:
              // Set index to point into the table at a free spot.
              int index = 0;
              UIntPtr[] table = null;

              // Grab from the free list.  Note that our free list can never be empty.
              // That's because it points either down a linked chain of previously allocated
              // and since free'd entries, or it points out past the high water mark.  We
              // may need to allocate memory to back that index, but the free list always
              // contains at least a virtual index.  And the slot that points past the
              // high water mark is always the last slot to be consumed from the free
              // list, so we grow only as a last resort.
              int logicalIndex = index = LinkToIndex(freeCandidateLink);

              // Relate that global index to a table and a local index.
              for (int i=0; i<CandidateTable.Length; i++) {
                  table = CandidateTable[i];
                  if (table == null) {
                      // Must be the first index into a new table.  We're going to
                      // create the new table, but we don't want to hold the spinLock
                      // during the create.  (We want the spinLock to be a leaf lock
                      // that cannot interact with any GC locks to cause deadlock).
                      VTable.Assert(index == 0);
                      lockHeld = false;
                      spinLock.Release();
#if SINGULARITY
                      Processor.RestoreLocalPreemption(disabled);
#endif
                      table = new UIntPtr[CandidateTable[i-1].Length*2];
#if SINGULARITY
                      disabled = Processor.DisableLocalPreemption();
#endif
                      spinLock.Acquire();
                      lockHeld = true;

                      // There is a race here.  If we lose the race, someone else will
                      // have extended the table.  If so, we use their official table and
                      // let the GC collect our extra one.  No need for interlocked
                      // operations since we are back inside the spinLock.
                      if (CandidateTable[i] == null) {
                          CandidateTable[i] = table;
                      }
                      // Regardless, the world has changed.
                      goto restart;
                  }

                  // Are we extending or are we chasing previously allocated empty slots?
                  if (index < table.Length) {
                      if (logicalIndex >= lastCandidateIndex) {
                          // we are extending past the high water mark.  Grow the free list
                          // ahead of us by 1 slot.
                          VTable.Assert(logicalIndex == lastCandidateIndex);
                          lastCandidateIndex = logicalIndex+1;
                          freeCandidateLink = IndexToLink(lastCandidateIndex);
                      } else {
                          // We are consuming the free list
                          freeCandidateLink = (int) table[index];
                          VTable.Assert(IsLink(freeCandidateLink));
                      }
                      break;
                  }
                  index -= table.Length;        // on to the next table
              }

              VTable.Assert(table != null, "Candidate Algorithmic inconsistency");

              // We have found the table!
              table[index] = Magic.addressOf(obj);

              // The following looks like a 64-bit porting issue (32-bit truncation).
              // But actually I'm just ensuring that object pointers have the low bit
              // cleared.
              VTable.Assert(!IsLink((int) objPtr));
          }
          finally {
              if (lockHeld) {
                  spinLock.Release();
#if SINGULARITY
                  Processor.RestoreLocalPreemption(disabled);
#endif
              }
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// Loop through the candidate structure and zero a reference to
      /// this object.
      /// </summary>
      internal static void SuppressCandidate(Object obj)
      {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          // It's tempting to just hold the spinLock after we find this object and
          // link it into the freeList.  However, SuppressFinalize and ReRegisterForFinalize
          // could be called on multiple threads for the same object simultaneously.  So
          // we really need a lock around the whole thing.
          int logicalIndex = 0;
#if SINGULARITY
          bool disabled = Processor.DisableLocalPreemption();
#endif
          spinLock.Acquire();
          try {
              UIntPtr objPtr = Magic.addressOf(obj);
              for (int i=0; i < CandidateTable.Length; i++) {
                  if (CandidateTable[i] != null) {
                      for (int j=0; j < CandidateTable[i].Length; j++, logicalIndex++) {
                          if (CandidateTable[i][j] == objPtr) {
                              CandidateTable[i][j] = (UIntPtr) freeCandidateLink;
                              freeCandidateLink = IndexToLink(logicalIndex);
                              return;
                          }
                      }
                  }
              }
          }
          finally {
              spinLock.Release();
#if SINGULARITY
              Processor.RestoreLocalPreemption(disabled);
#endif
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// Moves all candidates to the run queue.
      /// </summary>
      internal static void Shutdown()
      {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          if (running) {
              WaitForPending();
              running = false;

              // Wake up the finalizer thread, so that it will exit
              WorkExistsForFinalizerThread.Set();

              finalizerThread.Join();
          }

          // It looks like this stage of shutdown occurs when the app is single-threaded.
          // So we don't need the spinLock to protect against races if the app calls
          // SuppressFinalize or ReRegisterForFinalize on another thread.
          for (int i=0; i < CandidateTable.Length; i++) {
              if (CandidateTable[i] != null) {
                  for (int j=0; j < CandidateTable[i].Length; j++) {
                      UIntPtr candidate = CandidateTable[i][j];
                      if (candidate == UIntPtr.Zero) {
                          // The high water mark of the table.
                          return;
                      }
                      if (!IsLink((int) candidate)) {
                          try {
                              Object obj = Magic.fromAddress(candidate);
                              Magic.callFinalizer(obj);
                          } catch {
                              // Throw it away!
                          }
                      }
                  }
              }
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// Wait until the finalization queue has been emptied.
      /// </summary>
      internal static void WaitForPending() {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          if (Thread.CurrentThread == Finalizer.finalizerThread) {
              return;
          }

          WaitForPendingShouldReturn.WaitOne();

#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// BUGBUG: TODO
      /// </summary>
      internal static void CompactTables() {
      }

      [PreInitRefCounts]
      static unsafe Finalizer() {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          // There is a security issue here.  On 64-bit systems, a malicious SIP
          // could theoretically create more than 2 billion finalizable objects.
          // At that point, the use of 'int' in this file is unsafe, and could
          // allow multiple objects to share the same index.  However, it looks
          // like the candidate table, as allocated below, will support less than
          // 1/2 billion objects.  So we should be okay.
          CandidateTable = (UIntPtr[][])
              GCs.BootstrapMemory.Allocate(typeof(UIntPtr[][]), 24);

          CandidateTableShadow = (UIntPtr[][])
              GCs.BootstrapMemory.Allocate(typeof(UIntPtr[][]), 24);

          RunFinalizerTable = (UIntPtr[][])
              GCs.BootstrapMemory.Allocate(typeof(UIntPtr[][]), 24);

          RunFinalizerTableShadow = (UIntPtr[][])
              GCs.BootstrapMemory.Allocate(typeof(UIntPtr[][]), 24);

          CandidateTable[0] = (UIntPtr[])
              GCs.BootstrapMemory.Allocate(typeof(UIntPtr[]), 10);

          RunFinalizerTable[0] = (UIntPtr[])
              GCs.BootstrapMemory.Allocate(typeof(UIntPtr[]), 10);

          RunFinalizerTableShadow[0] = (UIntPtr[])
              GCs.BootstrapMemory.Allocate(typeof(UIntPtr[]), 10);

          lastCandidateIndex = 0;
          freeCandidateLink = IndexToLink(lastCandidateIndex);
#endif // REFERENCE_COUNTING_GC
      }


      /// <summary>
      /// Start the finalization thread.
      /// </summary>
      internal static void StartFinalizerThread() {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          if (GC.gcType == Microsoft.Bartok.Runtime.GCType.NullCollector) {
              return;
          }

// HACK: Threading issues are preventing use of a Finalizer thread.
//       Disabling for ARM so the GC can be used without it.
#if !OS_WINCE && !ISA_ARM
          WorkExistsForFinalizerThread = new AutoResetEvent(false);
          WaitForPendingShouldReturn = new ManualResetEvent(true);

#if SINGULARITY_KERNEL
          spinLock = new SpinLock(SpinLock.Types.Finalizer);
          finalizerThread = Thread.CreateThread(null,
                                                new ThreadStart(ThreadLoop));
          VTable.Assert(finalizerThread != null);
          running = true;
          finalizerThread.Start();
#elif SINGULARITY_PROCESS
          finalizerThread = new Thread(new ThreadStart(ThreadLoop));
          finalizerThread.SetIgnoredByJoinAll();
          running = true;
          finalizerThread.Start();
#else // !SINGULARITY
          finalizerThread = new Thread(new ThreadStart(ThreadLoop));
          running = true;
          finalizerThread.Start();
#endif // !SINGULARITY
#endif // REFERENCE_COUNTING_GC
#endif // !OS_WINCE
      }

      /// <summary>
      /// The thread loops doing this work forever.
      /// </summary>
      private static void ThreadLoop() {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          while(running) {
              if (WaitingToRun == 0) {
                  WaitForPendingShouldReturn.Set();
                  WorkExistsForFinalizerThread.WaitOne();
                  continue;
              }

              // Get some work
              Object current = GetObjectFromRun();
              VTable.Assert(current != null,
                            "No finalizer found, but WaitingToRun != 0");
              try {
                  Magic.callFinalizer(current);
              } catch {
                  // throw it away!
              }
              Interlocked.Decrement(ref WaitingToRun);
          }
          WaitForPendingShouldReturn.Set();

          // now that the finalizer thread has shutdown, we need to prevent
          // a GC from occuring
          Interlocked.Increment(ref GC.allocationGCInhibitCount);
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// This method must be called to prepare the Finalizer data
      /// structures for a collection.
      /// </summary>
      internal unsafe static void PrepareCollectFinalizers() {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          CompactTables();
          madeRunnable = false;

          for (int i=0; i < CandidateTable.Length; i++) {
              CandidateTableShadow[i] = CandidateTable[i];
          }
          for (int i=0; i < RunFinalizerTable.Length; i++) {
              RunFinalizerTableShadow[i] = RunFinalizerTable[i];
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// Finish up after a collection.
      /// </summary>
      internal static void ReleaseCollectFinalizers() {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          if (madeRunnable) {
              // Review: For now we will assert against a GC running after the
              // finalization thread has shut down. However, if this assert
              // fires and the situation is somewhat reasonable, then we should
              // allow a GC to occur.
              VTable.Assert(running,
                  "Attempt to request finalizer while finalization thread is not running.");
              WaitForPendingShouldReturn.Reset();
              WorkExistsForFinalizerThread.Set();
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// Ensure that any references from the Bootstrap space into the
      /// managed heap are traced during a collection avoiding dangling
      /// pointers.
      /// </summary>
      internal unsafe static
      void VisitBootstrapData(DirectReferenceVisitor visitor)
      {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          VisitAllRunFinalizer(visitor, true, false);

          // Trace other GC data. Being careful to NOT trace the Shadow
          visitor.VisitReferenceFields(CandidateTable);
          visitor.VisitReferenceFields(RunFinalizerTable);
          visitor.VisitReferenceFields(RunFinalizerTable[0]);
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// This method visits all the objects in the RunFinalizer structures.
      /// </summary>
      private unsafe static
      void VisitAllRunFinalizer(DirectReferenceVisitor visitor,
                                bool copyFirst, bool markedOnly)
      {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          // Visit all RunFinalizer objects.
          for (int i=0; i < RunFinalizerTableShadow.Length; i++) {
              UIntPtr[] table = copyFirst
                  ? RunFinalizerTable[i]
                  : RunFinalizerTableShadow[i];

              if (table != null) {
                  for (int j=0; j < table.Length; j++) {
                      fixed (UIntPtr *loc = &table[j]) {
                          if (*loc != UIntPtr.Zero) {
                              if (markedOnly) {
                                  if ((*loc & 1) == 1) {
                                      *loc = *loc & (~(UIntPtr)1);
                                  } else {
                                      continue;
                                  }
                              }
                              visitor.Visit(loc);
                          }
                      }
                  }
              }
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// Find all candidates that have become unreachable.
      /// </summary>
      internal unsafe static
      void ResurrectCandidates(DirectReferenceVisitor forwardVisitor,
                               DirectReferenceVisitor resurrectVisitor,
                               bool copyFirst)
      {
#if !(REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          UIntPtr[] runTable = null;
          int runTableIndex = 0;
          int runIndex = 0;

          // For the concurrent collector, ResurrectCandidates could happen
          // while the application threads are calling SuppressFinalize and
          // ReRegisterForFinalize.  So we need to use the spinLock to prevent
          // races.  But we do not want to hold the spinLock while allocating
          // (i.e. when we grow the RunFinalizerTable[Shadow]) because our
          // spinLock is a leaf lock.  We don't want to worry about deadlocks
          // involving the spinLock and any locking that occurs as part of a
          // GC provoked by an allocation attempt.
#if SINGULARITY
          bool disabled = Processor.DisableLocalPreemption();
#endif
          spinLock.Acquire();
          bool lockHeld = true;
          try {
              int logicalIndex = 0;
              for (int i=0; i < CandidateTableShadow.Length; i++) {
                  UIntPtr[] table = copyFirst
                      ? CandidateTable[i]
                      : CandidateTableShadow[i];

                  if (table == null) {
                      VTable.Assert(logicalIndex == lastCandidateIndex);
                      break;
                  }
                  for (int j=0; j < table.Length; j++, logicalIndex++) {
                      if (table[j] == UIntPtr.Zero) {
                          VTable.Assert(logicalIndex == lastCandidateIndex);
                          break;
                      }
                      fixed (UIntPtr *loc = &table[j]) {
                          if (!IsLink((int) *loc)) {
                              UIntPtr oldVal = *loc;
                              forwardVisitor.Visit(loc);
                              if (*loc == UIntPtr.Zero) {
                                  // Put this slot onto the CandidateTable's free list
                                  *loc = (UIntPtr) freeCandidateLink;
                                  freeCandidateLink = IndexToLink(logicalIndex);

                                  // marching forward through the RunFinalizer[Shadow] table, find an
                                  // empty slot to install this object.  Maintain the cursor across
                                  // objects, so we can efficiently transfer an entire batch.

                                  for (; runTableIndex < RunFinalizerTableShadow.Length; runTableIndex++) {
                                      runTable = copyFirst
                                          ? RunFinalizerTable[runTableIndex]
                                          : RunFinalizerTableShadow[runTableIndex];

                                      if (runTable == null) {
                                          // Create a new table
                                          int length = RunFinalizerTableShadow[runTableIndex-1].Length*2;

                                          lockHeld = false;
                                          spinLock.Release();
#if SINGULARITY
                                          Processor.RestoreLocalPreemption(disabled);
#endif
                                          UIntPtr[] newTable = new UIntPtr[length];
#if SINGULARITY
                                          disabled = Processor.DisableLocalPreemption();
#endif
                                          spinLock.Acquire();
                                          lockHeld = true;

                                          // There is no race with the RunFinalizerTable[Shadow].
                                          // The spinLock serializes access to the CandidateTable[Shadow].
                                          runTable = newTable;
                                          RunFinalizerTable[runTableIndex] = newTable;
                                          RunFinalizerTableShadow[runTableIndex] = newTable;
                                          UIntPtr tableAddr = Magic.addressOf(newTable);
                                          resurrectVisitor.Visit(&tableAddr);
                                          resurrectVisitor.VisitReferenceFields(RunFinalizerTable[runTableIndex]);
                                          resurrectVisitor.VisitReferenceFields(RunFinalizerTableShadow[runTableIndex]);
                                      }

                                      for (; runIndex < runTable.Length; runIndex++) {
                                          if (runTable[runIndex] == UIntPtr.Zero) {
                                              goto outer;
                                          }
                                      }
                                      runIndex -= runTable.Length;
                                      VTable.Assert(runIndex == 0);     // ready for next sub-table
                                  }
outer:
                                  // We found an empty slot in the RunFinalizerTable[Shadow],
                                  // where we can put our ready Candidate.  It's also possible
                                  // to reach this label by falling through after exhausting the
                                  // entire table.  This will result in an exception when we
                                  // attempt to over-index the array.  It's not clear what more
                                  // protections are required... the process has exceeded an
                                  // unlikely and hard-wired capacity limit.
                                  Interlocked.Increment(ref WaitingToRun);
                                  madeRunnable = true;

                                  if (copyFirst) {
                                      RunFinalizerTable[runTableIndex][runIndex]
                                          = oldVal | new UIntPtr(1);
                                  } else {
                                      RunFinalizerTableShadow[runTableIndex][runIndex]
                                          = oldVal | new UIntPtr(1);
                                  }
                              }
                          }
                      }
                  }
              }
          }
          finally {
              if (lockHeld) {
                  spinLock.Release();
#if SINGULARITY
                  Processor.RestoreLocalPreemption(disabled);
#endif
              }
          }

          if (madeRunnable) {
              // Resurrect objects!
              VisitAllRunFinalizer(resurrectVisitor, copyFirst, true);
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// Find and remove an object from the to be run list.  Remembers where
      /// the last object was found as a starting point for finding the next
      /// object.
      /// </summary>
      internal static Object GetObjectFromRun() {
#if (REFERENCE_COUNTING_GC || DEFERRED_REFERENCE_COUNTING_GC)
          return null;
#else
          bool first = true;
          int entryStart = Finalizer.LastEntryRun;

          for (int i = Finalizer.LastTableRun; ; i++) {
              if (i == RunFinalizerTableShadow.Length) {
                  i = 0;
              }

              UIntPtr[] table = RunFinalizerTable[i];

              if (table == null) {
                  i = 0;
                  table = RunFinalizerTable[0];
                  VTable.Assert(table != null, "lost RunFinalizerTable[0]");
              }

              for (int j = entryStart; j < table.Length; j++) {
                  if (table[j] != UIntPtr.Zero) {
                      Object obj = Magic.fromAddress(table[j] & ~(UIntPtr)1);
                      table[j] = UIntPtr.Zero;
                      Finalizer.LastTableRun = i;
                      Finalizer.LastEntryRun = j;
                      return obj;
                  }
                  if ((i == Finalizer.LastTableRun)
                      && (j == Finalizer.LastEntryRun)) {
                      if (first) {
                          // Triggers the very first time through the loops.
                          entryStart = 0;
                          first = false;
                      } else {
                          // Triggers after going around all of the tables.
                          return null;
                      }
                  }
              }
          }
#endif // REFERENCE_COUNTING_GC
      }

      /// <summary>
      /// The thread that runs finalizers.
      /// </summary>
      private static Thread finalizerThread;

      /// <summary>
      /// Did the current collection make any finalizers runnable?
      /// </summary>
      private static bool madeRunnable;

      /// <summary>
      /// Is the finalization thread running?
      /// </summary>
      private static bool running;

      /// <summary>
      /// The table of Finalization Candidates.
      /// </summary>
      private static UIntPtr[][] CandidateTable;

      /// <summary>
      /// A shadow of the candidates table (hidden from GC).
      /// </summary>
      private static UIntPtr[][] CandidateTableShadow;

      /// <summary>
      /// The table of objects to have finalizers run Candidates.
      /// </summary>
      private static UIntPtr[][] RunFinalizerTable;

      /// <summary>
      /// Controls sleeping on the finalizer thread.  The GC signals the
      /// finalizer thread when there is work to do.  The finalizer thread
      /// sleeps when there is no work remaining.  The use of an event prevents
      /// the GC from being blocked.
      /// </summary>
      private static AutoResetEvent WorkExistsForFinalizerThread;

      /// <summary>
      /// Controls sleeping in calls to WaitForPendingFinalizers.  The
      /// finalizer thread signals when work is complete.  The GC resets the
      /// signal when there is more work.  The use of an event should prevent
      /// deadlocks.
      /// </summary>
      private static ManualResetEvent WaitForPendingShouldReturn;

      /// <summary>
      /// A shadow of the run finalizer table (hidden from GC).
      /// </summary>
      private static UIntPtr[][] RunFinalizerTableShadow;

      /// <summary>
      /// This is one more than the highest index in use.
      /// </summary>
      private static int lastCandidateIndex;

      /// <summary>
      /// This is a link into the free list of entries in the CandidateTable.
      /// </summary>
      private static int freeCandidateLink;

      /// <summary>
      /// SpinLock to serialize modifications to the CandidateTable.
      /// </summary>
      private static SpinLock spinLock;

      /// <summary>
      /// This is the index of the table from which the last finalizer was run.
      /// Used as an optimization in finding the next finalizer to run.
      /// </summary>
      private static int LastTableRun;

      /// <summary>
      /// This is the index of the finalizer (in LastTableRun) that was last
      /// run.  Used as an optimization in finding the next finalizer to run.
      /// </summary>
      private static int LastEntryRun;

      /// <summary>
      /// The number of finalizers waiting to run
      /// </summary>
      private static int WaitingToRun;

  }
}
