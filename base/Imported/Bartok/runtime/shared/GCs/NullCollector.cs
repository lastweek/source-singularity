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

  using System.Threading;

  internal class NullCollector : BaseCollector {

      internal override void Collect(Thread currentThread, int generation)
      {
          GC.CollectTransition(currentThread, generation);
      }

      internal override void CollectStoppable(int currentThreadIndex,
                                              int generation)
      {
          VTable.NotReached("OutOfMemory: NullCollector: Collect called");
      }

      internal override void NewThreadNotification(Thread newThread,
                                                   bool initial)
      {
          base.NewThreadNotification(newThread, initial);
          BumpAllocator.NewThreadNotification(newThread, PageType.Owner0);
      }

      internal override void CheckForNeededGCWork(Thread currentThread) {
          if (NewBytesSinceGCExceeds((UIntPtr) 1500000000)) {
              VTable.NotReached
                  ("OutOfMemory: NullCollector: Out of original memory quota");
          }
      }

      internal override int CollectionGeneration(int gen) {
          VTable.NotReached
              ("OutOfMemory: NullCollector: CollectionGeneration called");
          return MinGeneration;
      }

      internal override UIntPtr AllocateObjectMemory(UIntPtr numBytes,
                                                     uint alignment,
                                                     Thread currentThread) {
          return BumpAllocator.Allocate(currentThread, numBytes, alignment);
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
              VTable.NotReached
                  ("OutOfMemory: NullCollector: TotalMemory called");
              return 0;
          }
      }

      internal override void EnableHeap() {
      }

      internal override void VerifyHeap(bool beforeCollection) {
      }

      internal override UIntPtr FindObjectAddr(UIntPtr interiorPtr) {
          VTable.NotReached
              ("OutOfMemory: NullCollector: FindObjectAddr called");
          return UIntPtr.Zero;
      }

      internal override void VisitObjects
      (ObjectLayout.ObjectVisitor objectVisitor,
       UIntPtr lowAddr,
       UIntPtr highAddr) {
      }

      internal override bool IsOnTheFlyCollector {
          get {
              return false;
          }
      }
  }
}
