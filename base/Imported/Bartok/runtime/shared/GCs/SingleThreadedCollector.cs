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
  using System.Runtime.CompilerServices;

  [NoCCtor]
  internal abstract class SingleThreadedCollector :
      StopTheWorldCollector {
      [NoInline]
      [ManualRefCounts]
      internal override void CollectStopped(int currentThreadIndex,
                                            int generation) {
      }

      internal override bool IsOnTheFlyCollector {
          get {
              return false;
          }
      }

      internal override void CheckForNeededGCWork(Thread currentThread) {
      }

      internal override void NewThreadNotification(Thread newThread,
                                                   bool initial) {
          base.NewThreadNotification(newThread, initial);
          SegregatedFreeList.NewThreadNotification(newThread, initial);
      }

      internal override void DeadThreadNotification(Thread deadThread) {
          MultiUseWord.CollectFromThread(deadThread);
          SegregatedFreeList.DeadThreadNotification(deadThread);
          base.DeadThreadNotification(deadThread);
      }

      // The sole purpose of this override is to avoid doing the work
      // specificed in StopTheWorldCollector.ThreadDormantGCNotification.
      internal override void ThreadDormantGCNotification(int threadIndex) {
      }

      // The sole purpose of this override is to avoid doing the work
      // specificed in StopTheWorldCollector.StopTheWorld.
      internal override void StopTheWorld() {
      }

      // The sole purpose of this override is to avoid doing the work
      // specificed in StopTheWorldCollector.ResumeTheWorld.
      internal override void ResumeTheWorld() {
      }
  }
}


