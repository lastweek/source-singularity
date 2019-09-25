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
  internal class ARCSCollector : SingleThreadedRCCollector {
      [PreInitRefCounts]
      public new static void Initialize() {
          SingleThreadedRCCollector.Initialize();

          incrementer =
              (RefCountIncrementer)BootstrapMemory.
              Allocate(typeof(RefCountIncrementer));
          decrementer =
              (RefCountDecrementer)BootstrapMemory.
              Allocate(typeof(RefCountDecrementer));

          instance =
              (ARCSCollector)BootstrapMemory.
              Allocate(typeof(ARCSCollector));
      }

      [NoInline]
      [ManualRefCounts]
      public override void VerifyHeap(bool beforeCollection) {
          preVerifyHeap();

          // Deallocate objects on the delayed deallocation list.
          purgeDeallocationList(decrementer);

          postVerifyHeap(beforeCollection);
      }


      [MixinConditional("ARCSGC")]
      [Mixin(typeof(Object))]
      internal class ARCSGCObject : System.Object {
          internal new TrialDeletion.PreHeader preHeader;
      }


      internal override void EnableHeap() {
      }

      internal override void DestructHeap() {
          if (VTable.enableGCVerify) {
              VerifyHeap(true);
          }
          base.DestructHeap();
          if (VTable.enableGCProfiling) {
              if (RCCollector.ProfilingMode) {
                  EmitRefCountsProfile();
              }
          }
      }

      [NoInline]
      [InlineIntoOnce]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static unsafe void NonNullIncrementRefCount(Object obj) {
          uint refState = BasicIncrementRefCount(obj);

          td.IncrementCycleProcessing(refState, obj);
      }

          // Exclude the object from leaked cycle processing.
          if ((refState & RSMasks.acyclicFlag) != 0) {
#if DEBUG
              PLCLink* pLinkAddr = td.getPLCLink(obj);
              VTable.Assert(pLinkAddr == null,
                            @"pLinkAddr == null");
#endif // DEBUG
          } else {
              PLCLink* pLinkAddr = td.getPLCLink(obj);
              // If the object hasn't already been removed from
              // the PLC ("potentially leaked cycle") list, remove it.
              if (pLinkAddr != null) {
                  // Reset the PLC link pointer in the object.
                  td.setPLCLink(obj, null);
                  td.removeFromPLCList(pLinkAddr);
              }
          }
      }

      [Inline]
      [InlineIntoOnce]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void AcyclicIncrementRefCount(Object obj) {
          if (obj == null) {
              return;
          }

          NonNullAcyclicIncrementRefCount(obj);
      }

      [Inline]
      [InlineIntoOnce]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static void NonNullAcyclicIncrementRefCount(Object obj) {
          uint refState = BasicIncrementRefCount(obj);

          VTable.Assert((refState & RSMasks.acyclicFlag) != 0,
                        @"(refState & RSMasks.acyclicFlag) != 0");
      }

      [Inline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static uint BasicIncrementRefCount(Object obj) {
          VTable.Assert(obj != null &&
                        (obj.REF_STATE & RSMasks.refCount) <
                        RSMasks.refCount,
                        @"obj != null &&
                        (obj.REF_STATE & RSMasks.refCount) <
                        RSMasks.refCount");

          uint refState = obj.REF_STATE;
          if ((refState & countingONFlagMask) == 0) {
              return;
          }
          VTable.Assert(refState != 0,
                        @"refState != 0");

          obj.REF_STATE = refState+1;

          return refState;
      }


      [NoInline]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static unsafe void NonNullDecrementRefCount(Object obj) {
          VTable.Assert(obj != null &&
                        (obj.REF_STATE & RSMasks.refCount) > 0,
                        @"obj != null &&
                        (obj.REF_STATE & RSMasks.refCount) > 0");

          uint refState = obj.REF_STATE;
          if ((refState & RSMasks.refCount) == 1) {
              VTable.Assert((refState & RSMasks.countingFlag) != 0,
                            @"(refState & RSMasks.countingFlag) != 0");

              MultiUseWord muw = MultiUseWord.GetForObject(obj);
              if (muw.IsMonitorOrInflatedTag()) {
                  MultiUseWord.RefCountGCDeadObjHook(muw);
              }

              // Set aside the object for a delayed deallocation.
              deallocateLazily(obj);
          } else if ((refState & RSMasks.countingFlag) == 0) {
              return;
          }

          obj.REF_STATE = refState-1;
      }

      [NoInline]
      [InlineIntoOnce]
      [ManualRefCounts]
      [RequiredByBartok]
      internal static unsafe void DecrementRefCount(Object obj) {
          if (obj == null) {
              return;
          }

          NonNullDecrementRefCount(obj);
      }


      [RequiredByBartok]
      internal static void IncrementReferentRefCounts(UIntPtr objAddr,
                                                      VTable vtable) {
          UpdateReferentRefCounts(objAddr, vtable, incrementer);
      }

      [RequiredByBartok]
      internal static void DecrementReferentRefCounts(UIntPtr objAddr,
                                                      VTable vtable) {
          UpdateReferentRefCounts(objAddr, vtable, decrementer);
      }

      [ManualRefCounts]
      internal static unsafe void IncrementReferentRefCounts
          (UIntPtr objAddr,
           VTable vtable,
           int start,
           int span) {
          UpdateReferentRefCounts(objAddr, vtable, start, span,
                                  incrementer);
      }

      [ManualRefCounts]
      internal static unsafe void DecrementReferentRefCounts
          (UIntPtr objAddr,
           VTable vtable,
           int start,
           int span) {
          UpdateReferentRefCounts(objAddr, vtable, start, span,
                                  decrementer);
      }


      [Inline]
      [ManualRefCounts]
      protected static void deallocateObjects() {
          deallocateObjects(decrementer);
      }

      [NoInline]
      [ManualRefCounts]
      protected static void purgeDeallocationList() {
          deallocateObjects(decrementer);
      }


      [ManualRefCounts]
      private static UIntPtr getDfsFinishingTime(Object obj) {
          return ((RCGCVerificationObject)obj).preHeader.
                 dfsFinishingTime;
      }

      [ManualRefCounts]
      private static void setDfsFinishingTime(Object obj,
                                              UIntPtr time) {
          ((RCGCVerificationObject)obj).preHeader.dfsFinishingTime =
              time;
      }


      private class RefCountIncrementer : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);
              IncrementRefCount(obj);
          }
      }

      private class RefCountDecrementer : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr* loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);
              DecrementRefCount(obj);
          }
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
              setBackupRefcount(obj, UIntPtr.Zero);

              VTable vtable = obj.vtable;
              return ObjectLayout.
                     ObjectSize(Magic.addressOf(obj), vtable);
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

      private class ResetTraversal : ObjectVisitor {
          [ManualRefCounts]
          internal override unsafe UIntPtr Visit(Object obj) {
              obj.GcMark(UIntPtr.Zero);
              VTable vtable = obj.vtable;
              UIntPtr size =
                  ObjectLayout.ObjectSize(Magic.addressOf(obj), vtable);

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
  }
      private static NonNullReferenceVisitor incrementer;
      private static NonNullReferenceVisitor decrementer;

}


