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
  internal abstract class RCCollector : Collector {
      [PreInitRefCounts]
      public static void Initialize() {
          SegregatedFreeList.Initialize();
      }


      // This is a compiler intrinsic whose value is controlled by
      // /StageControl.RCCollectorVerifyRefCounts.
      internal static extern bool VerificationMode {
          [Intrinsic]
          [MethodImplAttribute(MethodImplOptions.InternalCall)]
          get;
      }

      // This is a compiler intrinsic whose value is controlled by
      // /StageControl.RCCollectorVerifyLeakedCycles.
      internal static extern bool VerifyLeakedCycles {
          [Intrinsic]
          [MethodImplAttribute(MethodImplOptions.InternalCall)]
          get;
      }

      // This is a compiler intrinsic whose value is controlled by
      // /StageControl.RCCollectorGenerateProfile.
      internal static extern bool ProfilingMode {
          [Intrinsic]
          [MethodImplAttribute(MethodImplOptions.InternalCall)]
          get;
      }

      [MixinConditional("RCGC")]
      [Mixin(typeof(PostHeader))]
      [StructLayout(LayoutKind.Sequential)]
      [RequiredByBartok]
      internal struct PostHeaderRCGC {
          [CompilerInitField(2)]
          internal uint refState;
#if !SINGULARITY
          [RequiredByBartok]
#endif
          internal VTable vtableObject;
      }

      [MixinConditional("RCGC")]
      [Mixin(typeof(Object))]
      internal class RCGCObject : System.Object {
          internal new PostHeaderRCGC postHeader;

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

      [MixinConditional("RCGCVerification")]
      [Mixin(typeof(PreHeader))]
      [RequiredByBartok]
      internal struct PreHeaderRCGCVerification {
          internal UIntPtr backupRefcount;
          internal UIntPtr dfsDiscoveryTime;
          internal UIntPtr dfsFinishingTime;
      }

      [MixinConditional("RCGCVerification")]
      [Mixin(typeof(Object))]
      internal class RCGCVerificationObject : System.Object {
          internal new PreHeaderRCGCVerification preHeader;
      }

      /*
       * Every object maintains a 32-bit "reference state" (RS).
       * The RS consists of a 29-bit reference count, with the
       * remaining bits available for flagging purposes.
       *
       * In a 32-bit architecture, 4GB of memory is addressable.
       * Of this, the upper 2GB is usually reserved for use by
       * the system. So given an object size of at least
       * 12 bytes (sync block index, RS field and the vtable),
       * there can't be more than 2^28 objects. The reference
       * count can be more, due to multiple references from an
       * object to the same target (think of one large array of
       * references), but will be less than 2^29.
       *
       * Of the remaining three bits, one is reserved to ignore
       * reference-counting (RC) operations on objects.
       */

      internal struct RSMasks {
          internal const uint refCount =                0x1fffffff;

          internal const uint countingFlag =            0x80000000;
      }

      // Used only in profiling mode.
      internal struct UpdatePairs {
          public int Increments;
          public int Decrements;

          public static UpdatePairs operator+(UpdatePairs a,
                                              UpdatePairs b) {
              a.Increments += b.Increments;
              a.Decrements += b.Decrements;

              return a;
          }

          public int Total {
              get {
                  return Increments+Decrements;
              }
          }
      } // Increment and decrement counts of one kind of RC update.

      internal struct AcctRecord {
          // General RC update, on a "maybe-null" reference.
          public UpdatePairs MaybeNull;
          // General RC update, but on a non-null reference.
          public UpdatePairs NonNull;

          public UpdatePairs VtableOperand;
          public UpdatePairs RuntimeTypeOperand;

          public String MethodName;

          public static AcctRecord operator+(AcctRecord a,
                                             AcctRecord b) {
              VTable.Assert(Magic.addressOf(a.MethodName) ==
                            Magic.addressOf(b.MethodName),
                            @"Magic.addressOf(a.MethodName) ==
                            Magic.addressOf(b.MethodName)");

              a.MaybeNull += b.MaybeNull;
              a.NonNull += b.NonNull;

              a.VtableOperand += b.VtableOperand;
              a.RuntimeTypeOperand += b.RuntimeTypeOperand;

              return a;
          }

          public int CompareTo(AcctRecord rhs) {
              int lhsTotal = MaybeNull.Total+NonNull.Total;
              int rhsTotal = rhs.MaybeNull.Total+rhs.NonNull.Total;

              return lhsTotal < rhsTotal;
          }

          public void DispCountsHeader() {
              VTable.DebugPrint("GIncs\t\tGDecs");
              VTable.DebugPrint("\t\tNIncs\t\tNDecs");
              VTable.DebugPrint("\t\tV+\t\tV-");
              VTable.DebugPrint("\t\tR+\t\tR-");
          }

          public void DispMethodNameHeader() {
              VTable.DebugPrint("\t\tMethod");
          }

          public void DispCounts() {
              VTable.DebugPrint(MaybeNull.Increments);
              if (MaybeNull.Increments < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(MaybeNull.Decrements);
              if (MaybeNull.Decrements < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(NonNull.Increments);
              if (NonNull.Increments < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
              VTable.DebugPrint(NonNull.Decrements);
              if (NonNull.Decrements < 10000000) {
                  VTable.DebugPrint("\t\t");
              } else {
                  VTable.DebugPrint("\t");
              }
          }

          public void DispMethodName() {
              VTable.DebugPrint(MethodName);
          }

          public void Disp() {
              DispCounts();
              DispMethodName();
          }
      }


      internal override long TotalMemory {
          get {
              UIntPtr pageCount = UIntPtr.Zero;
              for (UIntPtr i = UIntPtr.Zero;
                   i < PageTable.pageTableCount; i++) {
                  if (PageTable.IsMyGcPage(i) &&
                      PageTable.Type(i) !=
                      SegregatedFreeList.INIT_PAGE) {
                      pageCount++;
                  }
              }
              return (long)PageTable.RegionSize(pageCount);
          }
      }


      internal override UIntPtr FindObjectAddr(UIntPtr interiorPtr) {
          return SegregatedFreeList.Find(interiorPtr);
      }

      internal override void VisitObjects
          (ObjectLayout.ObjectVisitor objVisitor,
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
      internal static unsafe bool AccumulateRCUpdates(String methodName,
                                                      int methodIndex,
                                                      uint maxIndex,
                                                      AcctRecord rec) {
          VTable.Assert(RCCollector.ProfilingMode,
                        @"RCCollector.ProfilingMode");

          // Return if the page table hasn't been set up yet.
          if (PageTable.pageTableCount == UIntPtr.Zero) {
              return false;
          }

          if (methods == null) {
              // Allocate up front storage for the accounting records.
              //
              // This is requisitioned directly from the memory
              // manager. Care should be taken to ensure that
              // AccumulateRCUpdates does not indirectly call
              // methods that may have compiler-inserted RC updates.
              VTable vtable =
                  ((RuntimeType)typeof(AcctRecord[])).classVtable;
              UIntPtr size =
                  ObjectLayout.ArraySize(vtable, maxIndex+1);

              BumpAllocator profileData =
                  new BumpAllocator(PageType.NonGC);
              UIntPtr profileDataStart =
                  MemoryManager.AllocateMemory(size);
              profileData.SetRange(profileDataStart, size);
              PageManager.SetStaticDataPages(profileDataStart, size);

              methods =
                  (AcctRecord[])Allocate(ref profileData, vtable, size);
              VTable.Assert(methods != null,
                            @"methods != null");

              *(uint*)(Magic.addressOf(methods)+
                  PostHeader.Size) = maxIndex+1;
          }

          VTable.Assert(methods.Length == maxIndex+1,
                        @"methods.Length == maxIndex+1");

          if (methods[methodIndex].methodName == null) {
              methodNames[methodIndex].methodName = methodName;
          }
          // Not "methodNames[methodIndex].methodName == methodName"
          // because the Equality operator carries compiler-inserted
          // RC updates!
          VTable.Assert(Magic.addressOf(methodNames[methodIndex].
                                        methodName) ==
                        Magic.addressOf(methodName),
                        @"Magic.addressOf(methodNames[methodIndex].
                                          methodName) ==
                        Magic.addressOf(methodName)");

          methods[methodIndex] += rec;

          return true;
      }

      [NoInline]
      [ManualRefCounts]
      internal static void EmitRefCountsProfile() {
          VTable.Assert(RCCollector.ProfilingMode,
                        @"RCCollector.ProfilingMode");

          if (methods == null) { // No RC updates present.
              return;
          }

          // Bubble sort in decreasing order of sums.
          for (int i = 0; i < methods.Length; i++) {
              for (int j = methods.Length-1; j > i; j--) {
                  if (methods[j].CompareTo(methods[j-1])) {
                      // Swap contents.
                      AcctRecord temp = methods[j];
                      methods[j] = methods[j-1];
                      methods[j-1] = temp;
                  }
              }
          }

          VTable.DebugPrint("\n");
          AcctRecord.DispCountsHeader();
          AcctRecord.DispMethodNameHeader();
          VTable.DebugPrint("\n");
          for (int i = 0; i < methods.Length; i++) {
              if (methods[i].increments.Total == 0 &&
                  methods[i].decrements.Total == 0) {
                  continue;
              }
              methods[i].DispCounts();
              methods[i].DispMethodName();
              VTable.DebugPrint("\n");
          }
      }


      private static Object Allocate(ref BumpAllocator profileData,
                                     VTable vtable,
                                     UIntPtr numBytes) {
          UIntPtr resultAddr =
              profileData.AllocateFast(numBytes, vtable.baseAlignment);
          Object result = Magic.fromAddress(resultAddr);
            result.REF_STATE = 1 ;
          result.vtable = vtable;
          return result;
      }

      private static AcctRecord[] methods;
  }
}
