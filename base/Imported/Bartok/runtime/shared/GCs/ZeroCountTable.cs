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

  using Microsoft.Bartok.Runtime;
  using System.Threading;
  using System.Runtime.InteropServices;
  using System.Runtime.CompilerServices;

  /* This class implements the ZeroCountTable for DeferredReferenceCounting
   * Collector. The ZCT is an array of 10000 (Consider dynamic sizing later)
   * uint entries. Initially, we link all entries together as a free list
   * using their array index. When object's RC goes to Zero, we take an
   * entry from free list, and put the object's address in it. In that
   * object's refState, the first bit(markFlagMask) is set to indicate
   * that it is in ZCT. When an object's RC becomes larger than 1, it
   * is removed from ZCT, its corresponding entry is cleared and put at the
   * front of the freelist. The freelist is a LIFO one.
   *
   * - table[0] is never used, so that 0 can be used for check, instead of
   *   using -1
   * If ZCT running out of entries, we trigger GC.
   */
  internal unsafe class ZeroCountTable {
      // Note: 1. in this class, every method should be ManualRefCounted
      //       2. all methods/fields are static, no need to allocate in
      //          BootstrapMemory. But the space for ZCT is dynamically
      //          allocated in a special pool
      //       3. As the pool is marked as NonGC, pointers will not be traced,
      //          and the pool will not be scanned, therefore keep RC untouched

      // Internal variables
      private static uint freeHead;
      private static UIntPtr[] zeroCountTable;
      private static uint maxEntries;
      private static ZCTGarbagePicker zctGarbagePicker;

      private static UIntPtr tableSize;

      [PreInitRefCounts]
      public static unsafe void Initialize() {
          maxEntries = 1 << 16;
          VTable UIntPtrArrayVtable =
              ((RuntimeType)typeof(UIntPtr[])).classVtable;
          tableSize =
              ObjectLayout.ArraySize(UIntPtrArrayVtable, maxEntries);

          // Allocate a pool for ZCT
          BumpAllocator entryPool = new BumpAllocator(PageType.NonGC);
          UIntPtr memStart = MemoryManager.AllocateMemory(tableSize);
          entryPool.SetZeroedRange(memStart, tableSize);
          PageManager.SetStaticDataPages(memStart, tableSize);

          // Initialize ZCT
          zeroCountTable = (UIntPtr[])
              DeferredReferenceCountingCollector.
              AllocateArray(ref entryPool,
                            UIntPtrArrayVtable,
                            tableSize);
          VTable.Assert(zeroCountTable != null,
                        @"zeroCountTable != null");

          *(uint*)(Magic.addressOf(zeroCountTable)+PostHeader.Size) =
              maxEntries;
          VTable.Assert(zeroCountTable.Length == maxEntries,
                        @"zeroCountTable.Length == maxEntries");

          // Build ZCT freeEntries list
          freeHead = 1;
          for (uint i = 1; i < maxEntries-1; i++) {
              zeroCountTable[i]=(UIntPtr)(((i+1) << 2) | 0x01);
          }
          zeroCountTable[maxEntries-1] = (UIntPtr)0x01;

          zctGarbagePicker =
              (ZCTGarbagePicker)BootstrapMemory.
              Allocate(typeof(ZCTGarbagePicker));
      }


      [Inline]
      [ManualRefCounts]
      [DisableBoundsChecks]
      private static uint GetFreeEntry() {
          VTable.Assert(freeHead != 0,
                        @"freeHead != 0");

          uint entry = freeHead;
          freeHead = ((uint)zeroCountTable[entry]) >> 2;

          return entry;
      }

      [Inline]
      [ManualRefCounts]
      [DisableBoundsChecks]
      private static void PutFreeEntry(uint index) {
          zeroCountTable[index] = (UIntPtr)((freeHead << 2) | 0x01);
          freeHead = index;
      }

      [ManualRefCounts]
      [DisableBoundsChecks]
      public static void Add(Object obj) {
          if (freeHead == 0) {
              GC.Collect(); // GC may add object into the PLC buffer.
          }

          uint refState = obj.REF_STATE;
          if ((refState &
              DeferredReferenceCountingCollector.markFlagMask) != 0) {
              return; // GC may already put this object in ZCT
          }

          uint position = GetFreeEntry();
          if ((refState & DeferredReferenceCountingCollector.
              acyclicFlagMask) == 0) {
              uint index =
                  DeferredReferenceCountingCollector.GetPLCIndex(obj);
              if (index != 0) {
                  DeferredReferenceCountingCollector.
                  SetPLCIndex(obj, 0);
                  DeferredReferenceCountingCollector.
                  removeFromPLCBuffer(index);
              }
          }
#if DEBUG
          else {
              uint index =
                  DeferredReferenceCountingCollector.GetPLCIndex(obj);
              VTable.Assert(index == 0,
                            @"index == 0");
          }
#endif // DEBUG

          zeroCountTable[position] = Magic.addressOf(obj);
          obj.REF_STATE = position |
              DeferredReferenceCountingCollector.markFlagMask |
              DeferredReferenceCountingCollector.countingONFlagMask |
              (refState &
              DeferredReferenceCountingCollector.acyclicFlagMask);
      }

      [ManualRefCounts]
      public static void Remove(Object obj) {
          uint refState = obj.REF_STATE;
          uint position = refState &
              DeferredReferenceCountingCollector.refCountMask;
          PutFreeEntry(position);

          obj.REF_STATE =
              DeferredReferenceCountingCollector.countingONFlagMask |
              (refState &
              DeferredReferenceCountingCollector.acyclicFlagMask);
      }

      [ManualRefCounts]
      [DisableBoundsChecks]
      private static unsafe uint PurgeZCT(NonNullReferenceVisitor entryVisitor)
      {
          uint purgedSlots = 0;
          for (uint i = 1; i < maxEntries; i++) {
              UIntPtr content = zeroCountTable[i];
              if (((uint)content & 0x01) != 0) {
                  continue; // Node in free list, skip
              }
              purgedSlots++;
              entryVisitor.Visit(&content);
          }

          return purgedSlots;
      }

      [ManualRefCounts]
      public static bool OutOfEntries() {
          return freeHead == 0;
      }

      [ManualRefCounts]
      public static bool isInZCT(Object obj) {
          return (obj.REF_STATE &
                 DeferredReferenceCountingCollector.
                 markFlagMask) != 0;
      }

      [ManualRefCounts]
      public static void ProcessZeroCountTable() {
          uint purgedSlots;

          do {
              purgedSlots = PurgeZCT(zctGarbagePicker);
          } while (purgedSlots > 0);
      }

      public static long Size {
          get {
              return (long)tableSize;
          }
      }

      private class ZCTGarbagePicker : NonNullReferenceVisitor {
          [ManualRefCounts]
          internal override unsafe void Visit(UIntPtr *loc) {
              UIntPtr objAddr = *loc;
              Object obj = Magic.fromAddress(objAddr);

              // 1. remove from ZCT
              Remove(obj);
              // 2. decrement RC on objects retained via multiuseword
              MultiUseWord muw = MultiUseWord.GetForObject(obj);
              if (muw.IsMonitorOrInflatedTag()) {
                  MultiUseWord.RefCountGCDeadObjHook(muw);
              }
              // 3. add to deallocation list
              DeferredReferenceCountingCollector.deallocateLazily(obj);
          }
      }
  }
}


