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

  using Microsoft.Bartok.Options;
  using Microsoft.Bartok.Runtime;

  using System.Threading;
  using System.Runtime.CompilerServices;

  internal unsafe class SequentialStoreBuffer : RememberedSet {

      internal static SequentialStoreBuffer instance;

      [AccessedByRuntime("referenced from halforgc.asm")]
      // Should be private, but mixin implementation will warn if visibility
      // of SequentialStoreBufferThread does not match that of Thread, and
      // making that public makes the 'ssb' field internal.
      internal struct ThreadLocal {
          internal UIntPtr overflowValue;
          [AccessedByRuntime("referenced from halforgc.asm")]
          internal UIntPtr *cursor;
          [AccessedByRuntime("referenced from halforgc.asm")]
          internal UIntPtr *limit;
      }

      [MixinConditional("SSB")]
      [MixinConditional("AllThreadMixins")]
      [Mixin(typeof(Thread))]
      [AccessedByRuntime("referenced from brtforgc.asm")]
      // Should be private, but mixin implementation will warn if visibility
      // does not match that of Thread.
      public sealed class SequentialStoreBufferThread : Object {
          [AccessedByRuntime("referenced from brtforgc.asm")]
          internal ThreadLocal ssb;
      }

      private static SequentialStoreBufferThread MixinThread(Thread t) {
          return (SequentialStoreBufferThread) (Object) t;
      }

      internal static void Initialize() {
          Initialize(128, PageTable.PageSize);
      }

      internal static void Initialize(int count, UIntPtr size) {
          writeBufferSize = ((int) size * count) / UIntPtr.Size;
          chunkSize = (int) size;
          UIntPtr memorySize = (UIntPtr) UIntPtr.Size * (uint) writeBufferSize;
          writeBuffer = (UIntPtr *)
              PageManager.AllocateNonheapMemory(null, memorySize);
          VTable.Assert(writeBuffer != null);
          AdjustChunkSize(1);
          SequentialStoreBuffer.instance = (SequentialStoreBuffer)
              BootstrapMemory.Allocate(typeof(SequentialStoreBuffer));
      }

      [Inline]
      internal override void RecordReference(ref Object reference,
                                             Object toObj)
      {
          Record((UIntPtr) Magic.toPointer(ref reference));
      }

      [Inline]
      internal override void RecordReference(UIntPtr* fromAddr,
                                             Object toObj)
      {
          Record((UIntPtr) fromAddr);
      }

      [Inline]
      internal override void RecordClonedObject(Object clonedObject)
      {
          Record(Magic.addressOf(clonedObject) + 1);
      }

      internal override void Clean() {
          for (int i = 0; i < Thread.threadTable.Length; i++) {
              Thread t = Thread.threadTable[i];
              if (t != null) {
                  Clean(t);
              }
          }
      }

      internal override void Clean(Thread thread) {
          UIntPtr wbCursor = (UIntPtr) MixinThread(thread).ssb.cursor;
          UIntPtr wbLimit = (UIntPtr) MixinThread(thread).ssb.limit;
          if (wbCursor < wbLimit) {
              VTable.Assert(wbCursor != UIntPtr.Zero);          
              Util.MemClear(wbCursor, wbLimit - wbCursor);
          }
      }

      [RequiredByBartok]
      [Inline]
      public static void Record(UIntPtr value) {
          Thread currentThread = Thread.CurrentThread;
          if (MixinThread(currentThread).ssb.cursor ==
              MixinThread(currentThread).ssb.limit) {
              RecordSlow(currentThread, value);
          } else {
              *MixinThread(currentThread).ssb.cursor = value;
              MixinThread(currentThread).ssb.cursor++;
          }
      }

      [CalledRarely]
      private static void RecordSlow(Thread currentThread, UIntPtr value) {
          // Try to acquire a new chunk of the store buffer
          while (writeBufferIndex < writeBufferSize) {
              int oldIndex = writeBufferIndex;
              int newIndex = oldIndex + chunkSize;
              if (Interlocked.CompareExchange(ref writeBufferIndex, newIndex,
                                              oldIndex) == oldIndex) {
                  // We secured a new block of write buffer for this thread
                  UIntPtr *cursor = writeBuffer + oldIndex;
                  *cursor = value;
                  cursor++;
                  MixinThread(currentThread).ssb.cursor = cursor;
                  MixinThread(currentThread).ssb.limit =
                      writeBuffer + newIndex;
                  return;
              }
          }
          // We have run out of write barrier space
          if (StopTheWorldGCData.CurrentPhase ==
              StopTheWorldPhase.SingleThreaded) {
              VTable.DebugBreak();
          }
          VTable.Assert(MixinThread(currentThread).ssb.overflowValue ==
                        UIntPtr.Zero);
          MixinThread(currentThread).ssb.overflowValue = value;
          GC.InvokeCollection(currentThread);
          while (MixinThread(currentThread).ssb.overflowValue != UIntPtr.Zero) {
              // Another thread must have taken charge of performing the
              // collection and hadn't yet assigned a GCRequest to the
              // current thread.  Give the other thread a chance to do
              // some work before we try invoking the collector again.
              Thread.Yield();
              GC.InvokeCollection(currentThread);
          }
      }

      internal override void Uniquify() {
          // Sort the write buffer.

          // TODO: Would like sort that is in-place, O(n lg n) worst-case, and
          // O(n) when nearly-sorted.

          bool changed = true;
          for(int max = writeBufferIndex; changed; --max) {
              changed = false;
              for(int i = 1; i < max; ++i) {
                  if(writeBuffer[i-1] > writeBuffer[i]) {
                      changed = true;
                      UIntPtr t = writeBuffer[i-1];
                      writeBuffer[i-1] = writeBuffer[i];
                      writeBuffer[i] = t;
                  }
              }
          }

          // Remove duplicates
          int dest = 0;
          UIntPtr last = UIntPtr.Zero;
          for (int i = 0; i < writeBufferIndex; i++) {
              UIntPtr current = *(writeBuffer + i);
              if (current != last) {
                  VTable.Assert(current > last);
                  *(writeBuffer + dest) = current;
                  dest++;
                  last = current;
                  if ((current & 1) != 0) {
                      // The entire object is marked, skip interior addresses
                      UIntPtr objPtr = current - 1;
                      VTable vtable = Magic.fromAddress(objPtr).vtable;
                      UIntPtr size = ObjectLayout.ObjectSize(objPtr, vtable);
                      VTable.Assert(size > 0);
                      UIntPtr objLimit = objPtr + size;
                      i++;
                      while (i < writeBufferIndex &&
                             *(writeBuffer + i) < objLimit) {
                          i++;
                      }
                      i--;
                  }
              }
          }
          writeBufferIndex = dest;
          // Remove duplicates hiding in the overflow slot in thread objects!
          for (int i = 0; i < Thread.threadTable.Length; i++) {
              Thread t = Thread.threadTable[i];
              if (t != null) {
                  UIntPtr overflowPtr = MixinThread(t).ssb.overflowValue;
                  if (overflowPtr != UIntPtr.Zero) {
                      int left = 0;
                      int right = writeBufferIndex;
                      while (left < right - 1) {
                          int mid = (left + right) / 2;
                          if (*(writeBuffer + mid) <= overflowPtr) {
                              left = mid;
                          } else {
                              right = mid;
                          }
                      }
                      UIntPtr foundPtr = *(writeBuffer + left);
                      if (overflowPtr == foundPtr) {
                          // Found an exact duplicate
                          MixinThread(t).ssb.overflowValue = UIntPtr.Zero;
                          continue;
                      } else if ((foundPtr & 1) != 0) {
                          UIntPtr objAddr = foundPtr - 1;
                          VTable vtable = Magic.fromAddress(objAddr).vtable;
                          UIntPtr size =
                              ObjectLayout.ObjectSize(objAddr, vtable);
                          if (overflowPtr < objAddr + size) {
                              // found a pointer into a checked object
                              MixinThread(t).ssb.overflowValue = UIntPtr.Zero;
                          }
                      } else if ((overflowPtr & 1) != 0) {
                          UIntPtr objAddr = overflowPtr - 1;
                          VTable vtable = Magic.fromAddress(objAddr).vtable;
                          UIntPtr size =
                              ObjectLayout.ObjectSize(objAddr, vtable);
                          UIntPtr objLimit = objAddr + size;
                          int skipCount = 0;
                          int probe = left + 1;
                          while (probe < writeBufferIndex &&
                                 *(writeBuffer + probe) < objLimit) {
                              probe++;
                              skipCount++;
                          }
                          if (skipCount > 0) {
                              while (probe < writeBufferIndex) {
                                  *(writeBuffer + left) =
                                      *(writeBuffer + probe);
                                  left++;
                                  probe++;
                              }
                          }
                      }
                  }
              }
          }
      }

      // REVIEW: This is marked inline because the adaptive collector calls
      // it with two different NonNullReferenceVisitors and we need to avoid
      // the virtual call.  We really want to specialize the method.
      [Inline]
      internal override void Scan(NonNullReferenceVisitor ptrVisitor,
                                  PageType genToCollect)
      {
          for (int i = 0; i < writeBufferIndex; i++) {
              UIntPtr tag = *(writeBuffer + i);
              if (tag != UIntPtr.Zero) {
                  if ((tag & 0x1) == 0) {
                      UIntPtr *fieldLoc = (UIntPtr *) tag;
                      if (*fieldLoc != UIntPtr.Zero) {
                          ptrVisitor.Visit(fieldLoc);
                      }
                  } else {
                      UIntPtr objectPtr = (UIntPtr) (tag - 1);
                      Object obj = Magic.fromAddress(objectPtr);
                      ptrVisitor.VisitReferenceFields(obj);
                  }
              }
          }
          // Handle the overflow in the thread objects
          for (int i = 0; i < Thread.threadTable.Length; i++) {
              Thread t = Thread.threadTable[i];
              if (t != null) {
                  UIntPtr tag = MixinThread(t).ssb.overflowValue;
                  if (tag != UIntPtr.Zero) {
                      if ((tag & 0x1) == 0) {
                          UIntPtr *fieldLoc = (UIntPtr *) tag;
                          if (*fieldLoc != UIntPtr.Zero) {
                              ptrVisitor.Visit(fieldLoc);
                          }
                      } else {
                          UIntPtr objectPtr = (UIntPtr) (tag - 1);
                          Object obj = Magic.fromAddress(objectPtr);
                          ptrVisitor.VisitReferenceFields(obj);
                      }
                  }
              }
          }
      }

      internal override void Reset() {
          int threadCount = 0;
          for (int i = 0; i < Thread.threadTable.Length; i++) {
              Thread t = Thread.threadTable[i];
              if (t != null) {
                  threadCount++;
                  MixinThread(t).ssb.overflowValue = UIntPtr.Zero;
                  MixinThread(t).ssb.cursor = null;
                  MixinThread(t).ssb.limit = null;
              }
          }
          AdjustChunkSize(threadCount);
      }

      private static void AdjustChunkSize(int threadCount) {
          writeBufferIndex = 0;
          // Adjust the size of the write barrier chunks
          int testSize = writeBufferSize;
          while (threadCount > 0) {
              threadCount >>= 1;
              testSize >>= 1;
          }
          if (testSize < chunkSize) {
              VTable.Assert(testSize > 0);
              chunkSize = testSize;
          }
      }

      internal static int chunkSize;
      internal static UIntPtr *writeBuffer;
      internal static int writeBufferIndex;
      internal static int writeBufferSize;

  }

}
