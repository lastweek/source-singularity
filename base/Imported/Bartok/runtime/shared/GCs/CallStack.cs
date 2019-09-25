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

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

    using Microsoft.Bartok.Options;
    using Microsoft.Bartok.Runtime;

#if SINGULARITY_KERNEL
#elif SINGULARITY_PROCESS
    using Microsoft.Singularity.V1.Services;
#endif

    [NoCCtor]
    [AccessedByRuntime("referenced from halexn.cpp")]
    internal unsafe class CallStack
    {

#if SINGULARITY
        // Static fields to be initialized to the addresses of labels
        // surrounding the linked-stack assembly code that we must skip.
        private static UIntPtr LinkStackFunctionsBegin;
        private static UIntPtr LinkStackFunctionsLimit;
        private static UIntPtr LinkStackBegin;
        private static UIntPtr LinkStackLimit;
        private static UIntPtr UnlinkStackBegin;
        private static UIntPtr UnlinkStackLimit;
        private static UIntPtr LinkStackStubsBegin;
        private static UIntPtr LinkStackStubsLimit;
#endif

        internal static void Initialize()
        {
#if SINGULARITY
            // Linked stacks pose a special problem for stack scanning.
            // The stack will contain "stuff" from the assembly code
            // implementations of linked stacks, and the stack walking
            // code needs to simply skip that "stuff".  Since the code
            // is defined in a single .asm file, we use labels around
            // the code to help us identify the PC values that will need
            // special processing.  Initialize the above static fields
            // to hold the addresses of the labels surrounding the code.
            fixed (byte *regionBegin =
                   &Microsoft.Singularity.Memory.Stacks.LinkStackFunctionsBegin) {
                LinkStackFunctionsBegin = (UIntPtr) regionBegin;
            }
            fixed (byte *regionLimit =
                   &Microsoft.Singularity.Memory.Stacks.LinkStackFunctionsLimit) {
                LinkStackFunctionsLimit = (UIntPtr) regionLimit;
            }
            fixed (byte *linkStackBegin =
                   &Microsoft.Singularity.Memory.Stacks.LinkStackBegin) {
                LinkStackBegin = (UIntPtr) linkStackBegin;
            }
            fixed (byte *linkStackLimit =
                   &Microsoft.Singularity.Memory.Stacks.LinkStackLimit) {
                LinkStackLimit = (UIntPtr) linkStackLimit;
            }
            fixed (byte *unlinkStackBegin =
                   &Microsoft.Singularity.Memory.Stacks.UnlinkStackBegin) {
                UnlinkStackBegin = (UIntPtr) unlinkStackBegin;
            }
            fixed (byte *unlinkStackLimit =
                   &Microsoft.Singularity.Memory.Stacks.UnlinkStackLimit) {
                UnlinkStackLimit = (UIntPtr) unlinkStackLimit;
            }
            fixed (byte *linkStackStubsBegin =
                   &Microsoft.Singularity.Memory.Stacks.LinkStackStubsBegin) {
                LinkStackStubsBegin = (UIntPtr) linkStackStubsBegin;
            }
            fixed (byte *linkStackStubsLimit =
                   &Microsoft.Singularity.Memory.Stacks.LinkStackStubsLimit) {
                LinkStackStubsLimit = (UIntPtr)linkStackStubsLimit;
            }
#endif
        }

        [Mixin(typeof(Thread))]
        // Should be private, but mixin implementation will warn if visibility
        // does not match that of Thread.
        public sealed class CallStackThread : Object {
            [AccessedByRuntime("referenced in brtstack.asm")]
            internal UIntPtr asmStackBase; // Limit of thread's stack
            [AccessedByRuntime("referenced in brtstack.asm")]
            internal UIntPtr asmStackLimit;
            [AccessedByRuntime("referenced in brtforgc.asm")]
            internal unsafe TransitionRecord *asmStackMarker;
        }

        private static CallStackThread MixinThread(Thread t) {
            return (CallStackThread) (Object) t;
        }

        internal static UIntPtr StackBase(Thread t) {
            return MixinThread(t).asmStackBase;
        }

        internal static void SetStackBase(Thread t, UIntPtr value) {
            MixinThread(t).asmStackBase = value;
        }

        internal static UIntPtr StackLimit(Thread t) {
            return MixinThread(t).asmStackLimit;
        }

        internal static void SetStackLimit(Thread t, UIntPtr value) {
            MixinThread(t).asmStackLimit = value;
        }

        internal static TransitionRecord* StackMarker(Thread t)
        {
            return MixinThread(t).asmStackMarker;
        }

        [AccessedByRuntime("referenced from halforgc.asm")]
        [RequiredByBartok]
        internal unsafe struct TransitionRecord {
            [AccessedByRuntime("referenced from halforgc.asm")]
            internal TransitionRecord *oldTransitionRecord;
            [AccessedByRuntime("referenced from halforgc.asm")]
            internal UIntPtr callAddr;
            [AccessedByRuntime("referenced from halforgc.asm")]
            internal UIntPtr stackBottom;
            [AccessedByRuntime("referenced from halforgc.asm")]
            internal CalleeSaveRegisters calleeSaveRegisters;
        }

        internal static Thread threadBeingProcessed;

        [RequiredByBartok]
        private static int callSiteTableCount;
        [AccessedByRuntime("referenced from halexn.cpp")]
        private static UIntPtr *codeBaseStartTable;
        [RequiredByBartok]
        private static UIntPtr **returnAddressToCallSiteSetNumbers;
        [RequiredByBartok]
        private static int **callSiteSetCount;

        private static int CallSiteTableNumber(UIntPtr returnAddr)
        {
            UIntPtr address = returnAddr;
            for (int i = 0; i < callSiteTableCount; i++) {
                UIntPtr baseAddress = codeBaseStartTable[i];
                if (address < baseAddress) {
                    continue;
                }
                UIntPtr relativeAddress = address - baseAddress;
                UIntPtr *ptr = returnAddressToCallSiteSetNumbers[i];
                int callSiteCount = *(callSiteSetCount[i]);
                if (relativeAddress >= ptr[0] &&
                    relativeAddress <= ptr[callSiteCount]) {
                    return i;
                }
            }
            return -1;
        }

        private static int CallSiteSetNumber(UIntPtr returnAddr, int index)
        {
            UIntPtr codeBaseAddr = codeBaseStartTable[index];
            UIntPtr relativeAddr = returnAddr - codeBaseAddr;
            UIntPtr *callSiteTable = returnAddressToCallSiteSetNumbers[index];
            int callSiteCount = *(callSiteSetCount[index]);
            int left = 0;
            int right = callSiteCount;
            // Loop invariant:
            //   callSiteTable[left] <= returnAddress < callSiteTable[right]
            while (left < right-1) {
                int mid = (left + right)/2;
                if (callSiteTable[mid] <= relativeAddr) {
                    left = mid;
                } else {
                    right = mid;
                }
            }
            return left;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct FullDescriptor {
            internal UIntPtr mask;
            internal int variableData;
        }

        private const uint ESCAPE32_TAG = 0x0;
        private const uint ESCAPE16_TAG = 0x1;
        private const uint ESCAPE8_TAG  = 0x2;

        // Check whether the specified stack frame contains the
        // transition record: if so then we're done scanning this
        // segment of the stack.  NB: the caller must ensure that the
        // framePointer has been recomputed in a
        // framePointerOmitted-method.
        private static bool FrameContainsTransitionRecord(UIntPtr *framePointer,
                                                          UIntPtr *stackPointer,
                                                          TransitionRecord *stopMarker) {
            bool result = false;
            if ((framePointer >= stopMarker) && (stackPointer < stopMarker)) {
                result = true;
            }
            return result;
        }

        private static
        bool WalkStackFrame(ref UIntPtr *framePointer,
                            ref UIntPtr *stackPointer,
                            ref CalleeSaveLocations calleeSaves,
                            ref UIntPtr returnAddr,
                            NonNullReferenceVisitor threadReferenceVisitor,
                            NonNullReferenceVisitor pinnedReferenceVisitor,
                            CompressedFrameDescriptor smallFrameDescriptor,
                            TransitionRecord *stopMarker,
                            Thread thread)
            // BUGBUG: Remove thread argument when ThreadContext is on stack!
        {
            FrameDescriptor frameDescriptor =
                new FrameDescriptor(smallFrameDescriptor);
            if (frameDescriptor.isFramePointerOmitted) {
                framePointer = stackPointer + frameDescriptor.frameSize;
            }
            if (FrameContainsTransitionRecord(framePointer, stackPointer,
                                              stopMarker)) {
                return true;    // true: done
            }
            switch (frameDescriptor.argumentTag) {
              case FrameDescriptor.ESCAPE32_TAG: {
                  int *table = (int *) frameDescriptor.argumentMaskOrTable;
                  int count = table[0];
                  int pinnedCount = table[1];
                  int *offsets = &table[2];
                  if (threadReferenceVisitor != null) {
                      for (int i = 0; i < count; i++) {
                          UIntPtr *loc = framePointer + offsets[i];
                          if (*loc != UIntPtr.Zero) {
                              // BUGBUG: threadReferenceVisitor.Visit(loc);
                              VisitIfNotContext(thread, threadReferenceVisitor, loc);
                          }
                      }
                  }
                  if (frameDescriptor.hasPinnedVariables &&
                      pinnedReferenceVisitor != null) {
                      offsets = &offsets[count];
                      for (int i = 0; i < pinnedCount; i++) {
                          UIntPtr *loc = framePointer + offsets[i];
                          if (*loc != UIntPtr.Zero) {
                              pinnedReferenceVisitor.Visit(loc);
                          }
                      }
                  }
                  break;
              }
              case FrameDescriptor.ESCAPE16_TAG: {
                  short *table = (short *) frameDescriptor.argumentMaskOrTable;
                  int count = table[0];
                  int pinnedCount = table[1];
                  short *offsets = &table[2];
                  if (threadReferenceVisitor != null) {
                      for (int i = 0; i < count; i++) {
                          UIntPtr *loc = framePointer + offsets[i];
                          if (*loc != UIntPtr.Zero) {
                              // BUGBUG: threadReferenceVisitor.Visit(loc);
                              VisitIfNotContext(thread, threadReferenceVisitor, loc);
                          }
                      }
                  }
                  if (frameDescriptor.hasPinnedVariables &&
                      pinnedReferenceVisitor != null) {
                      offsets = &offsets[count];
                      for (int i = 0; i < pinnedCount; i++) {
                          UIntPtr *loc = framePointer + offsets[i];
                          if (*loc != UIntPtr.Zero) {
                              pinnedReferenceVisitor.Visit(loc);
                          }
                      }
                  }
                  break;
              }
              case FrameDescriptor.ESCAPE8_TAG: {
                  sbyte *table = (sbyte *) frameDescriptor.argumentMaskOrTable;
                  int count = table[0];
                  int pinnedCount = table[1];
                  sbyte *offsets = &table[2];
                  if (threadReferenceVisitor != null) {
                      for (int i = 0; i < count; i++) {
                          UIntPtr *loc = framePointer + offsets[i];
                          if (*loc != UIntPtr.Zero) {
                              // BUGBUG: threadReferenceVisitor.Visit(loc);
                              VisitIfNotContext(thread, threadReferenceVisitor, loc);
                          }
                      }
                  }
                  if (frameDescriptor.hasPinnedVariables &&
                      pinnedReferenceVisitor != null) {
                      offsets = &offsets[count];
                      for (int i = 0; i < pinnedCount; i++) {
                          UIntPtr *loc = framePointer + offsets[i];
                          if (*loc != UIntPtr.Zero) {
                              pinnedReferenceVisitor.Visit(loc);
                          }
                      }
                  }
                  break;
              }
              case FrameDescriptor.COMPRESSED_MASK_TAG: {
                  // Process the arguments
                  int inBetweenSlotsAbove =
                      frameDescriptor.inBetweenSlotsAbove;
                  uint stackArgSize = frameDescriptor.argumentCount;
                  UIntPtr mask = frameDescriptor.argumentMaskOrTable;
                  if (threadReferenceVisitor != null && stackArgSize > 0) {
                      UIntPtr *argumentPointer =
                          framePointer + stackArgSize - 1 + inBetweenSlotsAbove;
                      for (int i = 0; mask != 0 && i < stackArgSize; i++) {
                          if ((mask & 0x1) != 0 &&
                              *argumentPointer != UIntPtr.Zero) {
                              // BUGBUG: threadReferenceVisitor.Visit(p);
                              VisitIfNotContext(thread, threadReferenceVisitor,
                                                argumentPointer);
                          }
                          mask >>= 1;
                          argumentPointer--;
                      }
                  } else {
                      for (int i = 0; mask != 0 && i < stackArgSize; i++) {
                          mask >>= 1;
                      }
                  }
                  // Process the local variables
                  if (threadReferenceVisitor != null) {
                      int transitionRecordSize =
                          frameDescriptor.hasTransitionRecord ?
                          sizeof(TransitionRecord) / sizeof (UIntPtr) :
                          0;
                      int registerCount =
                          CountBits(frameDescriptor.calleeSaveMask);
                      int inBetweenSlotsBelow =
                          frameDescriptor.inBetweenSlotsBelow;
                      UIntPtr *variablePtr =
                          framePointer - inBetweenSlotsBelow - registerCount
                          - transitionRecordSize - 1;  // -1 because FP is pointing in "above" region.
                      while (mask != UIntPtr.Zero) {
                          if ((mask & 0x1) != 0 &&
                              *variablePtr != UIntPtr.Zero) {
                              // BUGBUG: threadReferenceVisitor.Visit(p);
                              VisitIfNotContext(thread, threadReferenceVisitor,
                                                variablePtr);
                          }
                          mask >>= 1;
                          variablePtr--;
                      }
                  }
                  break;
              }
              default: {
                  VTable.NotReached("FrameDescriptor mask switch failed");
                  break;
              }
            }
            if (frameDescriptor.calleeSaveValueMask != 0 &&
                threadReferenceVisitor != null) {
                calleeSaves.ScanLiveRegs(frameDescriptor.calleeSaveValueMask,
                                         threadReferenceVisitor);
            }
    
#if X86 || AMD64 || ISA_IX86 || ISA_IX64
            UIntPtr nextReturnAddr;
            if (frameDescriptor.isFramePointerOmitted) {
                nextReturnAddr = *framePointer;
                stackPointer = framePointer + 1;
            } else {
                nextReturnAddr = *(framePointer + 1);
                stackPointer = framePointer + 2;
            }
#elif ARM || ISA_ARM
            // CompressedFrameDescriptor is the target specific portion.
            // This will be refactored to FrameDescriptor via partial classes.
            UIntPtr nextReturnAddr = CompressedFrameDescriptor.NextCallSite(frameDescriptor.isFramePointerOmitted, framePointer, out stackPointer);
#else
#error Unknown Architecture
#endif

            // In Singularity, the final return address of a thread is zero
            if (nextReturnAddr != UIntPtr.Zero) {
                calleeSaves.PopFrame(framePointer,
                                     frameDescriptor.calleeSaveMask,
                                     frameDescriptor.isFramePointerOmitted,
                                     frameDescriptor.hasTransitionRecord);
            } else {
                calleeSaves.ClearFrame(frameDescriptor.calleeSaveMask,
                                       frameDescriptor.isFramePointerOmitted);
            }
            UIntPtr *calcedfp = (UIntPtr *) calleeSaves.GetFramePointer();
            if (calcedfp != null) {
                framePointer = calcedfp;
            }
            returnAddr = nextReturnAddr;
            return false; // false: not done scanning: proceed to next frame
        }

        private static int CountBits(UIntPtr bitMask) {
            int result = 0;
            while (bitMask != UIntPtr.Zero) {
                if ((bitMask & (UIntPtr) 0x1) != UIntPtr.Zero) {
                    result++;
                }
                bitMask >>= 1;
            }
            return result;
        }

#if SINGULARITY_PROCESS
        // TODO: BUGBUG: Get rid of this when ThreadContext is on stack!
        [Inline]
        private static
        void VisitIfNotContext(Thread thread,
                               NonNullReferenceVisitor threadReferenceVisitor,
                               UIntPtr *p)
        {
            if (*p != (UIntPtr) thread.context &&
                (int *) *p != &thread.context->gcStates) {
                threadReferenceVisitor.Visit(p);
            }
        }
#else
        [Inline]
        private static
        void VisitIfNotContext(Thread thread,
                               NonNullReferenceVisitor threadReferenceVisitor,
                               UIntPtr *p)
        {
            threadReferenceVisitor.Visit(p);
        }
#endif

        [RequiredByBartok]
        private static ushort **callSetSiteNumberToIndex;
        [RequiredByBartok]
        private static CompressedFrameDescriptor **activationDescriptorTable;

        [PreInitRefCounts]
        internal static
        int ScanStacks(NonNullReferenceVisitor VisitThreadReference,
                       NonNullReferenceVisitor VisitPinnedReference)
        {
            int limit = Thread.threadTable.Length;
            int countThreads = 0;
            for (int i = 0; i < limit; i++) {
                Thread t = Thread.threadTable[i];
                if (t != null) {
                    CollectorStatistics.Event(GCEvent.StackScanStart, i);
                    ScanStack(t, VisitThreadReference, VisitPinnedReference);
                    CollectorStatistics.Event(GCEvent.StackScanComplete, i);
                    countThreads++;
                }
            }
            return countThreads;
        }

        [PreInitRefCounts]
        internal static
        uint ScanStack(Thread thread,
                       NonNullReferenceVisitor VisitThreadReference,
                       NonNullReferenceVisitor VisitPinnedReference)
        {
            Trace.Log(Trace.Area.Stack,
                      "Scanning stack for thread {0:x}",
                      __arglist(thread.threadIndex));

            uint numStackFrames = 0;
            threadBeingProcessed = thread;
            CalleeSaveLocations calleeSaves = new CalleeSaveLocations();
#if SINGULARITY_KERNEL
            TransitionRecord *marker = (TransitionRecord *) thread.context.stackMarkers;
#elif SINGULARITY_PROCESS
            TransitionRecord *marker = null;
            if (thread.context != null) {
                marker = (TransitionRecord *) thread.context->stackMarkers;
            }
#else
            TransitionRecord *marker = (TransitionRecord *)
                MixinThread(thread).asmStackMarker;
#endif
            while (marker != null) {
                Trace.Log(Trace.Area.Stack,
                          "Transition record: old={0:x}, callAddr={1:x}, stackBottom={2:x}", __arglist(marker->oldTransitionRecord, marker->callAddr, marker->stackBottom));
                marker->calleeSaveRegisters.DebugTrace();
                TransitionRecord *stopMarker = marker->oldTransitionRecord;
                UIntPtr returnAddr = marker->callAddr;
                UIntPtr *fp = (UIntPtr *)
                    marker->calleeSaveRegisters.GetFramePointer();
                UIntPtr *sp = (UIntPtr *) marker->stackBottom;
                calleeSaves.SetCalleeSaves(&marker->calleeSaveRegisters);
                numStackFrames +=
                    ScanStackSegment(ref calleeSaves, returnAddr, fp, sp,
                                     stopMarker, VisitThreadReference,
                                     VisitPinnedReference, thread);
                marker = marker->oldTransitionRecord;
            }
            threadBeingProcessed = null;
            return numStackFrames;
        }

        [PreInitRefCounts]
        private static
        uint ScanStackSegment(ref CalleeSaveLocations calleeSaves,
                              UIntPtr returnAddr,
                              UIntPtr *fp,
                              UIntPtr *sp,
                              TransitionRecord *stopMarker,
                              NonNullReferenceVisitor VisitThreadReference,
                              NonNullReferenceVisitor VisitPinnedReference,
                              Thread thread)
            // BUGBUG: Remove thread argument when ThreadContext is on stack!
        {
            uint numStackFrames = 0;
            while (true) {
#if SINGULARITY
                if (returnAddr >= LinkStackFunctionsBegin &&
                    returnAddr <= LinkStackFunctionsLimit) {
                    if (returnAddr >= LinkStackBegin &&
                        returnAddr <= LinkStackLimit) {
                        returnAddr = SkipLinkStackFrame(ref fp, ref sp);
                    } else if (returnAddr >= UnlinkStackBegin &&
                               returnAddr <= UnlinkStackLimit) {
                        returnAddr = SkipUnlinkStackFrame(ref fp, ref sp);
                    } else if (returnAddr >= LinkStackStubsBegin &&
                               returnAddr <= LinkStackStubsLimit) {
                        returnAddr = SkipLinkStackStubFrame(ref fp, ref sp);
                    } else {
                        VTable.NotReached("Unexpected link stack function");
                    }
                }
#endif

                // Exit loop if we have reached the of the stack segment
                if (fp >= stopMarker && sp < stopMarker) {
                    break;
                }
                int tableIndex = CallSiteTableNumber(returnAddr);
                if (tableIndex < 0) {
                    break;
                }
                int callSiteSet = CallSiteSetNumber(returnAddr, tableIndex);
                if (callSiteSet < 0) {
                    break;
                }
                ushort *callSiteToIndexTable =
                    callSetSiteNumberToIndex[tableIndex];
                int activationIndex = (int) callSiteToIndexTable[callSiteSet];
                VTable.Assert(activationIndex >= 0);
                CompressedFrameDescriptor *descriptorTable =
                    activationDescriptorTable[tableIndex];
                CompressedFrameDescriptor frameDescriptor =
                    descriptorTable[activationIndex];
                bool done = WalkStackFrame(ref fp, ref sp, ref calleeSaves,
                                           ref returnAddr,
                                           VisitThreadReference,
                                           VisitPinnedReference,
                                           frameDescriptor,
                                           stopMarker, thread);
                if (done) {
                    break;
                }
                numStackFrames++;
            }
            calleeSaves.ClearCalleeSaves();
            return numStackFrames;
        }

#if SINGULARITY
        private static UIntPtr SkipLinkStackFrame(ref UIntPtr *framePointer,
                                                  ref UIntPtr *stackPointer)
        {
            // The stack pointer and the frame pointer are in the same
            // stack segment.  We still need to skip over the frame
            // set up for the function that called LinkStack hasn't been
            // executed yet (the GC interaction occurred during allocation
            // of the new stack segment).
            stackPointer = framePointer + 2;
            framePointer = (UIntPtr*) *framePointer;
            return *(stackPointer - 1);
        }

        private static UIntPtr SkipUnlinkStackFrame(ref UIntPtr *framePointer,
                                                    ref UIntPtr *stackPointer)
        {
            // The frame pointer is already set up.  The stack pointer
            // needs to be adjusted for the two PC values (LinkStackXX and
            // UnlinkStack) and the two spilled values pushed onto the stack.
            stackPointer = stackPointer + 4;
            return *(stackPointer - 1);
        }

        private static UIntPtr SkipLinkStackStubFrame(ref UIntPtr *framePointer,
                                                      ref UIntPtr *stackPointer)
        {
            // 'framePointer' points to the ebp in the old frame
            // since at the end of WalkStackFrame, it sets return addr
            // and pops up a frame. However, since we are using linked
            // stacks, "pop up a frame" didn't actually set the frame
            // to the caller's frame, it just goes from the new frame to the
            // old frame, therefore, we need to get return addr and pop
            // a frame again.
            stackPointer = framePointer + 2;
            framePointer = (UIntPtr*) *framePointer;
            return *(stackPointer - 1);
        }
#endif
    }
}
