////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ThreadContext.cs
//
//  Note:
//

namespace Microsoft.Singularity
{
    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;

    using Microsoft.Singularity.V1.Threads;
    using Microsoft.Singularity.Isal;

    [NoCCtor]
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential)]
    [StructAlign(16)]
    [AccessedByRuntime("referenced from c++")]
    internal struct ThreadContext
    {
        [AccessedByRuntime("referenced from c++")]
        internal ThreadRecord   threadRecord;

        [AccessedByRuntime("referenced from c++")]
        internal ushort num;
        [AccessedByRuntime("referenced from c++")]
        internal ushort regs;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe ThreadContext * prev;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe ThreadContext * next;

        [AccessedByRuntime("referenced from c++")]
        internal unsafe ThreadContext * prevInKern;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe ThreadContext * nextInKern;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe ThreadContext * prevInProc;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe ThreadContext * nextInProc;

        [AccessedByRuntime("referenced from c++")]
        internal UIntPtr stackBegin;
        [AccessedByRuntime("referenced from c++")]
        internal UIntPtr stackLimit;
        [AccessedByRuntime("referenced from c++")]
        internal ushort processId;
        [AccessedByRuntime("referenced from c++")]
        internal bool uncaughtFlag; // true means "uncaught exception from process, so throw exception in kernel"
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal bool suspendAlert; // true means "check whether thread should suspend"

        // Note: These two forks must be exactly the same size, but their
        // fields alias differently for kernel or process code.
#if SINGULARITY_KERNEL
        [AccessedByRuntime("referenced from c++")]
        internal unsafe void *_thread;
        [AccessedByRuntime("referenced from c++")]
        internal UIntPtr processThread;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe System.GCs.CallStack.TransitionRecord * stackMarkers;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe System.GCs.CallStack.TransitionRecord * processMarkers;
        [AccessedByRuntime("referenced from c++")]
        internal ushort threadIndex;
        [AccessedByRuntime("referenced from c++")]
        internal ushort processThreadIndex;
#elif SINGULARITY_PROCESS
        [AccessedByRuntime("referenced from c++")]
        internal UIntPtr kernelThread;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe void *_thread;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe System.GCs.CallStack.TransitionRecord * kernelMarkers;
        [AccessedByRuntime("referenced from c++")]
        internal unsafe System.GCs.CallStack.TransitionRecord * stackMarkers;
        [AccessedByRuntime("referenced from c++")]
        internal ushort kernelThreadIndex;
        [AccessedByRuntime("referenced from c++")]
        internal ushort threadIndex;
#endif
        [AccessedByRuntime("referenced from halforgc.asm")]
        internal unsafe int gcStates;
        // See ThreadContext.IsInKernelMode
        private unsafe System.GCs.CallStack.TransitionRecord * modeMarker;

#if PAGING
        [AccessedByRuntime("referenced from c++")]
        internal UIntPtr abiStackHead;
        [AccessedByRuntime("referenced from c++")]
        internal UIntPtr abiStackBegin;
        [AccessedByRuntime("referenced from c++")]
        internal UIntPtr abiStackLimit;
#endif

#if THREAD_TIME_ACCOUNTING
        [AccessedByRuntime("referenced from c++")]
        internal ulong lastExecutionTimeUpdate;

        [AccessedByRuntime("referenced from c++")]
        internal ulong executionTime;
#endif
        //////////////////////////////////////////////// Methods & Properties.
        //
        internal Thread thread {
            [NoHeapAllocation]
            get { return GetThread(); }
        }

        [NoHeapAllocation]
        internal unsafe bool IsFirst()
        {
            return (((UIntPtr)prev) == UIntPtr.Zero);
        }

        [AccessedByRuntime("referenced from c++")]
        // Return true if the thread is in kernel mode, false if the
        // thread is in process mode.
        // Note that by the time this method returns, the thread might
        // have already switched to a different mode; in other words,
        // don't rely on this result of this method being up-to-date unless
        // the thread is suspended or blocked.
        [NoHeapAllocation]
        internal unsafe bool IsInKernelMode()
        {
            // When a thread enters process mode, RuntimeEntryPoint
            // sets modeMarker=processMarkers.  Thus, in process mode:
            //
            //   modeMarker == processMarkers
            //
            // When a thread in process mode calls the kernel, pushStackMark
            // pushes a child process marker onto the stack, so that
            // modeMarker is left pointing to the new processMarker's
            // parent (the old processMarker).  Thus, in kernel mode:
            //
            //   modeMarker == parent(processMarkers)
            //
            // This keeps the mode in sync with the process stack markers,
            // which is convenient though not essential.  This assumes that
            // the only reason a process pushes a stack marker is to enter
            // kernel mode.
            //
            // Since processMarkers may be null, ThreadContext.ParentModeMarker
            // defines a special definition for parent(null).
#if SINGULARITY_PROCESS
            System.GCs.CallStack.TransitionRecord * processMarkers =
                stackMarkers;
#endif // SINGULARITY_PROCESS
            if (modeMarker == processMarkers) {
                return false;
            }
            else {
                VTable.Assert(modeMarker == ParentModeMarker(processMarkers));
                return true;
            }
        }

        [AccessedByRuntime("referenced from c++")]
        [NoHeapAllocation]
        internal unsafe void SetKernelMode()
        {
#if SINGULARITY_PROCESS
            System.GCs.CallStack.TransitionRecord * processMarkers =
                stackMarkers;
#endif // SINGULARITY_PROCESS
            modeMarker = ParentModeMarker(processMarkers);
        }

        [AccessedByRuntime("referenced from c++")]
        [NoHeapAllocation]
        internal unsafe void SetProcessMode()
        {
#if SINGULARITY_PROCESS
            System.GCs.CallStack.TransitionRecord * processMarkers =
                stackMarkers;
#endif // SINGULARITY_PROCESS
            modeMarker = processMarkers;
        }

        [NoHeapAllocation]
        internal bool IsRunning()
        {
            return !threadRecord.spill.IsSpilled;
        }

        [NoHeapAllocation]
        static private unsafe System.GCs.CallStack.TransitionRecord *
            ParentModeMarker(System.GCs.CallStack.TransitionRecord * child)
        {
            System.GCs.CallStack.TransitionRecord * bottom =
                (System.GCs.CallStack.TransitionRecord *) (-1);

            VTable.Assert(child != bottom);
            if (child == null) {
                return bottom;
            }
            else {
                return child->oldTransitionRecord;
            }
        }

        //////////////////////////////////////////////////// External Methods.
        //
        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(32)]
        [NoHeapAllocation]
        private extern Thread GetThread();

        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal extern void UpdateAfterGC(Thread thread);

#if SINGULARITY_KERNEL
        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal extern void Initialize(int threadIndex, UIntPtr stackBegin, uint cr3);

        [AccessedByRuntime("output to header: defined in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal extern void InitializeIdle(int threadIndex, UIntPtr stackBegin, uint cr3);
#endif
    }
}

// This is a temporary workaround to get around bartok assumptions
namespace Microsoft.Singularity.X86
{
  using System.Runtime.CompilerServices;

  struct ProcessorContext
  {
      [RequiredByBartok]
      Microsoft.Singularity.X86.ThreadContext threadContext;
  }

  struct ThreadContext
  {
      [RequiredByBartok]
      System.UIntPtr stackLimit;
  }
}
