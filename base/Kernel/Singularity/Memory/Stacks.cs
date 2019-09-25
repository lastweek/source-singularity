////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Primitive stack segment manager
//

#if SINGULARITY_LINKED_STACKS
#else
#define USE_BIG_STACKS
#endif

//#define DEBUG_STACK_VERBOSE
//#define DO_TRACE_STACKS
namespace Microsoft.Singularity.Memory
{

    using System;
    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
    using System.Threading;
    using System.GCs;
    using Microsoft.Singularity;
    using Microsoft.Singularity.Isal;

    internal partial class Stacks {

        private static GetKernelStackCallback getKernelStackCallback;
        private static GetSipStackCallback getSipStackCallback;
        private static ReturnKernelStackCallback returnKernelStackCallback;
        private static ReturnSipStackCallback returnSipStackCallback;

        // This constant gives a reasonable size for an initial stack
        // chunk, leaving room for the metadata that will be added to
        // the top of the stack (sizeof(StackHead)).


#if USE_BIG_STACKS
        internal const int InitialStackSize = 0xfb00;
        internal const int SafetyBufferSize = 0x0400;
#elif ISA_IX64 || ISA_ARM || PHXBRIDGE
        // TODO: FIXFIX set back to f00
        internal const int InitialStackSize = 0xfb00;
        internal const int SafetyBufferSize = 0x0400;
#else
        internal const int InitialStackSize = 0x0f00;
        internal const int SafetyBufferSize = 0x0000;
#endif

        [StructLayout(LayoutKind.Sequential)]
        internal struct StackHead
        {
            internal UIntPtr    prevBegin;
            internal UIntPtr    prevLimit;
            internal UIntPtr    esp;
        };

        internal static void Initialize()
        {
            Tracing.Log(Tracing.Debug, "Stacks.Initialize() called");
            getKernelStackCallback = new GetKernelStackCallback();
            getSipStackCallback = new GetSipStackCallback();
            returnKernelStackCallback = new ReturnKernelStackCallback();
            returnSipStackCallback = new ReturnSipStackCallback();
        }

        internal static void Finalize()
        {
            Tracing.Log(Tracing.Debug, "Stacks.Finalize() KernelStacks");
            Tracing.Log(Tracing.Debug, "Stacks.Finalize()");
        }

        private class GetKernelStackCallback : Isa.ICallback
        {
            internal override UIntPtr Callback(UIntPtr param)
            {
                VTable.Assert(Isa.IsRunningOnInterruptStack);

                unsafe {
                    return GetStackSegment(param,
                                           ref *Processor.GetCurrentThreadContext(), true, false);
                }
            }
        }

        private class GetSipStackCallback : Isa.ICallback
        {
            internal override UIntPtr Callback(UIntPtr param)
            {
                VTable.Assert(Isa.IsRunningOnInterruptStack);

                unsafe {
                    UIntPtr stack = GetStackSegment(param,
                                                    ref *Processor.GetCurrentThreadContext(),
                                                    false, false);
                    if (stack == 0) {

                        // Allocate from the kernel reservation so we may terminate the SIP

                        stack = GetStackSegment(param, ref *Processor.GetCurrentThreadContext(),
                                                true, false);

                        // Note that even if we failed again and are returning null, we
                        // must return before any overflow handling logic, to get off
                        // the interrupt stack.

                    }

                    return stack;
                }
            }
        }

        private class ReturnKernelStackCallback : Isa.ICallback
        {
            internal override UIntPtr Callback(UIntPtr param)
            {
                VTable.Assert(Isa.IsRunningOnInterruptStack);

                unsafe {
                    ReturnStackSegmentRawCommon(ref *Processor.GetCurrentThreadContext(),
                                                true, false);
                }
                return 0;
            }
        }

        private class ReturnSipStackCallback : Isa.ICallback
        {
            internal override UIntPtr Callback(UIntPtr param)
            {
                VTable.Assert(Isa.IsRunningOnInterruptStack);

                unsafe {
                    ReturnStackSegmentRawCommon(ref *Processor.GetCurrentThreadContext(),
                                                false, false);
                }
                return 0;
            }
        }

        [NoStackLinkCheckTrans]
        internal static UIntPtr GetSipStackSegment(UIntPtr size)
        {
            UIntPtr stack;

            // @TODO: Historically we have disabled interrupts around stack growth.
            // Actually I think it is unnecessary; however to be conservative for
            // now we will disable interrupts while we use the interrupt stack.

            bool en = Processor.DisableInterrupts();
            try {
                unsafe {
                    // Sanity check: we allocate from the current stack segment, and
                    // will set the thread context to point to a new stack segment

                    VTable.Assert(Isa.GetStackPointer() <=
                                  Processor.GetCurrentThreadContext()->stackBegin);
                    VTable.Assert(Isa.GetStackPointer() >=
                                  Processor.GetCurrentThreadContext()->stackLimit);
                }
                stack = Isa.CallbackOnInterruptStack(getSipStackCallback, size);
            }
            finally {
                Processor.RestoreInterrupts(en);
            }

            return stack;
        }

        [NoStackLinkCheckTrans]
        internal static UIntPtr GetKernelStackSegment(UIntPtr size)
        {
            UIntPtr stack;

            // @TODO: see note about disabling interrupts above.
            bool en = Processor.DisableInterrupts();
            try {
                unsafe {
                    // Sanity check: we allocate from the current stack segment, and
                    // will set the thread context to point to a new stack segment

                    VTable.Assert(Isa.GetStackPointer() <=
                                  Processor.GetCurrentThreadContext()->stackBegin);
                    VTable.Assert(Isa.GetStackPointer() >=
                                  Processor.GetCurrentThreadContext()->stackLimit);
                }
                stack = Isa.CallbackOnInterruptStack(getKernelStackCallback, size);
            }
            finally {
                Processor.RestoreInterrupts(en);
            }

            return stack;
        }

        //
        // This is called for each new thread to get the initial stack segment.
        //
        [NoStackLinkCheckTrans]
        internal static UIntPtr GetInitialStackSegment(ref ThreadContext context)
        {
            // The first stack segment is always in kernel memory
            UIntPtr ret = GetStackSegment(0, ref context, true, true);
            return ret;
        }

        [NoStackLinkCheckTrans]
        internal static unsafe UIntPtr GetStackSegment(UIntPtr size,
                                                       ref ThreadContext context,
                                                       bool kernelAllocation,
                                                       bool initialStack)
        {
#if SINGULARITY_LINKED_STACKS
#else
            if (!initialStack) {
                // If we get here, then the initial stack size must not have
                // been sufficient to ensure that we don't need linked stacks.
                DebugStub.Break();
            }
#endif
            UIntPtr begin = context.stackBegin;
            UIntPtr limit = context.stackLimit;
#if DO_TRACE_STACKS
            Kernel.Waypoint(666);
#endif
            StackHead *head = GetStackSegmentRaw(size, ref context, kernelAllocation, initialStack);
            if (head != null) {
                head->prevBegin = begin;
                head->prevLimit = limit;
                head->esp = 0;
            }
            return (UIntPtr)head;
        }

        [NoStackLinkCheckTrans]
        internal static unsafe StackHead * GetStackSegmentRaw(UIntPtr size,
                                                              ref ThreadContext context,
                                                              bool kernelAllocation,
                                                              bool initialStack)
        {
            // Allocate a new chunk, making room for StackHead at the top.
            // If you change these constants to add more data, see the
            // comment about InitialStackSize at the top of this file!
#if DO_TRACE_STACKS
            Kernel.Waypoint(667);
#endif
            if (size == UIntPtr.Zero) {
                size = InitialStackSize;
            }
            size = MemoryManager.PagePad(size + sizeof(StackHead) + SafetyBufferSize);

            UIntPtr chunk;


            Process owner = Process.GetProcessByID(context.processId);
            //
            //// NOTE: here's where we should be clever about
            //// whether to allocate a stack chunk in the user range
            //// or the kernel range. Except, if we switch contexts
            //// during an ABI call while using a user-range stack
            //// segment on a paging machine, we die. Gloss over
            //// this hackily by always getting stack segments
            //// from the kernel range.
            //if (kernelAllocation || (owner == Process.kernelProcess)) {
            //  chunk = MemoryManager.KernelAllocate(
            //      MemoryManager.PagesFromBytes(size), owner, 0, PageType.Stack);
            //}
            //else {
            //  chunk = MemoryManager.UserAllocate(
            //      MemoryManager.PagesFromBytes(size), owner, 0, PageType.Stack);
            //}
            //

            UIntPtr  pageCount = MemoryManager.PagesFromBytes(size);
#if DEBUG_STACK_VERBOSE
            fixed (ThreadContext *ptr = &context) {
                Tracing.Log(Tracing.Debug,
                            "GetStackSegmentRaw(ctx={0:x8},size={1:d}) pages={2} [{3:x8}..{4:x8}]",
                            (UIntPtr)ptr, size, pageCount,
                            context.stackLimit, context.stackBegin);
           }
#endif
            chunk = MemoryManager.StackAllocate(pageCount, owner, 0, kernelAllocation, initialStack);

            if (chunk != UIntPtr.Zero) {
                // NB: We do _not_ zero out stack memory!
                // We assume that Bartok prevents access to prev contents.
                StackHead *head = (StackHead *)(chunk + size - sizeof(StackHead));

                context.stackBegin = chunk + size;
                context.stackLimit = chunk + SafetyBufferSize;

#if DEBUG_STACK_VERBOSE
                Tracing.Log(Tracing.Debug,
                            "GetStackSegmentRaw(size={0:d}) -> [{1:x8}..{2:x8}]",
                            size, context.stackLimit, context.stackBegin);
#endif
                return head;
            }
            else {
                // Stack allocation failed.  In the future, we should
                // trigger a kernel exception; for now, we break to the
                // debugger.
#if DEBUG_STACK_VERBOSE
                Tracing.Log(Tracing.Debug,
                            "GetStackSegmentRaw: KernelAllocate failed!(siz={0:d})",
                            size);
#endif
                //DebugStub.Break();
                return null;
            }
        }

        // This is called when returning a kernel stack segment
        [AccessedByRuntime("referenced from halstack.asm")]
        [NoStackOverflowCheck]
        internal static void ReturnKernelStackSegment()
        {
            // @TODO: see note about disabling interrupts above.
            bool en = Processor.DisableInterrupts();
            try {
                Isa.CallbackOnInterruptStack(returnKernelStackCallback, 0);

                unsafe {
                    // Sanity check: we freed from the previous segment, and
                    // should have set the thread context to point to this segment now.
                    VTable.Assert(Isa.GetStackPointer() <=
                                  Processor.GetCurrentThreadContext()->stackBegin);
                    VTable.Assert(Isa.GetStackPointer() >=
                                  Processor.GetCurrentThreadContext()->stackLimit);
                }
            }
            finally {
                Processor.RestoreInterrupts(en);
            }
        }

        // This is called when returning a stack segment allocated for a SIP
        [AccessedByRuntime("referenced from halstack.asm")]
        [NoStackOverflowCheck]
        internal static void ReturnSipStackSegment()
        {
            // @TODO: see note about disabling interrupts above.
            bool en = Processor.DisableInterrupts();
            try {
                Isa.CallbackOnInterruptStack(returnSipStackCallback, 0);

                unsafe {
                    // Sanity check: we freed from the previous segment, and
                    // should have set the thread context to point to this segment now.

                    VTable.Assert(Isa.GetStackPointer() <=
                                  Processor.GetCurrentThreadContext()->stackBegin);
                    VTable.Assert(Isa.GetStackPointer() >=
                                  Processor.GetCurrentThreadContext()->stackLimit);
                }
            }
            finally {
                Processor.RestoreInterrupts(en);
            }
        }

        [NoStackOverflowCheck]
        internal static unsafe void ActivatePreviousStackSegmentLimit()
        {
            // To avoid sprinkling [NoStackOverflowCheck] attributes
            // on too many methods, we manually inline a couple of methods.

            // ThreadContext *context = Processor.GetCurrentThreadContext();
            ThreadRecord *threadRecord = Isa.GetCurrentThread();
            ThreadContext *context = (ThreadContext *) threadRecord;
            StackHead *head = (StackHead *)
                (context->stackBegin - sizeof(StackHead));

            // Isa.StackLimit = head->prevLimit;
            threadRecord->activeStackLimit = head->prevLimit;
        }

        [AccessedByRuntime("referenced from halstack.asm")]
        [NoStackLinkCheckTrans]
        internal static unsafe void ReturnStackSegmentRawCommon(ref ThreadContext context,
                                                                bool kernelAllocation,
                                                                bool initialStack)
        {
            UIntPtr begin = context.stackBegin;
            UIntPtr limit = context.stackLimit;

            StackHead *head = (StackHead *)(begin - sizeof(StackHead));

#if DO_TRACE_STACKS
            Kernel.Waypoint(669);
#endif

            UIntPtr addr = limit - SafetyBufferSize;
            UIntPtr size = begin - limit + SafetyBufferSize;

#if DEBUG_STACK_VERBOSE
            fixed (ThreadContext *ptr = &context) {
                Tracing.Log(Tracing.Debug,
                            "ReturnStackSegmentRaw(ctx={0:x8}) [{1:x8}..{2:x8}]\n",
                            (UIntPtr)ptr, context.stackLimit, context.stackBegin);
            }
#endif

#if !PAGING
            context.stackBegin = head->prevBegin;
            context.stackLimit = head->prevLimit;
#else
            //context.stackBegin = head->prevBegin;
            //context.stackLimit = head->prevLimit;
            // Moved below, because of the following scenario:
            //   - call UnlinkStack
            //   - UnlinkStack switches to the scheduler stack
            //   - UnlinkStack calls ReturnStackSegmentRaw, which calls
            //     various other methods
            //   - one of the other methods invokes write barrier code
            //   - the write barrier code performs a stack link check
            //   - If context.stackLimit is already set to head->prevLimit,
            //     then it may appear that we're out of stack space,
            //     even if we're really not, so we jump to LinkStack
            //   - LinkStack overwrites the scheduler stack
            // TODO: really fix this.
            UIntPtr stackBegin = head->prevBegin;
            UIntPtr stackLimit = head->prevLimit;
#endif

            Process owner = Process.GetProcessByID(context.processId);
            //
            //// See note above in GetStackSegmentRaw
            //if ((owner != Process.kernelProcess) &&
            //(addr >= BootInfo.KERNEL_BOUNDARY)) {
            //MemoryManager.UserFree(addr, MemoryManager.PagesFromBytes(size), owner);
            //}
            //else {
            //MemoryManager.KernelFree(addr, MemoryManager.PagesFromBytes(size), owner);
            //}
            //
            MemoryManager.StackFree(addr, MemoryManager.PagesFromBytes(size), owner, kernelAllocation, initialStack);

#if PAGING
            // See comments above.
            context.stackBegin = stackBegin;
            context.stackLimit = stackLimit;
#endif

#if DEBUG_STACK_VERBOSE
            Tracing.Log(Tracing.Debug,
                        "ReturnStackSegment({0:x8}, {1:x8}) [{2:x8}..{3:x8}]\n",
                        addr, size, context.stackLimit, context.stackBegin);
#endif
        }

        //
        // This is called when a thread is destroyed and its last
        // stack segment is returned to the system
        //
        [AccessedByRuntime("referenced from halstack.asm")]
        [NoStackLinkCheckTrans]
        // NB: This function must execute in low-stack conditions!
        // See the comment at the top of this file.
        internal static void ReturnInitialStackSegment(ref ThreadContext context)
        {
            ReturnStackSegmentRawCommon(ref context, true, true);
        }

        //
        // This is called when cleaning up orphaned stack segments of the thread
        // when it is destroyed, usually as a result of an exception such as SIP
        // stack overflow.
        //
        [AccessedByRuntime("referenced from halstack.asm")]
        [NoStackLinkCheckTrans]
        // NB: This function must execute in low-stack conditions!
        // See the comment at the top of this file.
        internal static void ReturnStackSegment(ref ThreadContext context)
        {
            ReturnStackSegmentRawCommon(ref context, true, false);
        }

        //
        // This is invoked by ring0_halstack.asm when a SIP stack overflows
        // and no more memory can be allocated from the OS for it.
        //
        // It is expected that the SIP is "failed fast" and does not
        // return from this call.
        //
        [ExternalEntryPoint]
        [AccessedByRuntime("reference from halstack.asm")]
        internal static void StackOverflowForSIP()
        {
            DebugStub.WriteLine("******** SIP OOM on Stack, Failing Fast ********");

            // This does not make a stack transition record
            Thread.CurrentProcess.Stop((int)System.ProcessExitCode.ErrorDefault);

             // Should not return
            DebugStub.Break();
        }

        internal static unsafe void WalkStack(UIntPtr ebp)
        {
            System.GCs.CallStack.TransitionRecord *kernMarker;
            System.GCs.CallStack.TransitionRecord *procMarker;

            kernMarker = Processor.GetCurrentThreadContext()->stackMarkers;
            procMarker = Processor.GetCurrentThreadContext()->processMarkers;
            UIntPtr ebpKern = kernMarker != null ? kernMarker->calleeSaveRegisters.GetFramePointer() : UIntPtr.Zero;
            UIntPtr ebpProc = procMarker != null ? procMarker->calleeSaveRegisters.GetFramePointer() : UIntPtr.Zero;

#if DEBUG_STACK_VERBOSE
            fixed (byte * begin = &LinkStackBegin) {
                fixed (byte * limit = &LinkStackLimit) {
                    DebugStub.Print("LinkStack: {0:x8}..{1:x8}\n",
                                    __arglist((UIntPtr)begin, (UIntPtr)limit));
                }
            }

#endif

            DebugStub.Print("EBP={0:x8}, kernMarkers={1:x8}, procMarkers={2:x8}\n",
                            __arglist(ebp, (UIntPtr)kernMarker, (UIntPtr)procMarker));
            DebugStub.Print("EBP.....: EBP..... EIP..... transitn nexttran stbottom\n");

            while (ebp != UIntPtr.Zero) {
                if (ebp == ebpKern) {
                    DebugStub.Print("--kern--: {0:x8} {1:x8} {2:x8} {3:x8} {4:x8}\n",
                                    __arglist(ebpKern,
                                              (UIntPtr)kernMarker,
                                              kernMarker->callAddr,
                                              (UIntPtr)kernMarker->oldTransitionRecord,
                                              kernMarker->stackBottom));
                    kernMarker = kernMarker->oldTransitionRecord;
                    ebpKern = kernMarker != null ? kernMarker->calleeSaveRegisters.GetFramePointer() : UIntPtr.Zero;
                }
                if (ebp == ebpProc) {
                    DebugStub.Print("--proc--: {0:x8} {1:x8} {2:x8} {3:x8} {4:x8}: \n",
                                    __arglist(ebpProc,
                                              (UIntPtr)procMarker,
                                              procMarker->callAddr,
                                              (UIntPtr)procMarker->oldTransitionRecord,
                                              procMarker->stackBottom));

                    procMarker = procMarker->oldTransitionRecord;
                    ebpProc = procMarker != null ? procMarker->calleeSaveRegisters.GetFramePointer() : UIntPtr.Zero;
                }
                DebugStub.Print("{0:x8}: {1:x8} {2:x8}\n",
                                __arglist(ebp,
                                          ((UIntPtr*)ebp)[0], ((UIntPtr*)ebp)[1]));

                if (((UIntPtr*)ebp)[1] == UIntPtr.Zero) {
                    break;
                }
                ebp = ((UIntPtr*)ebp)[0];
            }
            // DebugStub.Break();
        }
    }
}
