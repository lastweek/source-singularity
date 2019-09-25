////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Processor.cs
//
//  Note:
//

//#define DEBUG_EXCEPTIONS
//#define DEBUG_INTERRUPTS
//#define DEBUG_DISPATCH_TIMER
//#define DEBUG_DISPATCH_IO
//#define CHECK_DISABLE_INTERRUPTS

// #define SINGULARITY_ASMP

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity.Eventing;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Isal;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Scheduling;
using Microsoft.Singularity.V1.Threads;

// For Abi Call
// using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity
{

    [CLSCompliant(false)]
    public enum ProcessorEvent : ushort
    {
        Exception = 0,
        Resume    = 1,
        Interrupt = 2
    }

    [CLSCompliant(false)]
    [CCtorIsRunDuringStartup]
    [AccessedByRuntime("referenced in hal.cpp/processor.cpp")]
    public class Processor
    {
        // Callback object for context switching
        static ResumeThreadCallback resumeThreadCallback;

        private ProcessorLogger ProcessorLog = null;
        private ProcessorCounter processorCounter = null;
        internal SamplingProfiler Profiler = null;
        internal bool nextSampleIdle = false;

        internal static bool IsSamplingEnabled = false;

        //
        // This is called by HalDevicesApic.StartApProcessors() when
        // initializing additional physical AP processors to set its
        // hardware state when its started.
        //
        public void InitializeKernelThreadState(Thread thread,
                                                UIntPtr kernelStackBegin,
                                                UIntPtr kernelStackLimit)
        {
            kernelThread = thread;
            kernelStackBegin = kernelStackBegin;
            kernelStackLimit = kernelStackLimit;
        }

        public HalTimer Timer
        {
            [NoHeapAllocation]
            get { return timer; }
        }

        public HalClock Clock
        {
            [NoHeapAllocation]
            get { return clock; }
        }

        internal static void InitializeProcessorTable(int cpus)
        {
            // use the full value initially
            ExpectedProcessors = cpus;
            processorTable = new Processor[cpus];
            for (int i = 0; i < processorTable.Length; i++) {
                processorTable[i] = new Processor(i);
            }
            DebugStub.WriteLine("Processors: {0} of {1}",
                                __arglist(processorTable.Length, cpus));
        }

        internal static void AllocateStack(UIntPtr size, out UIntPtr begin, out UIntPtr limit)
        {
            Kernel.Waypoint(818);
            size = MemoryManager.PagePad(size);
            limit = MemoryManager.KernelAllocate(
                MemoryManager.PagesFromBytes(size), null, 0, System.GCs.PageType.Stack);
            begin = limit + size;
            Kernel.Waypoint(819);
        }

        private Processor(int index)
        {
            processorIndex = index;

            if (interruptCounts == null) {
                interruptCounts = new int [256];
            }

            ProcessorLog = ProcessorLogger.Create("ProcessorLogger:"+index.ToString());
            processorCounter = ProcessorCounter.Create("ProcessorCounters:"+index.ToString(), 256);

            DebugStub.WriteLine("Processor: {0}", __arglist(index));
        }

        public void EnableProfiling()
        {
            if (SamplingEnabled()) {
                Profiler = SamplingProfiler.Create("SampleProfiler:" + Id.ToString(),
                                                   32,  // maximum stack depth
                                                   Kernel.ProfilerBufferSize); // sampling buffer size

                DebugStub.WriteLine("Sampling profiler enabled");
            }
        }

        public static Processor EnableProcessor(int processorId)
        {
            Processor p = processorTable[processorId];
            p.Initialize(processorId);
            return p;
        }

        private unsafe void Initialize(int processorId)
        {
            uint DefaultStackSize = 0xA000;

            processorTable[processorId] = this;

            context = (ProcessorContext*) Isa.GetCurrentCpu();

            DebugStub.WriteLine("Processor context: {0} {1:x8}",
                                __arglist(processorId, Kernel.AddressOf(context)));

            context->UpdateAfterGC(this);

            if (0 != processorId) {
                Thread.BindKernelThread(kernelThread,
                                    kernelStackBegin,
                                    kernelStackLimit);
            }

            AllocateStack(DefaultStackSize,
                          out context->cpuRecord.interruptStackBegin,
                          out context->cpuRecord.interruptStackLimit);

            Tracing.Log(Tracing.Debug, "Initialized Processor {0}",
                        (UIntPtr)processorId);

            Tracing.Log(Tracing.Debug, "asmInterruptStack={0:x}..{1:x}",
                        context->cpuRecord.interruptStackBegin,
                        context->cpuRecord.interruptStackLimit);

#if false
            DebugStub.WriteLine("proc{0}: InterruptStack={1:x}..{2:x}",
                                __arglist(
                                    processorId,
                                    context->cpuRecord.interruptStackBegin,
                                    context->cpuRecord.interruptStackLimit
                                    ));
#endif

            Interlocked.Increment(ref runningCpus);
            MpExecution.AddProcessorContext(context);

            // Need to allocate this callback object outside of NoThreadAllocation region
            if (processorId == 0) {
                resumeThreadCallback = new ResumeThreadCallback();
            }

            Isa.EnableCycleCounter();
        }

        ///
        /// <summary>
        ///     Initialize dispatcher
        /// </summary>
        ///
        /// <param name="processorId">Id of the processor dispatcher belongs to</param>
        ///
        public static void InitializeDispatcher(int processorId)
        {
            // Create a processor dispatcher
            processorTable[processorId].dispatcher = new ProcessorDispatcher();

            // Initialize dispatcher
            processorTable[processorId].dispatcher.Initialize(processorTable[processorId]);
        }

        ///
        /// <summary>
        ///     Activate Timer
        /// </summary>
        ///
        ///
        public static void ActivateTimer(int processorId)
        {
            processorTable[processorId].timer.SetNextInterrupt(TimeSpan.FromMilliseconds(5));
        }

        [NoHeapAllocation]
        public void Uninitialize(int processorId)
        {
            Tracing.Log(Tracing.Debug, "UnInitializing Processor {0}",
                        (UIntPtr)processorId);

            Interlocked.Decrement(ref runningCpus);

// #if DEBUG
            // Interrupts should be off now
            if (!InterruptsDisabled()) {
                DebugStub.WriteLine("Processor::Uninitialize AP Processor does not have interrupts disabled\n");
                DebugStub.Break();
            }
// #endif // DBG

            // Processor is out of commission
            HaltUntilInterrupt();
// #if DEBUG

            DebugStub.WriteLine("Processor::Uninitialize: AP processor woke up on shutdown!\n");
            DebugStub.Break();
// #endif // DBG

        }

        public void AddPic(HalPic pic)
        {
            Tracing.Log(Tracing.Audit, "AddPic({0})\n",
                        Kernel.TypeName(pic));
            this.pic = pic;
        }

        [NoHeapAllocation]
        public HalPic GetPic()
        {
            return this.pic;
        }

        [NoHeapAllocation]
        public void AddTimer(byte interrupt, HalTimer timer)
        {
            Tracing.Log(Tracing.Audit, "AddTimer({0}) on {1}\n",
                        Kernel.TypeName(timer), interrupt);
            this.timer = timer;
            this.timerInterrupt = interrupt;
        }

        [NoHeapAllocation]
        public void AddClock(byte interrupt, HalClock clock)
        {
            Tracing.Log(Tracing.Audit, "AddClock({0}) on {1}\n",
                        Kernel.TypeName(clock), interrupt);
            this.clock = clock;
            this.clockInterrupt = interrupt;
        }

        [NoHeapAllocation]
        public static void AddMemory(HalMemory aHalMemory)
        {
            Tracing.Log(Tracing.Audit, "AddHalMemory({0})\n",
                        Kernel.TypeName(aHalMemory));
            halMemory = aHalMemory;
        }

        [NoHeapAllocation]
        internal unsafe void Display()
        {
            int stackVariable;
            UIntPtr currentStack = new UIntPtr(&stackVariable);

            unchecked {
                Tracing.Log(Tracing.Debug, "Interrupt stack: {0:x} {1:x}..{2:x} uses",
                            currentStack,
                            context->cpuRecord.interruptStackBegin,
                            context->cpuRecord.interruptStackLimit);
            }
        }

        // Returns the processor that the calling thread is running on.
        // TODO:Needs to be fixed. (Added for consistency)
        public static Processor CurrentProcessor
        {
            [NoHeapAllocation]
            get { return GetCurrentProcessor(); }
        }

        ///
        /// <summary>
        ///     Retrieve current dispatcher
        /// </summary>
        public ProcessorDispatcher Dispatcher
        {
            [NoHeapAllocation]
            get { return dispatcher; }
        }


        [NoHeapAllocation]
        public static int GetCurrentProcessorId()
        {
            return GetCurrentProcessor().Id;
        }

        public unsafe int Id
        {
            [NoHeapAllocation]
            get {
                return context->cpuRecord.id;
            }
        }

        [NoHeapAllocation]
        public static Processor GetProcessor(int i)
        {
            if (null == processorTable && i == 0) {
                return CurrentProcessor;
            }
            else {
                return processorTable[i];
        }
        }

        public static int CpuCount
        {
            [NoHeapAllocation]
            get { return null == processorTable ? 1 : processorTable.Length; }
        }

        [NoHeapAllocation]
        public static void HaltUntilInterrupt()
        {
            Platform.ThePlatform.Halt();
        }

        [NoHeapAllocation]
        public int GetInterruptCount(byte interrupt)
        {
            return interruptCounts[interrupt];
        }

        public int GetIrqCount(byte irq)
        {
            HalPic pic = CurrentProcessor.pic;

            // Only set on native hal
            if (pic == null) {
                return 0;
            }

            return interruptCounts[pic.IrqToInterrupt(irq)];
        }

        public static byte GetMaxIrq()
        {
            HalPic pic = CurrentProcessor.pic;

            // This is not set on halhyper or halwin32
            if (pic == null) {
                return 0;
            }

            return CurrentProcessor.pic.MaximumIrq;
        }

        public static ulong CyclesPerSecond
        {
            [NoHeapAllocation]
            get { return GetCurrentProcessor().cyclesPerSecond; }

            [NoHeapAllocation]
            set { GetCurrentProcessor().cyclesPerSecond = value; }
        }

        public static ulong CycleCount
        {
            [NoHeapAllocation]
            get { return Isa.GetCycleCount(); }
        }

        //////////////////////////////////////////////////////////////////////
        //
        //

        [NoHeapAllocation]
        public static bool SamplingEnabled()
        {
            return (Kernel.ProfilerBufferSize != 0);
        }

        internal static void StartSampling()
        {
            if (SamplingEnabled()) {
                IsSamplingEnabled = true;
        }
        }

        [NoHeapAllocation]
        internal void NextSampleIsIdle()
        {
            nextSampleIdle = true;
        }

        //////////////////////////////////////////////////// External Methods.
        //
        [NoHeapAllocation]
        internal static Processor GetCurrentProcessor()
        {
            unsafe {
                return GetCurrentProcessorContext()->processor;
                }
            }

        [NoHeapAllocation]
        [AccessedByRuntime("output to header : called by c code")]
        internal static unsafe ThreadContext * GetCurrentThreadContext()
        {
            unsafe {
                return (ThreadContext *) Isa.GetCurrentThread();
            }
        }

        [NoHeapAllocation]
        [AccessedByRuntime("output to header : called by c code")]
        internal static unsafe ProcessorContext * GetCurrentProcessorContext()
        {
            unsafe {
                return (ProcessorContext *) Isa.GetCurrentCpu();
            }
        }

        [NoHeapAllocation]
        internal static Thread GetCurrentThread()
        {
            unsafe {
                return GetCurrentThreadContext()->thread;
            }
        }

        [NoHeapAllocation]
        internal static void SetCurrentThreadContext(ref ThreadContext context)
        {
            unsafe {
                fixed (ThreadContext *c = &context) {
                    Isa.SetCurrentThread(ref c->threadRecord);
                }
            }
        }

        ///
        /// <summary>
        ///     Verify if thread currently is running on interrupt stack
        /// </summary>
        ///
        [NoHeapAllocation]
        [Inline]
        internal bool IsOnInterruptStack(Thread currentThread)
        {
            return Isa.IsRunningOnInterruptStack;
        }

        internal bool InInterruptContext
        {
            [NoHeapAllocation]
            get {
                return Isa.InInterruptContext;
            }
        }

        [AccessedByRuntime("defined in halforgc.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.GCFRIEND)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal static extern void SwitchToThreadContext(ref ThreadContext oldContext, ref ThreadContext newContext);

        private class ResumeThreadCallback : Isa.ICallback
        {
            internal override UIntPtr Callback(UIntPtr param)
            {
                unsafe {
                    ThreadContext* newContext = (ThreadContext *) param;

                    // Switch our thread context, synchronizing with the dispatcher as necessary.
                    ProcessorDispatcher.TransferToThreadContext(ref *GetCurrentThreadContext(),
                                                                ref *newContext);

                    // Resume in the new context. Note that this call does not return.
                    newContext->threadRecord.spill.Resume();

                    return 0;
                }
            }
        }

        [AccessedByRuntime("referenced by halforgc.asm")]
        [NoHeapAllocation]
        [GCAnnotation(GCOption.NOGC)]
        internal static unsafe void SwitchToThreadContextNoGC(ref ThreadContext newContext)
        {
            // Interrupts should be disabled at this point
            VTable.Assert(Processor.InterruptsDisabled());

            // Save appears to returns twice: once with true on this thread after
            // the save, and once with false when the context is restored.

            if (GetCurrentThreadContext()->threadRecord.spill.Save()) {
                // Initial return from save; time to swap in the new context.
                // Must do this on the interrupt stack, since once we release the
                // dispatch lock the saved context is free to run (and we would
                // be on the same stack.)
                fixed (ThreadContext *c = &newContext) {
                    // Note that this does not return.
                    Isa.CallbackOnInterruptStack(resumeThreadCallback, (UIntPtr) c);
                }
            }

            // Saved context will resume here
        }

        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal static extern void TestSaveLoad(ref ThreadContext newContext);

        [MethodImpl(MethodImplOptions.InternalCall)]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(32)]
        [NoHeapAllocation]
        internal static extern void TestSave(ref ThreadContext newContext);

        //////////////////////////////////////////////////////////////////////
        //
        // These methods are currently marked external because they are used
        // by device drivers.  We need a tool to verify that device drivers
        // are in fact using them correctly!
        //

        [AccessedByRuntime("accessed by C++")]
        [NoHeapAllocation]
        [GCAnnotation(GCOption.NOGC)]
        public static bool DisableLocalPreemption()
        {
            return DisableInterrupts();
        }

        [AccessedByRuntime("accessed by C++")]
        [NoHeapAllocation]
        [GCAnnotation(GCOption.NOGC)]
        public static void RestoreLocalPreemption(bool enabled)
        {
            RestoreInterrupts(enabled);
        }

        [AccessedByRuntime("accessed by C++")]
        [NoHeapAllocation]
        [GCAnnotation(GCOption.NOGC)]
        public static bool DisableInterrupts()
        {
#if CHECK_DISABLE_INTERRUPTS
            bool wasDisabled = InterruptsDisabled();
#endif
            bool result = Isa.DisableInterrupts();

#if CHECK_DISABLE_INTERRUPTS
            if (result && wasDisabled) {
                DebugStub.Break();
            }
#endif

            return result;
        }

        [AccessedByRuntime("accessed by C++")]
        [NoHeapAllocation]
        [GCAnnotation(GCOption.NOGC)]
        public static void RestoreInterrupts(bool enabled)
        {
            int i = 0;
            try {
#if CHECK_DISABLE_INTERRUPTS
            if (!InterruptsDisabled()) {
                DebugStub.Break();
            }
#endif
            i = 1;
            if (enabled) {
                i = 2;
               // Processor flag should be turned off before this call
               if (GetCurrentProcessor().InInterruptContext) {
                    DebugStub.Break();
               }
               i = 3;
               Isa.EnableInterrupts();
            }
            i = 5;
#if CHECK_DISABLE_INTERRUPTS
            if (enabled && InterruptsDisabled()) {
                DebugStub.Break();
            }
#endif
            }
            catch(Exception e) {
                DebugStub.Break();
            }
        }

        // Use this method for assertions only!
        [AccessedByRuntime("accessed by C++")]
        [NoHeapAllocation]
        [GCAnnotation(GCOption.NOGC)]
        public static bool InterruptsDisabled()
        {
            return Platform.ThePlatform.AreInterruptsDisabled();
        }

        [NoHeapAllocation]
        public unsafe void IncrementInterruptCounts(int interrupt)
        {
            NumInterrupts++;
            NumExceptions++;
            interruptCounts[interrupt]++;

            if (ProcessorLog != null) {
                // ProcessorLog.Log(interrupt);
                processorCounter.Buffer[interrupt].Hits += 1;
            }
        }

        [NoHeapAllocation]
        internal static unsafe void UpdateAfterGC(Thread currentThread)
        {
            // Update the processor pointers in processor contexts
            for (int i = 0; i < Processor.processorTable.Length; i++) {
                Processor p = Processor.processorTable[i];
                if (p != null) {
                    p.context->UpdateAfterGC(p);
                }
            }
            // Ensure that Thread.CurrentThread returns new thread object
            SetCurrentThreadContext(ref currentThread.context);
        }

        [NoHeapAllocation]
        internal void ActivateDispatcher()
        {
             if (Platform.Cpu(processorIndex) != null){

                // Wake processor
                Platform.ThePlatform.WakeNow(processorIndex);
             }
        }

        ///
        /// <summary>
        /// Set next alarm: timer that we are interested in
        /// </summary>
        ///
        /// <param name="delta">Time until the next time we would like to be awaken</param>
        ///
        [NoHeapAllocation]
        public void SetNextTimerInterrupt(TimeSpan delta)
        {
            // Make sure that interrupts are disabled
            bool iflag = Processor.DisableInterrupts();

            TimeSpan start = delta;
            if (delta < timer.MinInterruptInterval) {
                delta = timer.MinInterruptInterval;
            }
            if (delta > timer.MaxInterruptInterval) {
                delta = timer.MaxInterruptInterval;
            }
#if false
            DebugStub.WriteLine("-- SetNextTimerInterrupt(delta={0}, start={1} [min={2},max={3})",
                                __arglist(delta.Ticks,
                                          start.Ticks,
                                          timer.MinInterruptInterval.Ticks,
                                          timer.MaxInterruptInterval.Ticks));
#endif
            timer.SetNextInterrupt(delta);

            // Restore interrupts if necessary
            Processor.RestoreInterrupts(iflag);
        }

        //////////////////////////////////////////////////////////////////////
        //
        // These (native) methods manipulate the local processor's paging
        // hardware. They can be used even before Processor.Initialize()
        // has been called.
        //

        internal static void EnablePaging(AddressSpace bootstrapSpace)
        {
            Isa.EnablePaging((uint)bootstrapSpace.PdptPage.Value);
        }

        internal static void ChangeAddressSpace(AddressSpace space)
        {
            Isa.ChangePageTableRoot((uint)space.PdptPage.Value);
        }

        internal static void InvalidateTLBEntry(UIntPtr pageAddr)
        {
            DebugStub.Assert(MemoryManager.IsPageAligned(pageAddr));
            Isa.InvalidateTLBEntry(pageAddr);
        }

        internal static AddressSpace GetCurrentAddressSpace()
        {
            return new AddressSpace(new PhysicalAddress(Isa.GetPageTableRoot()));
        }

        //
        public static HalMemory.ProcessorAffinity[] GetProcessorAffinity()
        {
            HalMemory.ProcessorAffinity[] processors =
                halMemory.GetProcessorAffinity();
            return processors;
        }

        public static HalMemory.MemoryAffinity[] GetMemoryAffinity()
        {
            HalMemory.MemoryAffinity[] memories =
                halMemory.GetMemoryAffinity();
            return memories;
        }


        public static unsafe void EnableMoreProcessors(int cpus)
        {
            ExpectedProcessors = cpus;
            Platform.ThePlatform.EnableMoreCpus(cpus);
            StartApProcessors(cpus);
        }

        /// <summary> Start application processors. </summary>
        [System.Diagnostics.Conditional("SINGULARITY_MP")]
        public static void StartApProcessors(int cpuCount)
        {
            // At this point only the BSP is running.

            Tracing.Log(Tracing.Debug, "Processor.StartApProcessors()");
            Platform.StartApProcessors(cpuCount);

            // At this point the BSP and APs are running.
        }

        /// <summary> Stop application processors. </summary>
        [NoHeapAllocation]
        [System.Diagnostics.Conditional("SINGULARITY_MP")]
        public static void StopApProcessors()
        {
            //
            // Note: This should go into a HAL interface and this
            //       code confined to Platform.cs
            //

            // At this point the BSP and APs are running.
            Tracing.Log(Tracing.Debug, "Processor.StopApProcessors()");

            if (Processor.GetRunningProcessorCount() > 1) {

                //
                // This stops them in MpExecution in a halt state with
                // interrupts off.
                //
                Platform.BroadcastFixedIPI((byte)Isal.IX.EVectors.HaltApProcessors, true);
            }

            while (GetRunningProcessorCount() != 1) {
                // Thread.Sleep(100); Thread.Sleep needs NoHeapAllocation annotation   
                Thread.Yield();
            }

            //
            // We must reset the AP Processors since a debug entry
            // will generated a NMI which will wake them up from HALT,
            // and they may start executing code again while the kernel
            // is still shutting down.
            //
            Platform.ResetApProcessors();

            DebugStub.RevertToUniprocessor();
            // At this point only the BSP is running.
        }

        /// <summary> Gets the number of processors in use by
        /// the system. </summary>
        [NoHeapAllocation]
        public static int GetRunningProcessorCount()
        {
            return runningCpus;
        }

        /// <summary> Gets the total number of processors known
        /// to the system.  This includes processors not
        /// currently in use by the system. </summary>
        [NoHeapAllocation]
        public static int GetProcessorCount()
        {
            return Platform.GetProcessorCount();
        }

        //
        //public static int GetDomainCount()
        //{
        //  HalMemory.ProcessorAffinity[] processors =
        //      halMemory.GetProcessorAffinity();
        //  uint domain = 0;
        //  for (int i = 0; i < processors.Length; i++) {
        //      if (processors[i].domain > domain) {
        //          domain = processors[i].domain;
        //      }
        //  }
        //  domain++; // domain number starts from 0
        //  return (int)domain;
        //}
        //

        public static bool PerProcessorAddressSpaceDisabled()
        {
            return halMemory.PerProcessorAddressSpaceDisabled();
        }

        public static bool HasAffinityInfo()
        {
            HalMemory.ProcessorAffinity[] processors = halMemory.GetProcessorAffinity();
            HalMemory.MemoryAffinity[] memories = halMemory.GetMemoryAffinity();
            if (processors == null || memories == null) {
                return false;
            }
            return true;
        }

        // return cpuId if context is not null
        [NoHeapAllocation]
        public unsafe int ValidProcessorId(int i)
        {
            if (context != null) {
                return context->cpuRecord.id;
            }
            else {
                return -1;
            }
        }

        ///
        /// <summary>
        ///     Is system MP or UP
        /// </summary>
        ///
        public static bool IsUP
        {
            [NoHeapAllocation]
            get
            {
                return CpuCount == 1;
            }
        }

        ///<summary> Count of the number of processors expected to be running </summary>
        public static int                   ExpectedProcessors;

        ///<summary> Global processor table </summary>
        public static Processor[]           processorTable;

        /// <summary> Processor contexts </summary>
        internal unsafe ProcessorContext*   context;

        ///<summary> Processor dispatcher </summary>
        [AccessedByRuntime("referenced from c++")]
        internal ProcessorDispatcher        dispatcher;

        //<summary> Hardware pic, or its emulation </summary>
        private HalPic                     pic;

        /// <summary> Per processor HalTimer </summary>
        internal HalTimer                  timer = null;

        /// <summary> Per processor HalClock </summary>
        internal HalClock                  clock = null;

        /// <summary> Hal memory interface </summary>
        private static HalMemory           halMemory;

        /// <summary> Id of a timer interrupt </summary>
        internal byte                       timerInterrupt;

        /// <summary> Id of a clock interrupt</summary>
        internal byte                       clockInterrupt;

        /// <summary> Shows if a processor currently in a context of interrupt </summary>
        private bool                        inInterruptContext = false;

        /// <summary> Shows if a processor currently in halt state </summary>
        private bool                        halted = false;

        ///<summary> Processor Index </summary>
        private int                         processorIndex;

        /// <summary> A number of exception occured on this processor </summary>
        public uint                         NumExceptions = 0;

        /// <summary> A number of interrupts occrued on this processor </summary>
        public uint                         NumInterrupts = 0;

        /// <summary> A number of context switches </summary>
        public uint                         NumContextSwitches = 0;

        /// <summary> A interrupt statistics per processor </summary>
        internal int[]                      interruptCounts;

        /// <summary> A number of cycles per second on a given processor </summary>
        private ulong                       cyclesPerSecond;

        /// <summary> A number of active Processors </summary>
        private static int                  runningCpus = 0;

        /// <summary> An initial per processor kernel thread </summary>
        private Thread                      kernelThread;

        /// <summary>Beginning of kernel thread stack </summary>
        private UIntPtr                     kernelStackBegin = 0;

        /// <summary> Limit of kernel thread stack </summary>
        private UIntPtr                     kernelStackLimit = 0;
    }
}
