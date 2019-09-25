//////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// Isa specifies a standard architecture-neutral interface to the target execution
// environment required by Singularity.  Unlike the HAL there is only a single
// Isa available at a time (although the Isa implementation changes on different ISA's.)
//
// Isa defines a basic framework for interrupt handling and dispatching, which is uniform
// across HALs.
//
// The Isa model is:
//
// Each processor has 2 processor-specific records avaiable to it.
//  - The CpuRecord is effectively constant for the processor
//  - The ThreadRecord will be changed by the OS as context switches occur on the processor
//
// Pointers to these structures are stored in an architecture-specific, yet well-known,
// atomic instruction sequence. (Specifically, atomic with respect to processor migration
// occuring during the sequence.)
//
// This sequence is allowed to be parameterized by a runtime constant parameter
// "offset" (one for each processor and thread.)  Values of each offset are
// provided at init time and may not change.  (E.g. on x86 this is an offset from fs:[0].)
//
// The target also abstracts ISA-specific interrupt handling and dispatch logic. Each architecture
// identifies interrupts into one of 3 categories (based on static partitioning of dispatch ids):
//      - Exceptions.  These cause the current context to be saved in the CpuRecord, and
//          are dispatched to the debugger infrastructure.  (Eventually they will be further
//          handled by additional logic, but this is not in place yet.)  Note that exceptions
//          are not currently reentrant.
//      - "Quick" interrupts.  These interrupts are intended to be handled by lightweight kernel
//          logic.  They cannot trigger context switches and thus do not require full context saves.
//      - Normal interrupts.  These cause a context save into the per-thread spill area.  The
//          presumption is that execution may resume on a different thread.
//
// There needs to be some discipline enforced in terms of priority of these interrupts, but
// currently there is none. (The current assumption is that normal/quick interrupts
// are non-reentrant, and exceptions may occur at any time but may not be interrupted.  However
// note that nothing is preventing quick interrupts from interrupting anything but debugging.)
//
// The interrupt dispatching logic also manages stack switches.  The basic model is that only
// normal thread execution occurs on growable stacks. Therefore we maintain only a single
// interrupt stack for all interrupt and exception dispatch - reentrant interrupts simply
// grow that stack.  Note that if we ever overflow the interrupt stack it is a panic situation,
// but this is the case anyway since we cannot allocate during interrupt processing.  Also note
// that this stack is also suitable for executing application-level stack growth code, since
// such code cannot run during interrupt time.

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Diagnostics;
#if SINGULARITY_KERNEL
using Microsoft.Singularity.Hal;
using HalPlatform = Microsoft.Singularity.Hal.Platform;
#endif

#if ISA_IX
using Microsoft.Singularity.Isal.IX;
#elif ISA_ARM
using Microsoft.Singularity.Isal.Arm;
#endif

namespace Microsoft.Singularity.Isal
{
  [NoCCtor]
  [AccessedByRuntime("referenced in c++")]
  [CLSCompliant(false)]
  public class Isa
  {
      [AccessedByRuntime("foo", AllFields=true)]
      public enum Type
      {
          X86,
          X64,
          Arm
      };

#if ISA_IX86
      public const Type Target = Type.X86;
#elif ISA_IX64
      public const Type Target = Type.X64;
#elif ISA_ARM
      public const Type Target = Type.Arm;
#endif

      ////////////////////////////////////////////////////////////////////////
      // Thread-local and cpu-local storage
      //
      // Each ISA sets up an architecure-specific way to access a processor- and thread-specific
      // data segment. To allow flexibility in the implementation of this, the HAL
      // is allowed to parameterize the location where this data is stored (although this
      // offset is interpreted in an ISA-specific way: fs offset on x86, gs offset on
      // x64, etc.)  This parameter is generically referred to as the "offset".
      //
      // Note that for each ISA there is a specific well-known assembly sequence, using
      // this offset, to access the thread and processor records.  (Architecture-neutral code
      // should use the function call interfaces.)
      ////////////////////////////////////////////////////////////////////////

      [AccessedByRuntime("referenced in c++")]
      public static int currentThreadOffset;
      [AccessedByRuntime("referenced in c++")]
      public static int currentCpuOffset;

      [AccessedByRuntime("referenced in c++")]
      [CLSCompliant(false)]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      public static unsafe extern ThreadRecord *GetCurrentThread();

      [AccessedByRuntime("referenced in c++")]
      [CLSCompliant(false)]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      public static unsafe extern CpuRecord *GetCurrentCpu();

#if SINGULARITY_KERNEL
      [AccessedByRuntime("referenced in c++")]
      [CLSCompliant(false)]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      public static unsafe extern void SetCurrentThread(ref ThreadRecord record);
#endif

      ////////////////////////////////////////////////////////////////////////
      // Interrupt stack access
      //
      // This routine allows managed code to be executed on the interrupt stack.
      //
      // This can only be safely accomplished with interrupt disabled.
      // There are two reasons interrupts are required to be disabled here:
      //
      // 1. We must disable interrupts around the narrow window where we are flipping the stack
      //    back and forth from the interrupt stack (essentially this must be atomic or the
      //    interrupt dispatcher could get confused.)
      //
      // 2. We cannot tolerate a context switch when we are on the interrupt stack.
      //
      // If we ever support leveled interrupts, we may want to disable interrupts for a very
      // narrow window, and separately disable scheduling operations for the longer window.
      ////////////////////////////////////////////////////////////////////////

      [AccessedByRuntime("referenced by asm")]
      public abstract class ICallback
      {
          [NoStackLinkCheckTrans]
          internal abstract UIntPtr Callback(UIntPtr param);

          [AccessedByRuntime("referenced by asm")]
          [NoStackLinkCheckTrans]
          private static UIntPtr DoCallback(ICallback  pThis, UIntPtr param)
          {
              VTable.Assert(Isa.IsRunningOnInterruptStack);

              return pThis.Callback(param);
          }
      }

#if SINGULARITY_KERNEL

      [NoStackLinkCheckTrans]
      [NoHeapAllocation]
      public static UIntPtr CallbackOnInterruptStack(ICallback callback, UIntPtr param)
      {
          VTable.Assert(HalPlatform.ThePlatform.AreInterruptsDisabled());

          // Here we assert that we aren't reentering the interrupt stack.  This would technically
          // be just fine (we'd just call back immediately),  but the check is here because:
          // (a) existing clients currently don't expect this to happen, so it's a sanity check
          // (b) we are participating in an annoying hack where we "discard" the NoHeapAllocation
          //     attribute on our callback path through unmanaged code, since stack allocation
          //     calls through here and is not annotated properly.  Thus we can't directly call
          //     the callback here. (@todo: This needs to be fixed.)

          VTable.Assert(!IsRunningOnInterruptStack);

          return SwitchToInterruptStackAndCallback(callback, param);
      }

      [AccessedByRuntime("defined in interrupt.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public extern static UIntPtr SwitchToInterruptStackAndCallback(ICallback callback,
                                                                     UIntPtr param);
#endif // SINGULARITY_KERNEL

      public static bool IsRunningOnInterruptStack
      {
          [NoHeapAllocation]
          get {
              unsafe {
                  return StackLimit == GetCurrentCpu()->interruptStackLimit;
              }
          }
      }

      ////////////////////////////////////////////////////////////////////////
      // Direct register access
      ////////////////////////////////////////////////////////////////////////

      public static UIntPtr StackLimit
      {
          [NoHeapAllocation]
          get {
              unsafe {
                  return GetCurrentThread()->activeStackLimit;
              }
          }
          [NoHeapAllocation]
          set {
              unsafe {
                  GetCurrentThread()->activeStackLimit = value;
              }
          }
      }

#if ISA_ARM

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      public static extern uint GetCpsr();

#endif // ISA_ARM

#if ISA_IX

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      public static extern UIntPtr GetCs();

#endif // ISA_IX

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern void WriteMsr(uint offset,ulong value);

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern ulong ReadMsr(uint offset);

      ////////////////////////////////////////////////////////////////////////
      // Specialized instruction support
      ////////////////////////////////////////////////////////////////////////

#if SINGULARITY_KERNEL

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      public static extern void Halt();

#endif // SINGULARITY_KERNEL


#if ISA_ARM
      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [StackBound(32)]
      [NoHeapAllocation]
      internal static extern void EnableCycleCounter();
#else
      [NoHeapAllocation]
      internal static void EnableCycleCounter()
      {
      }
#endif

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [StackBound(32)]
      [NoHeapAllocation]
      internal static extern ulong GetCycleCount();

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern ulong ReadPmc(uint offset);

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(64)]
      [NoHeapAllocation]
      public static extern void ReadCpuid(uint feature,
                                          out uint v0, out uint v1, out uint v2, out uint v3);

      ////////////////////////////////////////////////////////////////////////
      // Basic FPU support
      ////////////////////////////////////////////////////////////////////////

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(64)]
      [NoHeapAllocation]
      public static extern void InitFpu();

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      private static extern uint ReadFpuStatus();

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      private static extern void ClearFpuStatus();

      ////////////////////////////////////////////////////////////////////////
      // IO space support
      ////////////////////////////////////////////////////////////////////////

#if ISA_IX

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(64)]
      [NoHeapAllocation]
      public static extern int In(ushort port);

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(64)]
      [NoHeapAllocation]
      public static extern void Out(ushort port, int value);

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(64)]
      [NoHeapAllocation]
      public static extern unsafe void RepInS(uint count, ushort port, byte *buffer);

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(64)]
      [NoHeapAllocation]
      public static extern unsafe void RepOutS(uint count, ushort port, byte *buffer);

#endif // ISA_IX

      ////////////////////////////////////////////////////////////////////////
      // Chip-level interrupt enable flag
      ////////////////////////////////////////////////////////////////////////

#if SINGULARITY_KERNEL

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      public static extern bool AreInterruptsDisabled();

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      internal static extern bool DisableInterrupts();

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      internal static extern void EnableInterrupts();

#endif // SINGULARITY_KERNEL

      ////////////////////////////////////////////////////////////////////////
      // Call frame support
      ////////////////////////////////////////////////////////////////////////

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      internal static unsafe extern UIntPtr GetFrameReturnAddress(UIntPtr framePointer);

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      internal static unsafe extern UIntPtr GetFrameCallerFrame(UIntPtr framePointer);

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      internal static extern UIntPtr GetStackPointer();

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      internal static extern UIntPtr GetFramePointer();

      // These methods are public and safe to use from any where provided
      // there's at least 2 call frames on the stack.
      [NoHeapAllocation]
      public static UIntPtr GetCallerReturnAddress()
      {
          UIntPtr currentFrame = GetFramePointer();
          UIntPtr callerFrame = GetFrameCallerFrame(currentFrame);
          if (callerFrame == UIntPtr.Zero) {
              return UIntPtr.Zero;
          }
          UIntPtr callersCaller = GetFrameReturnAddress(callerFrame);
          return callersCaller;
      }

      /// <summary>
      /// Provides a mini stack trace starting from the caller of the caller
      /// of this method.
      /// </summary>
      [NoHeapAllocation]
      public static void GetStackReturnAddresses(out UIntPtr pc1, out UIntPtr pc2, out UIntPtr pc3)
      {
          pc1 = UIntPtr.Zero;
          pc2 = UIntPtr.Zero;
          pc3 = UIntPtr.Zero;

          UIntPtr currentFrame = GetFramePointer();
          UIntPtr callerFrame = GetFrameCallerFrame(currentFrame);
          if (callerFrame == UIntPtr.Zero) {
              return;
          }
          pc1 = GetFrameReturnAddress(callerFrame);
          callerFrame = GetFrameCallerFrame(callerFrame);
          if (callerFrame == UIntPtr.Zero) {
              return;
          }
          pc2 = GetFrameReturnAddress(callerFrame);
          callerFrame = GetFrameCallerFrame(callerFrame);
          if (callerFrame == UIntPtr.Zero) {
              return;
          }
          pc3 = GetFrameReturnAddress(callerFrame);
      }

      /// <summary>
      /// Provides the full stack trace starting from the caller of the caller
      /// of this method.
      /// </summary>
      /// <returns>Return address values in stack array from top to bottom</returns>
      [NoHeapAllocation]
      public static uint GetStackReturnAddresses(UIntPtr[] stack)
      {
          uint index;
          if (stack == null) {
              return 0;
          }
          UIntPtr currentFrame = GetFramePointer();
          UIntPtr callerFrame = GetFrameCallerFrame(currentFrame);
          for (index = 0; callerFrame != UIntPtr.Zero && index < stack.Length; index++) {
              stack[index] = GetFrameReturnAddress(callerFrame);
              callerFrame = GetFrameCallerFrame(callerFrame);
          }
          return index;
      }

      ////////////////////////////////////////////////////////////////////////
      // Execution mode
      ////////////////////////////////////////////////////////////////////////

      [NoHeapAllocation]
      [AccessedByRuntime("foo")]
      internal static bool IsInUserMode()
      {
#if ISA_IX
            // The bottom two bits of the CS selector are the RPL
            // (requested privilege level) of the selector. If
            // this is 3, we're running in ring3. Otherwise,
            // we're more privileged.

            return (GetCs() & 0x3) == 3;
#else
            // We don't currently support non-priveleged mode on other archs.
            return false;
#endif
      }

#if SINGULARITY_KERNEL

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      internal static extern void EnterUserMode();

#endif // SINGULARITY_KERNEL

      ////////////////////////////////////////////////////////////////////////
      // Chip-level paging support
      ////////////////////////////////////////////////////////////////////////

#if SINGULARITY_KERNEL

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern void EnablePaging(uint pdpt);

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern void DisablePaging();

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern void ChangePageTableRoot(uint pdpt);

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern UIntPtr GetPageTableRoot();

      [AccessedByRuntime("foo")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(16)]
      [NoHeapAllocation]
      public static extern void InvalidateTLBEntry(UIntPtr pageAddr);

#endif // SINGULARITY_KERNEL

      ////////////////////////////////////////////////////////////////////////
      // Interrupt dispatch logic
      ////////////////////////////////////////////////////////////////////////

      public static bool InInterruptContext
      {
          [NoHeapAllocation]
          get {
              unsafe {
                  // Note that there is a small window where we haven't switched stacks where this
                  // will return false.  However this is balanced against the complexity of
                  // maintaining a specific flag, especially across context restores operations.

                  // Also note that during normal thread execution there is a small possibility of
                  // getting another CPU's interruptStackLimit due to processor migration, but it
                  // should not affect the result.

                  return StackLimit == GetCurrentCpu()->interruptStackLimit;
              }
          }
      }

#if SINGULARITY_KERNEL

      // This call signature is a lie - in fact this routine has asm-level
      // calling conventions and will never be called by managed code.
      [AccessedByRuntime("defined in interrupt.asm")]
      public extern static void DispatchVector();

      // This type is a lie - in fact this is a code fragment. However
      // C# won't let us take the address of code, so we declare it as a byte.
      [AccessedByRuntime("output to header : defined in context.asm")]
      [ExternalStaticData]
      public unsafe static byte DefaultReturnFromInterrupt;

      // The HAL is also allowed to customize the behavior of the final sequence of resuming
      // a context, since it includes enabling interrupts which is abstracted by the hal.
      // Currently this is specified by an unmanaged code snipped pointer.  This code
      // should have identical semantics to [iretd on x86,x64; tbd otherwise.]
      [AccessedByRuntime("referenced in c++")]
      private unsafe static void *returnFromInterrupt;

      [NoHeapAllocation]
      [AccessedByRuntime("referenced in c++")]
      public static unsafe void SetReturnFromInterruptRoutine(UIntPtr code)
      {
          returnFromInterrupt = (void *) code;
      }

      // DebuggerDispatch dispatches exceptions to the debugger infrastructure.
      // Eventually this should move to the HAL, as different platforms will
      // have different debugging requiremnts

      [NoHeapAllocation]
      private static void DispatchDebugger(ref SpillContext context, int exception)
      {
#if ISA_IX
          // TBD: factor this special case into debugger abstraction
          if (exception == EVectors.Nmi) {

            if (Microsoft.Singularity.MpExecution.FreezeRequested) {

              Singularity.MpExecution.FreezeProcessor(ref context);

            } else {

                DebugStub.WriteLine("******************* NMI Interrupt **********************\n");
                Singularity.DebugStub.Trap(ref context, exception);
            }
          }
          else {
              // TBD: we should factor the debugger support into the HAL.
              Singularity.DebugStub.Trap(ref context, exception);
          }
#elif ISA_ARM
          // Fix up pc for some software exceptions, regardless of debugger attachment.

          if (exception == ExceptionVector.SoftwareInterrupt) {
              // Move pc forward to resume after interrupting instruction.
              if (context.instruction != 0x0efffff01) {
                  // Don't move pc forward for debugger-inserted breakpoints.
                  context.pc += 4;
              }
          }
          else if (exception == ExceptionVector.UndefinedInstruction) {
              // Move pc forward to resume after interrupting instruction.
              context.pc += 4;
          }

          // TBD: we should factor the debugger support into the HAL.
          Singularity.DebugStub.Trap(ref context, exception);
#endif

          context.Resume();
      }

      // InterruptDispatch is called by the asm code after saving the context
      // and switching stacks.  This routine may return, in which case execution
      // is resumed, or it may call RestoreContext on a new thread.

      [AccessedByRuntime("referenced in asm")]
      [NoHeapAllocation]
      public static unsafe void DispatchInterrupt(InterruptContext *context)
      {
#if false
          DebugStub.WriteLine("---------------------------------------------------------------\n");
          DebugStub.WriteLine("DispatchInterrupt (vector={0:x2})", __arglist(context->vector));
          context->Display();
          DebugStub.WriteLine("---------------------------------------------------------------\n");
#endif

          // This count is stored in the Singularity Processor object, since that is where singx86
          // looks for it.  Need to move at some point.
          Singularity.Processor p = Singularity.Processor.CurrentProcessor;
          if (p != null) {
              p.IncrementInterruptCounts(context->ExceptionId);
          }

          if (context->IsException()) {
              // All exceptions get reported to the debugger (as first chance.)
              DispatchDebugger(ref GetCurrentCpu()->spill, context->ExceptionId);

              // TBD: eventually we want to actually have OS logic to do something with
              // hardware exceptions...
          }
          else {
              // Reset context for interrupt code (this affects the fpu)
              // @todo: investigate details here; this seems wrong -SET
              SpillContext.ResetCurrent();

              HalPlatform.CurrentCpu.DispatchInterrupt(context);
          }
      }

#endif // SINGULARITY_KERNEL

      ////////////////////////////////////////////////////////////////////////
      // Initialization
      ////////////////////////////////////////////////////////////////////////

#if SINGULARITY_KERNEL

      [NoHeapAllocation]
      [NoStackOverflowCheck]
      [AccessedByRuntime("referenced in c++")]
      public static void Initialize(int cpuRecordOffset, int threadRecordOffset)
      {
          // Fetch the offsets from the HAL
          currentCpuOffset = cpuRecordOffset;
          currentThreadOffset = threadRecordOffset;

          // Set default return from interrupt routine
          unsafe {
              fixed (byte *p = &DefaultReturnFromInterrupt) {
                  returnFromInterrupt = p;
              }
          }
      }

      [NoHeapAllocation]
      [NoStackOverflowCheck]
      [AccessedByRuntime("referenced in c++")]
      [NoStackLinkCheckTrans]
      public static unsafe void InitializeCpu(CpuRecord *cpu,
                                              int cpuid,
                                              UIntPtr stackLimit)
      {
          unsafe {
              cpu->id = cpuid;

              // Set up active stack limit before we may incurr
              // a linked stack check.
              cpu->bootThread.activeStackLimit = stackLimit;

              // Initially we just use the current stack for interrupts.
              cpu->interruptStackBegin = 0;
              cpu->interruptStackLimit = stackLimit;

              InitializeCurrentCpu(ref *cpu);



              InitializeCurrentThread(ref cpu->bootThread);
          }
      }

      [AccessedByRuntime("referenced in c++")]
      [NoHeapAllocation]
      public static void InitializeDispatchTable()
      {
#if ISA_IX
          InitializeIdt();
#elif ISA_ARM
          // Nothing to do as there is no table, just code.
#endif
      }

      [AccessedByRuntime("referenced in c++")]
      [NoHeapAllocation]
      public static void InitializeCpuDispatchTable()
      {
#if ISA_IX
          LoadIdt();
#elif ISA_ARM
          unsafe {
              UIntPtr sp = GetCurrentCpu()->dispatchStack.StackBegin;

              // Initialize the sp pointers in the various exception modes
              SetModeSp(ProcessorMode.Fiq, sp);
              SetModeSp(ProcessorMode.Irq, sp);
              SetModeSp(ProcessorMode.Supervisor, sp);
              SetModeSp(ProcessorMode.Abort, sp);
              SetModeSp(ProcessorMode.Undefined, sp);
          }
          LoadResetVector();
#endif
      }

      [AccessedByRuntime("referenced in c++")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      private static unsafe extern void InitializeCurrentThread(ref ThreadRecord record);

      [AccessedByRuntime("referenced in c++")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [GCAnnotation(GCOption.NOGC)]
      [StackBound(32)]
      [NoHeapAllocation]
      private static unsafe extern void InitializeCurrentCpu(ref CpuRecord record);

#endif // SINGULARITY_KERNEL

      ////////////////////////////////////////////////////////////////////////
      // Interrupt table
      ////////////////////////////////////////////////////////////////////////

#if SINGULARITY_KERNEL

#if ISA_IX

      [AccessedByRuntime("accessed from asm")]
      // BUG: declare this ExternalStaticData since it is not properly aligned by bartok
      [ExternalStaticData]
      public static InterruptTable idt;

      [AccessedByRuntime("called from C++")]
      [NoHeapAllocation]
      public static void InitializeIdt()
      {
          idt.Initialize();
      }

      [AccessedByRuntime("defined in interrupt.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      public static extern void LoadIdt();

#endif

#if ISA_ARM

      [AccessedByRuntime("defined in isa.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      public static extern void SetModeSp(int mode, UIntPtr sp);

      [AccessedByRuntime("defined in interrupt.asm")]
      [MethodImpl(MethodImplOptions.InternalCall)]
      [NoHeapAllocation]
      [StackBound(32)]
      public static extern void LoadResetVector();

#endif // ISARM

#endif // SINGULARITY_KERNEL

  }
}
