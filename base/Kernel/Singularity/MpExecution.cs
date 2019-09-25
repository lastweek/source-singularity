///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MpExecution.cs
//
//  Note:
//          The purpose of this class is to control the execution state of
//  processors on MP systems.  Specifically, to stop processors running
//  while the debugger is active and while a GC is running.
//
//  NB These functions may be called with the debugger
//  communications lock held.  Any calls to DebugStub.Print or
//  its ilk will cause processor to spin on lock forever.

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity
{
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halkd.cpp")]
    public class MpExecution
    {
        // Enumeration of Processor states
        const int Uninitialized = 0x00;   // Processor state uninitialized
        const int Running       = 0x01;   // Processor running normally
        const int TargetFrozen  = 0x02;   // Processor should stop
        const int TargetThaw    = 0x04;   // Processor should continue
        const int FreezeActive  = 0x08;   // Processor is active during freeze
        const int FreezeOwner   = 0x10;   // Processor initiating freeze

        static internal volatile bool FreezeRequested;

        static SpinLock                 freezeLock;
        static volatile int             freezeCount;
        static unsafe ProcessorContext* activeCpuContext;
        static unsafe ProcessorContext* ownerCpuContext;

        [ NoHeapAllocation ]
        static internal unsafe void AddProcessorContext(ProcessorContext* context)
        {
            // Add processor to list of processors in MP system.  Careful
            // to avoid adding processor mid-freeze or without lock.
          start:
            freezeLock.Acquire();
            try {
                if (FreezeRequested)
                    goto start;
                ProcessorContext* head = Processor.processorTable[0].context;

                context->nextProcessorContext = head->nextProcessorContext;
                head->nextProcessorContext = context;
                context->ipiFreeze = Running;
                // From this point on the processor is visible
                // in the debugger
                DebugStub.AddProcessor(context->cpuRecord.id);
            }
            finally {
                freezeLock.Release();
            }
        }
#if NOP
        [ AccessedByRuntime("referenced from halkd.cpp") ]
        [ NoHeapAllocation ]
        static internal unsafe void FreezeAllProcessors()
        {
            freezeLock.Acquire();
            try {
                freezeCount++;
                if (FreezeRequested == true) {
                    // Processors are already frozen
                    return;
                }

                ownerCpuContext  = Processor.GetCurrentProcessorContext();
                activeCpuContext = ownerCpuContext;
                if (activeCpuContext->displacedProcessorContext->nextProcessorContext == activeCpuContext) {
                    return;
                }
                FreezeRequested = true;

                activeCpuContext->displacedProcessorContext->ipiFreeze = FreezeActive | FreezeOwner;
//TODOMP                Platform.FreezeProcessors();

                // Wait until all running processors have gone into freeze
                ProcessorContext* context = activeCpuContext->displacedProcessorContext->nextProcessorContext;
                do
                {
                    if ((context->displacedProcessorContext->ipiFreeze & (TargetFrozen | FreezeActive)) != 0) {
                        context = context->displacedProcessorContext->nextProcessorContext;
                    }
                } while (context->displacedProcessorContext->nextProcessorContext != activeCpuContext);
            }
            finally {
                freezeLock.Release();
            }
        }
#else

        [ AccessedByRuntime("referenced from halkd.cpp") ]
        [ NoHeapAllocation ]
        [ Conditional("SINGULARITY_MP") ]
        static internal unsafe void FreezeAllProcessors()
        {
            // This method is only called on MP systems when the
            // number of running processors is greater than 1.
            freezeLock.Acquire();
            try {
                freezeCount++;
                if (FreezeRequested == true) {
                    // Processors are already frozen
                    return;
                }

                ownerCpuContext  = Processor.GetCurrentProcessorContext();
                activeCpuContext = ownerCpuContext;
                if (activeCpuContext->nextProcessorContext == activeCpuContext) {
                    return;
                }
                FreezeRequested = true;

                activeCpuContext->ipiFreeze = FreezeActive | FreezeOwner;
                // Generate an NMI on all processors (except this one)
                Platform.ThePlatform.FreezeAllCpus();

                // Wait until all running processors have gone into freeze
                ProcessorContext* context = activeCpuContext->nextProcessorContext;
                do
                {
                    if ((context->ipiFreeze & (TargetFrozen | FreezeActive)) != 0) {
                        context = context->nextProcessorContext;
                    }
                } while (context != activeCpuContext);
            }
            finally {
                freezeLock.Release();
            }
        }
#endif

        [ NoHeapAllocation ]
        static internal unsafe void
        FreezeProcessor(ref SpillContext threadContext)
        {
            ProcessorContext* context = Processor.GetCurrentProcessorContext();

            if (context->ipiFreeze == Uninitialized) {
                // Processor was still being initialized when IPI issued
                while (FreezeRequested == true)
                    ; // just spin until thaw occurs
                return;
            }

            context->ipiFreeze = TargetFrozen;

            while (context->ipiFreeze != TargetThaw && FreezeRequested) {
                if ((context->ipiFreeze & FreezeActive) == FreezeActive) {
                    //
                    // This processor has been made the active processor
                    //
                    activeCpuContext = context;

                    // Pass state over to debugger stub
                    if (DebugStub.TrapForProcessorSwitch(ref threadContext)) {
                        // We're returning to Freeze owner, make it active
                        context->ipiFreeze         &= ~FreezeActive;
                        ownerCpuContext->ipiFreeze |= FreezeActive;
                    }
                }
            }

            context->ipiFreeze = Running;
        }

        // Return true maps to ContinueNextProcessor
        // Return false maps to ContinueProcessorReselected
        [ AccessedByRuntime("referenced from halkd.cpp") ]
        [ NoHeapAllocation ]
        static internal unsafe bool SwitchFrozenProcessor(int cpuId)
        {
            ProcessorContext* currentContext = Processor.GetCurrentProcessorContext();
            if (currentContext->cpuRecord.id == cpuId) {
                // No processor to switch to.
                return false;
            }

            ProcessorContext* context = currentContext->nextProcessorContext;
            do
            {
                if (context->cpuRecord.id == cpuId) {
                    currentContext->ipiFreeze &= ~FreezeActive;
                    context->ipiFreeze |= FreezeActive;
                    goto WaitForWakeupOrReselection;
                }
                context = context->nextProcessorContext;
            } while (context != activeCpuContext);

            // cpuId not found so no processor to switch to.
            return false;

          WaitForWakeupOrReselection:
            // If this processor is in the frozen state already, return
            // (it'll fall back into FreezeProcessor() loop). NB Initiating
            // processor can never be in this state.
            if (currentContext->ipiFreeze == TargetFrozen) {
                return true;
            }

            // This processor is the freeze owner, wait to be
            // reselected as the active processor.
            while ((currentContext->ipiFreeze & FreezeActive) != FreezeActive)
                ;

            return false;
        }

        [ AccessedByRuntime("referenced from halkd.cpp") ]
        [ NoHeapAllocation ]
        [ Conditional("SINGULARITY_MP") ]
        static internal unsafe void ThawAllProcessors()
        {
            // This method is only called on MP systems when the
            // number of running processors is greater than 1.
            freezeLock.Acquire();
            try {
                if (FreezeRequested == false) {
                    return;
                }

                freezeCount--;
                if (freezeCount != 0) {
                    return;
                }

                FreezeRequested = false;

                ProcessorContext* context = activeCpuContext;
                do
                {
                    context->ipiFreeze = TargetThaw;
                    context = context->nextProcessorContext;
                } while (context != activeCpuContext);
            }
            finally {
                freezeLock.Release();
            }
        }


         /////////////////////////////////////////////////////////////
        // Initialization function

        internal static void Initialize()
        {
            freezeLock = new SpinLock(SpinLock.Types.MpExecutionFreeze);
        }

        //
        // This is called for a StopTheWorldCollector to ensure CPU's
        // other than the one performing the GC do not service interrupts
        // that can corrupt the heap.
        //
        [NoHeapAllocation]
        static internal unsafe void StopProcessorsForGC()
        {
            ProcessorContext* current = Processor.GetCurrentProcessorContext();

            // Set gcIpiGate to 0 for all processors
            ProcessorContext* context = current;
            do {
                context->gcIpiGate = 0;

                context = context->nextProcessorContext;

            } while (context != current);

            //
            // We don't want to send a broadcast to all but self on a single
            // processor system since the call will fail with no receivers.
            //
            // Note we may have other processors that have not been enabled
            // by the OS and are sitting in SIPI, and won't answer the IPI.
            //
            if (Processor.GetRunningProcessorCount() > 1) {
                Platform.BroadcastFixedIPI((byte)Isal.IX.EVectors.GCSynchronization, false);
            }

            // Wait for ackknowledgement from all CPU's but self
            context = current->nextProcessorContext;

            //DebugStub.WriteLine("StopProcessorsForGC: GC CPU (sender) is {0}\n",
                                //__arglist(current->cpuId));

            while (context != current) {

                //DebugStub.WriteLine("StopProcessorsForGC: Waiting for CPU {0}\n",
                      //__arglist(context->cpuId));

                while (context->gcIpiGate == 0) ;

                //DebugStub.WriteLine("StopProcessorsForGC: CPU {0} Acknowledged\n",
                      //__arglist(context->cpuId));

                context = context->nextProcessorContext;
            }

            return;
        }

        //
        // Called by the StopTheWorldCollector to allow processors
        // to re-enable their interrupts
        //
        [ NoHeapAllocation ]
        static internal unsafe void ResumeProcessorsAfterGC()
        {
            // clear the GC wait flag for each CPU
            ProcessorContext* current = Processor.GetCurrentProcessorContext();

            ProcessorContext* context = current;
            do {
                context->gcIpiGate = 0;

                context = context->nextProcessorContext;

            } while (context != current);

            //DebugStub.WriteLine("ResumeProcessorsAfterGC: All processors resumed\n");

            return;
        }

        //
        // This interrupt occurs when the processor executing the elected
        // GC thread requires all the other processors to stop touching the
        // heap.
        //
        // The GC has ensured that no threads are running through the GC thread
        // synchronization, but interrupts may still occur and enter managed
        // code, and this must be stopped to prevent corruptions on the heap
        // for non-concurrent collectors.
        //
        // The processor with the elected GC thread has already masked off its
        // interrupts and is waiting for the non-GC processors to report
        // that their interrupts are disabled.
        //
        [NoHeapAllocation]
        static internal unsafe void GCSynchronizationInterrupt()
        {
            // - member barriers and other issues with spinwaiting on a variable

            bool en = Processor.DisableInterrupts();

            //DebugStub.WriteLine("Processor {0} received GCSynchronizationInterrupt!\n",
                                 //__arglist(Processor.GetCurrentProcessorId()));


            ProcessorContext* current = Processor.GetCurrentProcessorContext();

            // Write value for this processor stating we ackknowledge the interrupt
            current->gcIpiGate = 1;

            // Question: Are we at a GC safe point? For all GC's?

            //
            // Spinwait until the GC processor indicates its done by clearing
            // this flag.
            //

            while (current->gcIpiGate != 0) {
                //
            }

            Processor.RestoreInterrupts(en);

            //DebugStub.WriteLine("Processor {0} done with GCSynchronizationInterrupt!\n",
                                 //__arglist(Processor.GetCurrentProcessorId()));

            return;
        }

        // Test ..
        internal static void Test()
        {

        }
   }
}
