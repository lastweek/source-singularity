///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoIrq.cs
//

//#define DEBUG_DISPATCH_IO

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity.Hal;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class IoIrq
    {
        private readonly byte irq;
        private InterruptAwareAutoResetEvent! signal;
        private IoIrq next;
        private bool registered;

        //////////////////////////////////////////////////////////////////////
        //
        //
        private const int MaxInterrupts = 256;
        private static IoIrq[]! irqTable;
        private static SpinLock regLock;

        static IoIrq()
        {
            irqTable = new IoIrq [MaxInterrupts];
            regLock = new SpinLock(SpinLock.Types.IoIrq);
        }

        [NoHeapAllocation]
        private static bool AcquireLock()
        {
            bool enabled = Processor.DisableInterrupts();
#if SINGULARITY_MP
            regLock.Acquire();
#endif // SINGULARITY_MP
            return enabled;
        }

        [NoHeapAllocation]
        private static void ReleaseLock(bool enabled)
        {
#if SINGULARITY_MP
            regLock.Release();
#endif // SINGULARITY_MP
            Processor.RestoreInterrupts(enabled);
        }

        // This doesn't need a lock because Register and Release
        // insure that the list is *always* valid (even when being updated).
        [NoHeapAllocation]
        public static void SignalInterrupt(byte irq)
        {
#if DEBUG_DISPATCH_IO
            DebugStub.WriteLine("++ SetInterruptEvent: Irq={0:x2}", __arglist(irq));
#endif
            for (IoIrq step = irqTable[irq]; step != null; step = step.next) {
                step.signal.InterruptAwareSet();
            }
        }

        public IoIrq(byte irq)
        {
            this.irq = irq;
            this.next = null;
            this.signal = new InterruptAwareAutoResetEvent(false);
            this.registered = false;
        }

        public byte Irq
        {
            [NoHeapAllocation]
            get { return irq; }
        }

        // Insert the IoIrq into the linked list for this irq.
        // If it is the first entry, then notify HAL to enable its irq.
        // Returns true if this IoIrq caused the irq to be enabled.
        public bool RegisterInterrupt()
        {
            bool enabled = AcquireLock();
            try {
                Tracing.Log(Tracing.Debug, "Register Irq={0:x2}", irq);
#if DEBUG_DISPATCH_IO
                DebugStub.WriteLine("++ Register Irq={0:x2}", __arglist(irq));
#endif

                this.next = irqTable[irq];
                irqTable[irq] = this;

                this.registered = true;

                if (next == null) {
                    Platform.EnableIoInterrupt(irq);
                    return true;
                }
            }
            finally {
                ReleaseLock(enabled);
            }
            return false;
        }

        // Remove the IoIrq into the linked list for this irq.
        // If it is the last entry, then notify HAL to disable its irq.
        // Returns true if this IoIrq caused the irq to be disabled.
        public bool ReleaseInterrupt()
        {
            bool enabled = AcquireLock();
            try {

                Tracing.Log(Tracing.Debug, "Release Irq={0:x2}", irq);
#if DEBUG_DISPATCH_IO
                DebugStub.WriteLine("++ Release Irq={0:x2}", __arglist(irq));
#endif

                if (irqTable[irq] == this) {
                    irqTable[irq] = this.next;
                }
                else {
                    IoIrq! prev = (!)irqTable[irq];
                    while (prev.next != this) {
                        prev = prev.next;
                    }
                    prev.next = this.next;
                }

                this.next = null;
                this.registered = false;

                if (irqTable[irq] == null) {
                    Platform.DisableIoInterrupt(irq);
                    return true;
                }
            }
            finally {
                ReleaseLock(enabled);
            }
            return true;
        }

        public bool WaitForInterrupt()
        {
            DebugStub.Assert(this.registered);

            if (signal != null) {
                signal.InterruptAwareWaitOne();
                return true;
            }
            return false;
        }

        public void Pulse()
        {
            signal.InterruptAwareSet();
        }

        public bool AckInterrupt()
        {
#if DEBUG_DISPATCH_IO
            DebugStub.WriteLine("++ AckInterrupt: Irq={0:x2}", __arglist(irq));
#endif
            Platform.EnableIoInterrupt(irq);
            return true;
        }

        public override string! ToString()
        {
            return String.Format("IRQ:{0,2:x2}", irq);
        }
    }
}
