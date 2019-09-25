///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note: Process Code
//

using System;
using System.Threading;

using Microsoft.Singularity.V1.Threads;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class IoIrq : IoRange
    {
        private readonly byte irq;
        private InterruptHandle handle;

        internal IoIrq(byte irq)
        {
            this.irq = irq;
        }

        ~IoIrq()
        {
            if (handle.id != UIntPtr.Zero) {
                ReleaseInterrupt();
            }
        }

        public byte Irq
        {
            get { return irq; }
        }

        public bool RegisterInterrupt()
        {
            InterruptHandle handleOnStack;
            bool success = InterruptHandle.Create(irq, out handleOnStack);
            handle = handleOnStack;
            return success;
        }

        public bool ReleaseInterrupt()
        {
            bool ret = InterruptHandle.Dispose(handle);
            handle = new InterruptHandle();
            return ret;
        }

        public bool WaitForInterrupt()
        {
            if (handle.id != UIntPtr.Zero) {
                return InterruptHandle.Wait(handle);
            }
            return false;
        }

        public void Pulse()
        {
            if (handle.id != UIntPtr.Zero) {
                InterruptHandle.Pulse(handle);
            }
        }

        public bool AckInterrupt()
        {
            if (handle.id != UIntPtr.Zero) {
                return InterruptHandle.Ack(handle);
            }
            return false;
        }

        public override string ToString()
        {
            return String.Format("IRQ:{0,2:x2}", irq);
        }
    }
}
