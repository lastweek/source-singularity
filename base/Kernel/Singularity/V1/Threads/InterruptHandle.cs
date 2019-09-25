////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   InterruptHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.V1.Threads
{
    [CLSCompliant(false)]
    public struct InterruptHandle // : public SyncHandle
    {

        public readonly UIntPtr id; // could be moved to SyncHandle
        public static readonly InterruptHandle Zero = new InterruptHandle();

        internal InterruptHandle(UIntPtr id)
        {
            this.id = id;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(
            byte irqNum,
            InterruptHandle* handle)
        {
            return Create(irqNum, out *handle);
        }

        public static bool Create(byte irqNum,
                                  out InterruptHandle handle)
        {
            bool ret = false;
            handle = new InterruptHandle();

            //
            // Create an IoIrq, and a handle in the current process to hold it.
            //
            IoConfig config = Thread.CurrentProcess.IoConfig;
            for (int i = 0; i < config.DynamicRanges.Length; i++) {
                IoIrqRange iir = config.DynamicRanges[i] as IoIrqRange;
                if (iir != null && iir.Irq <= irqNum && irqNum < iir.Irq + iir.Size) {
                    IoIrq irq = iir.IrqAtOffset((byte)(irqNum - iir.Irq));

                    handle = new InterruptHandle(
                        Thread.CurrentProcess.AllocateHandle(irq));
                    irq.RegisterInterrupt();
                    ret = true;
                    break;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "InterruptHandle.Create(irq={0:x2}, out id={0:x8})",
                        irqNum, handle.id);
            return ret;
        }

        [ExternalEntryPoint]
        public static bool Dispose(InterruptHandle handle)
        {
            Tracing.Log(Tracing.Debug, "InterruptHandle.Dispose(id={0:x8})",
                        handle.id);

            bool ret = false;
            if (handle.id != UIntPtr.Zero) {
                //
                // Releasing the handle will allow the IoIrq event to be
                // garbage-collected.
                //
                IoIrq irq = HandleTable.GetHandle(handle.id) as IoIrq;
                ret = irq.ReleaseInterrupt();
                Thread.CurrentProcess.ReleaseHandle(handle.id);
            }
            return ret;
        }

        [ExternalEntryPoint]
        public static bool Wait(InterruptHandle handle)
        {
            if (handle.id == UIntPtr.Zero) {
                Tracing.Log(Tracing.Error,
                            "InterruptHandle.Wait(id={0:x8}) on bad handle",
                            handle.id);
                return false;
            }

            //
            // Convert the handle to a IoIrq and wait on it.
            //
            IoIrq irq = HandleTable.GetHandle(handle.id) as IoIrq;
            bool ret = irq.WaitForInterrupt();

            Tracing.Log(Tracing.Debug, "InterruptHandle.Wait(id={0:x8})", handle.id);

            return ret;
        }

        [ExternalEntryPoint]
        public static void Pulse(InterruptHandle handle)
        {
            if (handle.id == UIntPtr.Zero) {
                Tracing.Log(Tracing.Error,
                            "InterruptHandle.Wait(id={0:x8}) on bad handle",
                            handle.id);
                return;
            }
            IoIrq irq = HandleTable.GetHandle(handle.id) as IoIrq;
            irq.Pulse();
            Tracing.Log(Tracing.Debug, "InterruptHandle.Pulse(id={0:x8})",
                        handle.id);
        }

        [ExternalEntryPoint]
        public static bool Ack(InterruptHandle handle)
        {
            if (handle.id == UIntPtr.Zero) {
                Tracing.Log(Tracing.Error,
                            "InterruptHandle.Ack(id={0:x8}) on bad handle",
                            handle.id);
                return false;
            }

            //
            // Convert the handle to an auto-reset event; set the event.
            //
            IoIrq irq = HandleTable.GetHandle(handle.id) as IoIrq;
            bool ret = irq.AckInterrupt();

            Tracing.Log(Tracing.Debug, "InterruptHandle.Ack(id={0:x8})", handle.id);
            return ret;
        }

    }
}
