////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DeviceService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity.V1.Services
{
    [CLSCompliant(false)]
    public struct DeviceService
    {
        [ExternalEntryPoint]
        public static unsafe uint GetPnpSignature(int index, /*[out]*/ char * output, uint maxout)
        {
            IoConfig config = Thread.CurrentProcess.IoConfig;

            Tracing.Log(Tracing.Debug, "DeviceService.GetPnpSignature({0:x8}, {1})",
                        (UIntPtr)output, maxout);
            if (config == null || config.Ids == null || config.Ids.Length == 0) {
                return 0;
            }

            if (index < 0)
                return 0;
            if (index >= config.Ids.Length)
                return 0;
            string id = config.Ids[index];

            Tracing.Log(Tracing.Debug, "  {0}", config.ToString());
            if (output == null) {
                return (uint)id.Length + 1;
            }
            return (uint)id.InternalGetChars(output, (int)maxout);
        }

        [ExternalEntryPoint]
        public static unsafe bool GetPciPort(
            out PciPortHandle pciPortHandle
            )
        {
            return PciPortHandle.Create(out pciPortHandle);
        }

        [ExternalEntryPoint]
        public static uint GetDynamicIoRangeCount()
        {
            uint ret = 0;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null) {
                ret = (uint)config.DynamicRanges.Length;
            }

            Tracing.Log(Tracing.Debug, "DeviceService.GetDynamicIoRangeCount() = {0}", ret);
            Tracing.Log(Tracing.Debug, "  {0}", config.ToString());
            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetDynamicIoPortRangeImpl(
            uint range,
            ushort * port,
            ushort * size,
            bool * readable,
            bool * writable)
        {
            return GetDynamicIoPortRange(range, out *port, out *size,
                out *readable, out *writable);
        }

        public static bool GetDynamicIoPortRange(uint range,
                                                 out ushort port,
                                                 out ushort size,
                                                 out bool readable,
                                                 out bool writable)
        {
            bool ret = false;

            port = 0;
            size = 0;
            readable = false;
            writable = false;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.DynamicRanges.Length > range) {
                IoPortRange ipr = config.DynamicRanges[range] as IoPortRange;
                if (ipr != null) {
                    port = ipr.Port;
                    size = ipr.Size;
                    readable = ipr.Readable;
                    writable = ipr.Writable;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetDynamicIoPortRange(range={0}, out port={1:x4}, out size={2})",
                        range, port, size);

            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetDynamicIoMemoryRangeImpl(
            uint range,
            byte * * data,
            uint * size,
            bool * readable,
            bool * writable)
        {
            return GetDynamicIoMemoryRange(range, out *data, out *size,
                out *readable, out *writable);
        }

        public static unsafe bool GetDynamicIoMemoryRange(uint range,
                                                          out byte * data,
                                                          out uint size,
                                                          out bool readable,
                                                          out bool writable)
        {
            bool ret = false;

            data = null;
            size = 0;
            readable = false;
            writable = false;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.DynamicRanges.Length > range) {
                IoMemoryRange imr = config.DynamicRanges[range] as IoMemoryRange;
                if (imr != null) {
                    data = (byte *)imr.PhysicalAddress.Value;
                    size = (uint)imr.Length;
                    readable = imr.Readable;
                    writable = imr.Writable;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetDynamicIoMemoryRange(range={0}, out data={1:x8}, out size={2})",
                        range, (UIntPtr)data, size);

            return ret;
        }

        [ExternalEntryPoint]
        public static int GetIrqCount(byte irq)
        {
            int count = Processor.CurrentProcessor.GetIrqCount(irq);
            Tracing.Log(Tracing.Debug,
                "DeviceService.GetIrqCount(irq={0:x}, count={1:x8})",(UIntPtr) irq, (UIntPtr) count);
            return count;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetDynamicIoIrqRangeImpl(
            uint range,
            byte * line,
            byte * size)
        {
            return GetDynamicIoIrqRange(range, out *line, out *size);
        }

        public static bool GetDynamicIoIrqRange(uint range,
                                                out byte line,
                                                out byte size)
        {
            bool ret = false;

            line = 0;
            size = 0;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.DynamicRanges.Length > range) {
                IoIrqRange iir = config.DynamicRanges[range] as IoIrqRange;
                if (iir != null) {
                    line = iir.Line;
                    size = iir.Size;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetDynamicIoIrqRange(range={0}, out line={1:x2}, out size={2:x2})",
                        range, line, size);

            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetDynamicIoDmaRangeImpl(
            uint range,
            byte * channel,
            byte * size)
        {
            return GetDynamicIoDmaRange(range, out *channel, out *size);
        }

        public static bool GetDynamicIoDmaRange(uint range,
                                                out byte channel,
                                                out byte size)
        {
            bool ret = false;

            channel = 0;
            size = 0;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.DynamicRanges.Length > range) {
                IoDmaRange idr = config.DynamicRanges[range] as IoDmaRange;
                if (idr != null) {
                    channel = idr.Channel;
                    size = idr.Size;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetDynamicIoDmaRange(range={0}, out channel={1:x2}, out size={2:x2})",
                        range, channel, size);

            return ret;
        }


        [ExternalEntryPoint]
        public static uint GetFixedIoRangeCount()
        {
            uint ret = 0;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null) {
                if (config.FixedRanges != null) {
                    ret = (uint)config.FixedRanges.Length;
                }
            }

            Tracing.Log(Tracing.Debug, "DeviceService.GetFixedIoRangeCount() = {0}", ret);
            Tracing.Log(Tracing.Debug, "  {0}", config.ToString());
            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetFixedIoPortRangeImpl(
            uint range,
            ushort * port,
            ushort * size,
            bool * readable,
            bool * writable)
        {
            return GetFixedIoPortRange(range, out *port, out *size,
                out *readable, out *writable);
        }

        public static bool GetFixedIoPortRange(uint range,
                                               out ushort port,
                                               out ushort size,
                                               out bool readable,
                                               out bool writable)
        {
            bool ret = false;

            port = 0;
            size = 0;
            readable = false;
            writable = false;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.FixedRanges.Length > range) {
                IoPortRange ipr = config.FixedRanges[range] as IoPortRange;
                if (ipr != null) {
                    port = ipr.Port;
                    size = ipr.Size;
                    readable = ipr.Readable;
                    writable = ipr.Writable;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetFixedIoPortRange(range={0}, out port={1:x4}, out size={2})",
                        range, port, size);

            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetFixedIoMemoryRangeImpl(
            uint range,
            byte * * data,
            uint * size,
            bool * readable,
            bool * writable)
        {
            return GetFixedIoMemoryRange(range, out *data, out *size,
                out *readable, out *writable);
        }

        public static unsafe bool GetFixedIoMemoryRange(uint range,
                                                        out byte * data,
                                                        out uint size,
                                                        out bool readable,
                                                        out bool writable)
        {
            bool ret = false;

            data = null;
            size = 0;
            readable = false;
            writable = false;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.FixedRanges.Length > range) {
                IoMemoryRange imr = config.FixedRanges[range] as IoMemoryRange;
                if (imr != null) {
                    data = (byte *)imr.PhysicalAddress.Value;
                    DebugStub.Assert(data != null);
                    size = (uint)imr.Length;
                    readable = imr.Readable;
                    writable = imr.Writable;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetFixedIoMemoryRange(range={0}, out data={1:x8}, out size={2})",
                        range, (UIntPtr)data, size);

            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetFixedIoIrqRangeImpl(
            uint range,
            byte * line,
            byte * size)
        {
            return GetFixedIoIrqRange(range, out *line, out *size);
        }

        public static bool GetFixedIoIrqRange(uint range,
                                              out byte line,
                                              out byte size)
        {
            bool ret = false;

            line = 0;
            size = 0;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.FixedRanges.Length > range) {
                IoIrqRange iir = config.FixedRanges[range] as IoIrqRange;
                if (iir != null) {
                    line = iir.Line;
                    size = iir.Size;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetFixedIoIrqRange(range={0}, out line={1:x2}, out size={2:x2})",
                        range, line, size);

            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool GetFixedIoDmaRangeImpl(
            uint range,
            byte * channel,
            byte * size)
        {
            return GetFixedIoDmaRange(range, out *channel, out *size);
        }

        public static bool GetFixedIoDmaRange(uint range,
                                              out byte channel,
                                              out byte size)
        {
            bool ret = false;

            channel = 0;
            size = 0;

            IoConfig config = Thread.CurrentProcess.IoConfig;
            if (config != null && config.FixedRanges.Length > range) {
                IoDmaRange idr = config.FixedRanges[range] as IoDmaRange;
                if (idr != null) {
                    channel = idr.Channel;
                    size = idr.Size;
                    ret = true;
                }
            }

            Tracing.Log(Tracing.Debug,
                        "DeviceService.GetFixedIoDmaRange(range={0}, out channel={1:x2}, out size={2:x2})",
                        range, channel, size);

            return ret;
        }

        [ExternalEntryPoint]
        public static UIntPtr MapPhysicalRange(UIntPtr physStart,
                                               UIntPtr numBytes,
                                               bool readable,
                                               bool writable)
        {
            return MemoryManager.UserMapPhysicalMemory(
                new PhysicalAddress(physStart), numBytes
                );
        }

        [ExternalEntryPoint]
        public static void UnmapPhysicalRange(UIntPtr startAddr,
                                              UIntPtr limitAddr)
        {
            MemoryManager.UserUnmapPhysicalMemory(startAddr, limitAddr);
        }

        // Resolve a 32-bit virtual address (virtualAddr) to a
        // 32-bit physical address (physAddr).  If the lookup
        // succeeds, return true, and set physRemaining to be
        // the number of bytes on physAddr's physical page whose
        // address is greater than or equal to physAddr.  For
        // example, if physAddr is the very last address on the
        // page, physRemaining will be 1.  TODO: if needed, add
        // some notion of pinned memory
        [ExternalEntryPoint]
        public static unsafe bool GetDmaPhysicalAddressImpl(
            UIntPtr virtualAddr,
            UIntPtr * physAddr,
            UIntPtr * physRemaining)
        {
            return GetDmaPhysicalAddress(virtualAddr,
                                         out *physAddr,
                                         out *physRemaining);
        }

        private static bool GetDmaPhysicalAddress(UIntPtr     virtualAddr,
                                                  out UIntPtr physAddr,
                                                  out UIntPtr physRemaining)
        {
            UIntPtr alignedAddr = MemoryManager.PageAlign(virtualAddr);
#if PAGING
            PhysicalAddress phys = VMManager.GetPageMapping(alignedAddr);
            if (phys != PhysicalAddress.Null) {
                physAddr = (UIntPtr)phys.Value + (virtualAddr - alignedAddr);
                physRemaining = MemoryManager.PagePad(physAddr + 1) - physAddr;
                return true;
            }
#else
            if (virtualAddr != UIntPtr.Zero) {
                physAddr      = virtualAddr;
                physRemaining = MemoryManager.PagePad(physAddr + 1) - physAddr;
                return true;
            }
#endif // PAGING
            physAddr      = UIntPtr.Zero;
            physRemaining = UIntPtr.Zero;
            return false;
        }
    }
}
