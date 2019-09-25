///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoConfig.cs
//

using System;
using StringBuilder = System.Text.StringBuilder;
using ArrayList = System.Collections.ArrayList;

#if SINGULARITY_PROCESS
using Microsoft.Singularity;
using Microsoft.Singularity.V1.Services;
#endif // SINGULARITY_PROCESS

namespace Microsoft.Singularity.Io
{
    /// <summary>
    /// Instances of this class represent a set of I/O resources that have been assigned
    /// to a specific device driver instance.
    /// </summary>
    [CLSCompliant(false)]
    public abstract class IoConfig
    {
        /// <summary>
        /// Contains the list of device IDs for this device.  These IDs are created (assigned)
        /// by the bus driver that enumerated this device.  The bus driver may assign any
        /// number of IDs.  The first ID should always be the Singularity-compatible ID,
        /// which uses a path-like syntax, e.g. /pnp/PNP0303 for devices enumerated by the
        /// PNP BIOS / ISAPNP bus device, or /pci/02/00/8086/... for devices enumerated by
        /// the PCI bus enumerator.
        /// </summary>

        public String[] Ids;
        public IoRange[]    DynamicRanges;
        public IoRange[]    FixedRanges;

        /// <summary>
        /// This property exists for compatibility with drivers that assume a single device ID.
        /// It returns the first device ID in the list.
        /// </summary>
        // [Obsolete("Fix code to use Ids (list of ids)")]
        public String Id
        {
            get
            {
                if (Ids == null || Ids.Length == 0 || Ids[0] == null)
                    return "";
                else
                    return Ids[0];
            }
        }

        /// <summary>
        /// Builds a description of this IoConfig instance.
        /// </summary>
        /// <returns>The description text.</returns>
        public virtual string ToPrint()
        {
            StringBuilder text = new StringBuilder();
            ToPrint(text);
            return text.ToString();
        }

        /// <summary>
        /// Builds a description of this IoConfig instance.
        /// </summary>
        /// <param name="text">The text buffer in which to write the description.</param>
        protected void ToPrint(StringBuilder text)
        {
            text.Append("IoConfig: type=");
            text.Append(this.GetType().Name);
            text.Append("\n");
            DumpIds(text);
            DumpRanges(text);
        }

        public void DumpIds(StringBuilder text)
        {
            foreach (string id in this.Ids) {
                text.Append("    device id: ");
                text.Append(id);
                text.Append("\n");
            }
        }

        public void DumpRanges(StringBuilder text)
        {
            if (FixedRanges != null) {
                for (int i = 0; i < FixedRanges.Length; i++) {
                    if (FixedRanges[i] != null) {
                        text.Append("    frange[");
                        text.Append(i);
                        text.Append("]: ");
                        text.Append(FixedRanges[i]);
                        text.Append("\n");
                    }
                }
            }
            if (DynamicRanges != null) {
                for (int i = 0; i < DynamicRanges.Length; i++) {
                    if (DynamicRanges[i] != null) {
                        text.Append("    drange[");
                        text.Append(i);
                        text.Append("]: ");
                        text.Append(DynamicRanges[i]);
                        text.Append("\n");
                    }
                }
            }
        }

        /// <summary>
        /// Prints a description of this I/O configuration to the debug port.
        /// </summary>
        public void Print()
        {
            DebugStub.WriteLine(ToPrint());
        }

#if SINGULARITY_PROCESS
        public static unsafe IoConfig GetConfig()
        {
            // first get the device signature
            ArrayList idlist = new ArrayList();
            char[] idbuffer = new char[0x80];
            for (int i = 0;; i++) {
                int len = (int)DeviceService.GetPnpSignature(i, null, 0);
                if (len == 0)
                    break;
                if (len > idbuffer.Length)
                    idbuffer = new char[len];
                fixed (char* idbuffer_pinned = &idbuffer[0]) {
                    len = (int)DeviceService.GetPnpSignature(i, idbuffer_pinned, (uint)idbuffer.Length);
                }
                if (len == 0)
                    break;
                string id = new String(idbuffer, 0, len);
                idlist.Add(id);
                Tracing.Log(Tracing.Debug, "PNP Signature: [{0}]", id);
            }
            string[] ids = (string[])idlist.ToArray(typeof(string));
#if false
            string id = null;
            char[] sigArray = new char[DeviceService.GetPnpSignature(null, 0)];
            fixed (char *sigPtr = &sigArray[0]) {
                int len = (int)DeviceService.GetPnpSignature(
                    sigPtr, (uint)sigArray.Length);

                id = String.StringCTOR(sigPtr, 0, len);
            }
#endif

            // now get the fixed resources
            IoRange[] fixedRanges = GetFixedIoResources();

            // now determine if this is a PCI bus, and if so, configure it as
            // such
            PciPortHandle pciPortHandle = new PciPortHandle();

            if (DeviceService.GetPciPort(out pciPortHandle))
            {
                PciPort port = new PciPort(pciPortHandle);
                return PciConfig.Create(ids, port, fixedRanges);
            }
            else {
                Tracing.Log(Tracing.Debug, "PCI Config: None.");
            }

            // it isn't a PCI device, so create a PnpConfig object

            // TODO: We should really copy all of the ranges, so that
            // we can augment even PCI devices (like VGA cards).

            uint rangeCount = DeviceService.GetDynamicIoRangeCount();
            Tracing.Log(Tracing.Debug, "I/O Ranges: {0}", rangeCount);

            IoRange[] dynamicRanges = new IoRange[rangeCount];

            for (uint range = 0; range < rangeCount; range++) {
                ushort port;
                ushort size;
                bool readable;
                bool writable;
                byte * dataAddr;
                uint dataSize;
                byte irq;
                byte irqSize;
                byte dma;
                byte dmaSize;

                if (DeviceService.GetDynamicIoPortRange(range, out port,
                                                        out size, out readable,
                                                        out writable))
                {
                    Tracing.Log(Tracing.Debug, "{0:d4}. I/O Port: port={1:x4}" +
                                "[{2:x}] read={3} write={4}",
                                range, port, size,
                                (UIntPtr)(readable ? 1 : 0),
                                (UIntPtr)(writable ? 1 : 0));
                    dynamicRanges[range] = new IoPortRange(port, size, readable,
                                                           writable);
                }
                else if (DeviceService.GetDynamicIoMemoryRange(range,
                                                               out dataAddr,
                                                               out dataSize,
                                                               out readable,
                                                               out writable))
                {

                    UIntPtr addr = (UIntPtr)dataAddr;
                    Tracing.Log(Tracing.Debug, "{0:d4}. Memory:  addr={1:x8}" +
                                "[2:x] read={3} write={4}",
                                range, addr, dataSize,
                                (UIntPtr)(readable ? 1 : 0),
                                (UIntPtr)(writable ? 1 : 0));
                    dynamicRanges[range] = new IoMemoryRange(addr, dataSize,
                                                             readable,
                                                             writable);
                }
                else if (DeviceService.GetDynamicIoIrqRange(range, out irq,
                                                            out irqSize))
                {
                    Tracing.Log(Tracing.Debug, "{0:d4}. Irq:  irq={1:x2}" +
                                "[{2:x}]", range, irq, irqSize);
                    dynamicRanges[range] = new IoIrqRange(irq, irqSize);
                }
                else if (DeviceService.GetDynamicIoDmaRange(range, out dma,
                                                            out dmaSize))
                {
                    Tracing.Log(Tracing.Debug, "{0:d4}. Dma:  dma={1:x2}" +
                                "[{2:x}]", range, dma, dmaSize);
                    dynamicRanges[range] = new IoDmaRange(dma, dmaSize);
                }
                else {
                    Tracing.Log(Tracing.Debug, "{0:d4}. Empty", range);
                }
            }

            return new PnpConfig(ids, dynamicRanges, fixedRanges);
        }

        // return an IoRange array filled with all of the fixed resources that
        // this assembly requested in its manifest
        private unsafe static IoRange[] GetFixedIoResources()
        {
            uint rangeCount = DeviceService.GetFixedIoRangeCount();
            Tracing.Log(Tracing.Debug, "I/O Ranges: {0}", rangeCount);

            IoRange[] ranges = new IoRange[rangeCount];

            for (uint range = 0; range < rangeCount; range++) {
                ushort port, size;
                bool readable, writable;
                byte * dataAddr;
                uint dataSize;
                byte irq, irqSize;
                byte dma, dmaSize;

                if (DeviceService.GetFixedIoPortRange(range, out port,
                                                      out size, out readable,
                                                      out writable))
                {
                    Tracing.Log(Tracing.Debug, "{0:d4}. I/O Port: port={1:x4}" +
                                "[{2:x}] read={3} write={4}",
                                range, port, size,
                                (UIntPtr)(readable ? 1 : 0),
                                (UIntPtr)(writable ? 1 : 0));
                    ranges[range] = new IoPortRange(port, size, readable,
                                                    writable);
                }
                else if (DeviceService.GetFixedIoMemoryRange(range,
                                                             out dataAddr,
                                                             out dataSize,
                                                             out readable,
                                                             out writable))
                {
                    UIntPtr addr = (UIntPtr)dataAddr;
                    Tracing.Log(Tracing.Debug, "{0:d4}. Memory:  addr={1:x8}" +
                                "[2:x] read={3} write={4}",
                                range, addr, dataSize,
                                (UIntPtr)(readable ? 1 : 0),
                                (UIntPtr)(writable ? 1 : 0));
                    ranges[range] = new IoMemoryRange(addr, dataSize, readable,
                                                      writable);
                }
                else if (DeviceService.GetFixedIoIrqRange(range, out irq,
                                                          out irqSize))
                {
                    Tracing.Log(Tracing.Debug,
                                "{0:d4}. Irq:  irq={1:x2}[{2:x}]",
                                range, irq, irqSize);
                    ranges[range] = new IoIrqRange(irq, irqSize);
                }
                else if (DeviceService.GetFixedIoDmaRange(range, out dma,
                                                          out dmaSize))
                {
                    Tracing.Log(Tracing.Debug,
                                "{0:d4}. Dma:  dma={1:x2}[{2:x}]",
                                range, dma, dmaSize);
                    ranges[range] = new IoDmaRange(dma, dmaSize);
                }
                else {
                    Tracing.Log(Tracing.Debug, "{0:d4}. Empty", range);
                }
            }
            return ranges;
        }
#endif // SINGULARITY_PROCESS
    }
}
