////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PnpBios.cs
//
//  Note:
//

//#define VERBOSE

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;

using System;
using System.Collections;
using System.Diagnostics;
using System.Text;
using System.Configuration.Assemblies;
using System.Runtime.Remoting;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Reflection;

namespace Microsoft.Singularity.Drivers
{
    [CLSCompliant(false)]
    public class PnpBios : IBusDevice
    {
        // since this is in the kernel, it can make whatever ports and memory it
        // wants.  The purpose of having a decorated DeviceRequirement object is
        // just to generate metadata correctly; in truth, we can't do CTR on
        // this because these resources aren't dynamic, and so we can't count on
        // IoSystem to get the resources for us.  Instead, we get our own
        // resources, and then we tell IoSystem about them via the method
        // ReportConfig
        [DriverCategory]
        [Signature("/root/pnp0")]
        [EnumeratesDevice("/pnp/...")]
        class MyConfig : DriverCategoryDeclaration
        {
            [IoMemoryRange(0, Default = 0xf3c30000, Length = 1, AllowWrite = false)]
            IoMemoryRange mem1;

            [IoPortRange(1, Default = 0x20b, Length = 1, AllowWrite = false)]
            IoPortRange port1;

            [IoFixedPortRange(Base = 0x0a79, Length = 0x01, AllowRead = false)]
            IoPortRange isaWritePort;

            [IoFixedPortRange(Base = 0x0279, Length = 0x01, AllowRead = false)]
            IoPortRange isaReadport;
        }

        private static byte lowestbit(uint bits)
        {
            for (byte i = 0; i < 32; i++, bits >>= 1) {
                if ((bits & 1) != 0) {
                    return i;
                }
            }
            return byte.MaxValue;
        }

        private static char hexdigit(byte c)
        {
            return (char)((c >= 10) ? ('A' + (char)c - 10) : ('0' + (char)c));
        }

        [StructLayout(LayoutKind.Explicit)]
        [CLSCompliant(false)]
        public struct PNPNODE {
            [FieldOffset( 0)] public ushort   Size;   //0
            [FieldOffset( 2)] public byte     Node;   //2
            [FieldOffset( 3)] public byte     ProductId0; //3
            [FieldOffset( 4)] public byte     ProductId1; //4
            [FieldOffset( 5)] public byte     ProductId2; //5
            [FieldOffset( 6)] public byte     ProductId3; //6
            [FieldOffset( 7)] public byte     DeviceType0;    //7
            [FieldOffset( 8)] public byte     DeviceType1;    //8
            [FieldOffset( 9)] public byte     DeviceType2;    //9
            [FieldOffset(10)] public ushort   DeviceAttributes;   //10..11
        }

        private IoMemory!  region;
        private IoPort!  isaReadPort;
        private IoPort!  isaWritePort;
        private IoPort!  isaAddressPort;

        private byte    isaCsns;
        private string  newId; // not thread safe!

        private const ushort ISA_ADDRESS_PORT   = 0x0279;
        private const ushort ISA_WRITE_PORT     = 0x0A79;

        private const byte ISA_ADDR_WAKE    = 0x03;
        private const byte ISA_ADDR_CONFIG  = 0x04;
        private const byte ISA_ADDR_STATUS  = 0x05;

        private byte GetIsaResByte()
        {
            isaAddressPort.Write8(ISA_ADDR_STATUS);
            while ((isaReadPort.Read8() & 0x1) == 0) {
                // wait for ready.
            }
            isaAddressPort.Write8(ISA_ADDR_CONFIG);
            return isaReadPort.Read8();
        }

        private void GetIsaResBytes(byte[]! buffer, int begin, int limit)
        {
            for (int i = begin; i < limit; i++) {
                buffer[i] = GetIsaResByte();
            }
        }

        public PnpBios(Resources.PnpBiosInfo pbi)
            requires pbi.pnpRegion != null;
            requires pbi.isaReadPort != null;
        {
            region = pbi.pnpRegion.AtOffset(0, (int)pbi.pnpRegion.Length);
            isaReadPort = pbi.isaReadPort;
            isaWritePort = new IoPort(ISA_WRITE_PORT, 1, Access.Write);
            isaAddressPort = new IoPort(ISA_ADDRESS_PORT, 1, Access.Write);
            isaCsns = (byte)pbi.isaCsns;
        }

        public void Initialize()
        {
        }

        public void Finalize()
        {
        }

        private string DecodeId(byte[]! buffer, int offset)
        {
            return "" +
                (char)('@' + (buffer[offset + 0] >> 2)) +
                (char)('@' + (((buffer[offset + 0] & 0x3) << 3) | (buffer[offset + 1] >> 5))) +
                (char)('@' + ((buffer[offset + 1] & 0x1f))) +
                hexdigit((byte)(buffer[offset + 2] >> 4)) +
                hexdigit((byte)(buffer[offset + 2] & 0xf)) +
                hexdigit((byte)(buffer[offset + 3] >> 4)) +
                hexdigit((byte)(buffer[offset + 3] & 0xf));
        }

        private string DecodePnpId(int offset)
        {
            byte[] buffer = new byte [7];
            region.Read8(offset, buffer, 0, 7);

            return DecodeId(buffer, 0);
        }

        private void DecodeIsaLarge(byte[]! buffer, int size, ArrayList! list)
        {
#if VERBOSE
            DebugStub.Print("  IsaLarge[{0}]: ", __arglist(buffer[0] & 0x7f));
#endif

            switch (buffer[0] & 0x7f) {
              default:
#if VERBOSE
                DebugStub.Print("   ???1 {0,2:x2}\n", __arglist(buffer[0] & 0x7f));
#endif
                break;
              case 0x1:
                if (buffer[10] == 0) {
                    break;
                }
#if VERBOSE
                DebugStub.Print("   Memory inf={0,2:x2} min={1,4:x4}00 max={2,4:x4}00 aln={3,4:x4} len={4,4:x4}00\n",
                                __arglist(
                                    buffer[3],
                                    BitConverter.ToUInt16(buffer, 4),
                                    BitConverter.ToUInt16(buffer, 6),
                                    BitConverter.ToUInt16(buffer, 8),
                                    BitConverter.ToUInt16(buffer, 10)
                                    ));
#endif
                list.Add(new IoMemoryRange((uint)BitConverter.ToUInt16(buffer, 4) << 8,
                                           (uint)BitConverter.ToUInt16(buffer, 10) << 8,
                                           Access.ReadWrite));
                break;
              case 0x2:
#if VERBOSE
                DebugStub.Print("   PNP ANSI Id\n");
#endif
                break;
              case 0x4:
#if VERBOSE
                DebugStub.Print("   PNP Vendor\n");
#endif
                break;
              case 0x5:
                if (BitConverter.ToUInt32(buffer, 16) == 0) {
                    break;
                }
#if VERBOSE
                DebugStub.Print("   32-bit Memory inf={0,2:x2} min={1,8:x8} max={2,8:x8} aln={3,8:x8} len={4,8:x8}\n",
                                __arglist(
                                    buffer[3],
                                    BitConverter.ToUInt32(buffer, 4),
                                    BitConverter.ToUInt32(buffer, 8),
                                    BitConverter.ToUInt32(buffer, 12),
                                    BitConverter.ToUInt32(buffer, 16)));
#endif
                list.Add(new IoMemoryRange((uint)BitConverter.ToUInt32(buffer, 4),
                                           (uint)BitConverter.ToUInt32(buffer, 16),
                                           Access.ReadWrite));
                break;
              case 0x6:
                if (BitConverter.ToUInt32(buffer, 8) == 0) {
                    break;
                }
#if VERBOSE
                DebugStub.Print("   32-bit Fixed Memory inf={0,2:x2} bas={1,8:x8}..{2,8:x8}\n",
                                __arglist(
                                    buffer[3],
                                    BitConverter.ToUInt32(buffer, 4),
                                    BitConverter.ToUInt32(buffer, 4) + BitConverter.ToUInt32(buffer, 8) - 1
                                    ));
#endif
                list.Add(new IoMemoryRange((uint)BitConverter.ToUInt32(buffer, 4),
                                           (uint)BitConverter.ToUInt32(buffer, 8),
                                           Access.ReadWrite));
                break;
            }
        }

        private void DecodeIsaSmall(byte[]! buffer, int size, ArrayList! list)
        {
#if VERBOSE
            DebugStub.Print("  IsaSmall[{0}]: ", __arglist(buffer[0] >> 3));
#endif

            switch (buffer[0] >> 3) {
                default:
#if VERBOSE
                    DebugStub.Print("   ???2 {0,2:x2}\n", __arglist(buffer[0] >> 3));
#endif
                    break;

                case 0x1: // Version
#if VERBOSE
                    DebugStub.Print("   Version PnP={0,2:x2}, Vendor={1,2:x2}\n",
                                    __arglist(
                                        buffer[1],
                                        buffer[2]));
#endif
                    break;
                case 0x2: // Logical Device
#if VERBOSE
                    DebugStub.Print("   Logical Device={0} Flags={1,2:x2} {2,2:x2}\n",
                                    __arglist(
                                        DecodeId(buffer, 1),
                                        buffer[5],
                                        buffer[6]));
#endif
                    break;
                case 0x3: // Compatible Device
#if VERBOSE
                    DebugStub.Print("   Compatible Device={0}\n",
                                    __arglist(DecodeId(buffer, 1)));
#endif
                    newId = "/" + DecodeId(buffer,1) + newId;
                    break;
                case 0x4: // IRQ
                    byte irq = lowestbit(BitConverter.ToUInt16(buffer, 1));
                    if (size >= 4) {
#if VERBOSE
                        DebugStub.Print("   IRQ {0,4:x4} type={1,2:x2}\n",
                                        __arglist(irq, buffer[3]));
#endif
                    }
                    else {
#if VERBOSE
                        DebugStub.Print("   IRQ {0,4:x4}\n", __arglist(irq));
#endif
                    }
                    list.Add(new IoIrqRange(irq, 1));
                    break;
                case 0x5: // DMA
                    byte dma = lowestbit(buffer[1]);
#if VERBOSE
                    DebugStub.Print("   DMA {0,2:x2} type={1,2:x2}\n",
                                    __arglist(dma, buffer[2]));
#endif
                    list.Add(new IoDmaRange(dma, 1));
                    break;
                case 0x6: // [
#if VERBOSE
                    DebugStub.Print("   Start pri={0} [\n",
                                    __arglist((buffer[0] >> 3 == 2 ? buffer[1] : (byte)0)));
#endif
                    break;
                case 0x7: // ]
#if VERBOSE
                    DebugStub.Print("   ] End\n");
#endif
                    break;
                case 0x8: // Port
                    if (buffer[7] == 0) {
                        break;
                    }
#if VERBOSE
                    DebugStub.Print("   I/O Port inf={0,2:x2} min={1,4:x4} max={2,4:x4} aln={3,2:x2} len={4,2:x2} {5,4:x4}..{6,4:x4}\n",
                                    __arglist(
                                        buffer[1],
                                        BitConverter.ToUInt16(buffer, 2),
                                        BitConverter.ToUInt16(buffer, 4),
                                        buffer[6],
                                        buffer[7],
                                        BitConverter.ToUInt16(buffer, 2),
                                        BitConverter.ToUInt16(buffer, 2) + buffer[7] - 1));
#endif
                    list.Add(new IoPortRange(BitConverter.ToUInt16(buffer, 2),
                                             buffer[7],
                                             Access.ReadWrite));
                    break;
                case 0x9: // Fixed Port
                    if (buffer[3] == 0) {
                        break;
                    }
#if VERBOSE
                    DebugStub.Print("   Fixed I/O Port bas={0,4:x4} len={1,2:x2}  {2,4:x4}..{3,4:x4}\n",
                                    __arglist(
                                        BitConverter.ToUInt16(buffer, 1),
                                        buffer[3],
                                        BitConverter.ToUInt16(buffer, 1),
                                        BitConverter.ToUInt16(buffer, 1) + buffer[3] - 1));
#endif
                    list.Add(new IoPortRange(BitConverter.ToUInt16(buffer, 1),
                                             buffer[3],
                                             Access.ReadWrite));
                    break;
                case 0xe: // Vendor
#if VERBOSE
                    DebugStub.Print("   Vendor\n");
#endif
                    break;
            }
        }

        private byte[]! SizeBuffer(byte[] buffer, int size)
        {
            if (buffer == null || buffer.Length < size) {
                return new byte[size];
            }
            return buffer;
        }

        private PnpConfig DecodeIsa()
        {
            ArrayList list = new ArrayList();
            byte[] buffer = null;

            for (;;) {
                byte b = GetIsaResByte();
                int size;

                if (b == 0x79) {
                    break;
                }

                if ((b & 0x80) != 0) {
                    byte b1 = GetIsaResByte();
                    byte b2 = GetIsaResByte();
                    size = 3 + (((int)b2 << 8) | b1);

                    buffer = SizeBuffer(buffer, size);
                    buffer[0] = b;
                    buffer[1] = b1;
                    buffer[2] = b2;
                    GetIsaResBytes(buffer, 3, size);

                    DecodeIsaLarge(buffer, size, list);
                }
                else {
                    size = 1 + (b & 0x7);
                    buffer = SizeBuffer(buffer, size);
                    buffer[0] = b;
                    GetIsaResBytes(buffer, 1, size);

                    DecodeIsaSmall(buffer, size, list);
                }
            }
            return NewPnpConfig((!)newId, list);
        }

        private PnpConfig DecodePnp(int offset, int limit)
        {
            ArrayList list = new ArrayList();
            byte[] buffer = null;

            while (offset < limit) {
                if (region.Read8(offset) == 0x79) {
                    offset += 2;
                    break;
                }

                int size;

                if ((region.Read8(offset) & 0x80) != 0) {
                    size = 3 + region.Read16(offset + 1);

                    buffer = SizeBuffer(buffer, size);
                    region.Read8(offset, buffer, 0, size);

                    DecodeIsaLarge(buffer, size, list);
                }
                else {
                    size = 1 + (region.Read8(offset) & 0x7);

                    buffer = SizeBuffer(buffer, size);
                    region.Read8(offset, buffer, 0, size);

                    DecodeIsaSmall(buffer, size, list);
                }
                offset += size;
            }
            return NewPnpConfig((!)newId, list);
        }

        private static PnpConfig! NewPnpConfig(string! id, ArrayList! list)
        {
            ArrayList idlist = new ArrayList();

            string pnp_id = "/pnp" + id;

            idlist.Add(pnp_id);

            int pos = 5; // skip "/pnp/"

            // DebugStub.WriteLine("parsing isa pnp id: " + pnp_id);

            for (;;) {
                int next = pnp_id.IndexOf('/', pos);
                if (next == -1)
                    break;
                string variant = pnp_id.Substring(0, next);
                idlist.Add(variant);
                // DebugStub.WriteLine("adding variant: " + variant);
                pos = next + 1;
            }
            
            string[]! ids = (!)(string[])idlist.ToArray(typeof(string));

            // DebugStub.Break();
            return new PnpConfig(ids, list);
        }


        // create a PnpConfig object that tells all of the resources being used
        // by this resource, so that we can account for everything in IoSystem

        // This may seem perverse, but it is necessary!  We don't use
        // enumeration to get the root device, and our accounting tool requires
        // the IoConfig objects that are created via enumeration.  Since the
        // memory range and readport range are gleaned through the boot process,
        // without enumeration, we have to provide this hack to get the resource
        // config into an IoConfig object, or else our accounting will not
        // include the root bus.
#if SINGULARITY_KERNEL
        public PnpConfig! ReportConfig()
#else
        internal PnpConfig! ReportConfig()
#endif
        {
            ArrayList list = new ArrayList();
            IoRange [] fixedRanges = new IoRange[2];

            list.Add(new IoMemoryRange((UIntPtr)region.PhysicalAddress.Value,
                                       (UIntPtr)region.Length,
                                       true, true));
            list.Add(new IoPortRange(isaReadPort.Port,
                                     isaReadPort.Size,
                                     isaReadPort.Readable,
                                     isaReadPort.Writable));

            // since we're creating manual (and, for that matter, trusted)
            // accounting, let's save a bit of work and generate the fixed
            // resources right now.
            fixedRanges[0] = new IoPortRange(isaWritePort.Port,
                                             isaWritePort.Size,
                                             isaWritePort.Readable,
                                             isaWritePort.Writable);
            fixedRanges[1] = new IoPortRange(isaAddressPort.Port,
                                             isaAddressPort.Size,
                                             isaAddressPort.Readable,
                                             isaAddressPort.Writable);
            PnpConfig p = new PnpConfig(new string[] { "" }, list);
            p.FixedRanges = fixedRanges;
            return p;
        }


        public SortedList Enumerate()
        {
            SortedList found = new SortedList();

            Tracing.Log(Tracing.Audit, "Probing ISA Information");
            DebugStub.WriteLine("Enumerating ISA PNP:");
            int node = 0x000;
            for (byte csn = 1; csn <= isaCsns; csn++) {
#if VERBOSE
                DebugStub.Print("Reading csn={0}\n", __arglist(csn));
#endif
                isaAddressPort.Write8(ISA_ADDR_WAKE);
                isaWritePort.Write8(csn);

                byte[] buffer = new byte[9];
                GetIsaResBytes(buffer, 0, 9);
                newId = "/" + DecodeId(buffer, 0);

                DebugStub.Print(newId);
                DebugStub.Print("/");
                DebugStub.Print(node);
                DebugStub.Print(":\n");
                found.Add(String.Format("/{0,3:x3}", node++), DecodeIsa());
            }

#if VERBOSE
            DebugStub.Print("\n");
#endif
            // See http://download.microsoft.com/download/1/6/1/161ba512-40e2-4cc9-843a-923143f3456c/devids.txt
            node = 0x100;
            for (int offset = 0; offset < region.Length;) {
                ushort size = region.Read16(offset);
#if VERBOSE
                ushort attr = region.Read16(offset + 10);
#endif

                newId = "/" + DecodePnpId(offset + 3);

#if VERBOSE
                DebugStub.Print("  {0,8:x8} {1} {2,4:x4}",
                                __arglist((uint)(region.PhysicalAddress.Value + (ulong)offset), newId, attr));
                String s = "";

                if ((attr & 0x0100) != 0) s += " dyn";
                if ((attr & 0x0080) != 0) s += " onl";
                if ((attr & 0x0040) != 0) s += " rmv";
                if ((attr & 0x0020) != 0) s += " dck";
                if ((attr & 0x0010) != 0) s += " ipl";
                if ((attr & 0x0008) != 0) s += " inp";
                if ((attr & 0x0004) != 0) s += " out";
                if ((attr & 0x0002) != 0) s += " cfg";
                if ((attr & 0x0001) != 0) s += " dis";

                DebugStub.WriteLine(s);
#endif

                DebugStub.WriteLine("{0}/{1:x3}:", __arglist(newId, node));
                found.Add(String.Format("/{0,3:x3}", node++),
                          DecodePnp(offset + 12, offset + size));

                offset += size;
            }
            DebugStub.WriteLine("");
            return found;
        }
    }
}
