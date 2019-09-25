//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Notes:
//
//  Simple Driver for Intel 8254x PCI Ethernet Cards.
//
//  Useful reference URLs:
//      http://download.intel.com/design/network/manuals/8254x_GBe_SDM.pdf
//
//  We use standard IP/TCP checksum offloading.
//
//  The driver currently runs in interrupt driven mode using hardware based
//  interrupt throttling.
//
//  Phy handling is automatic and relies on attached phy supporting
//  auto-negotiation.  The phy update interrupt is used to keep track
//  of phy state.
//
//  TODO:
//
//   - Flow Control Support
//   - Support for packet fragments (all packets must have a single fragment
//     currently)
//   - Jumbo Packets
//   - Transmit TCP/IP checksum offloading
//

//#define DEBUG_INTEL

using System;
using System.Threading;
using System.Diagnostics;
using System.Collections;

using Microsoft.Contracts;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
//using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Io.Net;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Drivers;
using Microsoft.SingSharp;

using Microsoft.Singularity.Directory;
//using Microsoft.Singularity.Extending;

using Drivers.Net;

namespace Microsoft.Singularity.Drivers.Network.Intel
{
    [CLSCompliant(false)]
    public class Intel: IThreadStart
    {
        internal const uint MaxTxFragmentsPerPacket = 1; // Todo: allow frags
        internal const uint MaxRxFragmentsPerPacket = 1; // Todo: allow frags

        internal const uint MaxRxPackets = 511; // TODO: 1023;   // one less than full buffer
        internal const uint MaxTxPackets = 511; // TODO: 2047;

        // Fragments must be power of two.
        internal const uint MaxTxFragmentsInRing = ((MaxTxPackets + 1) *
                                                    MaxTxFragmentsPerPacket) ;
        internal const uint MaxRxFragmentsInRing = ((MaxRxPackets + 1) *
                                                    MaxRxFragmentsPerPacket);

        internal const ChecksumSupport ChecksumSupport =
                              Microsoft.Singularity.Io.Net.ChecksumSupport.AllIp4Receive
                            | Microsoft.Singularity.Io.Net.ChecksumSupport.AllIp6Receive;

        internal const uint IEEE8023FrameBytes = 1518;
        internal const uint MtuBytes           = 1514;
        internal const uint PhyAddress         = 1;

        private string             cardName;
        private CardType            cardType;
        //private PciDeviceConfig    pciConfig;
        private PciMemory           ioMemory;
        //TODO: private IoIrq              irq;
        private Thread              irqWorkerThread;
        private bool                irqWorkerStop;
        private bool                ioRunning;

        private IntelEventRelay     eventRelay;

        private EerdRegister       eerdReg;
        private EthernetAddress     macAddress;

        private IntelRxRingBuffer  rxRingBuffer;
        private IntelTxRingBuffer  txRingBuffer;

        [NotDelayed]
        internal Intel(PciDeviceConfig config, PciMemory ioMemory, string cardName, CardType cardType)
        {
            this.ioMemory = ioMemory;
            this.cardName = cardName;
            this.cardType = cardType;

            //TODO: IoIrqRange iir = res.irq;
            //TODO: irq = iir.IrqAtOffset(0);

            rxRingBuffer = new IntelRxRingBuffer(MaxRxFragmentsInRing);
            txRingBuffer = new IntelTxRingBuffer(MaxTxFragmentsInRing);

            //PciDeviceConfig config = (PciDeviceConfig)IoConfig.GetConfig();
            //this.pciConfig = config;

//            DebugWriteLine("PCI Control {0:x8} Status {1:x8}",
//                           DebugStub.ArgList(config.Control, config.Status));
/*
            byte cap = config.Capabilities;
            while (cap != 0 && cap < 0xff) {
                DebugWriteLine("Capability at: {0:x2}", DebugStub.ArgList(cap));
                byte id = config.Read8(cap);
                if (id == 7) {
                    DebugWriteLine("PCI-X Command {0:x4} Status {1:x8}",
                                   DebugStub.ArgList(
                                       config.Read16(cap + 2) & 0x3f,
                                       config.Read32(cap + 4)
                                       )
                                   );
                }
                else if (id == 5) {
                    // MSI capability - only reached if enabled,
                    // but usually present.
                    DebugWriteLine("MSI Control {0:x4} Address {1:x8}.{2:x8} Data {3:x4}",
                                   DebugStub.ArgList(config.Read16(cap + 2),
                                             config.Read32(cap + 8),
                                             config.Read32(cap + 4),
                                             config.Read16(cap + 10)
                                             )
                              );
                }
                else {
                    DebugWriteLine("Unknown capability {0:x2}", DebugStub.ArgList(id));
                }

                cap = config.Read8(cap + 1);
            }
*/
            eerdReg = new EerdRegister(config.DeviceId);

            //DebugWriteLine("Irq {0}", DebugStub.ArgList(irq.Irq));

//            Debug.Assert((config.Control & PciConfig.PCI_ENABLE_BUS_MASTER) != 0);
//            Debug.Assert((config.Control & PciConfig.PCI_ENABLE_MEMORY_SPACE) != 0);
//            DebugStub.Assert(config.InterruptsEnabled);
        }

        ~Intel()
        {
            ReleaseResources();
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Initialisation and finalisation code
        //
        internal void Initialize()
        {
            DebugPrint("Initialising " + DriverName + " Version " + DriverVersion);

            //TODO: if (!irq.RegisterInterrupt()) {
            //    DebugStub.Break();
            //}

            ResetDevice();
            SetupPhys();
            SetupMac();
        }

        void ReleaseResources()
        {
            DisableInterrupts();
            StopIo();
            //TODO: irq.ReleaseInterrupt();
            irqWorkerThread = null;
        }

        internal void Shutdown()
        {
            if (irqWorkerThread != null) {
                // XXX This is not the right way to do this.
                DisableInterrupts();
                StopIo();
            }
        }

        public void Run()
        {
            System.DebugStub.Print("Intel@" + Kernel.CurrentThread + ". ");
            IrqWorkerMain();
        }

        internal void StartIo()
        {
            irqWorkerStop   = false;
            irqWorkerThread = new Thread(this);
            irqWorkerThread.Start();

            SetupMac();

            DisableInterrupts();//TODO: EnableInterrupts();

            StartReceiver();
            StartTransmitter();
            this.ioRunning = true;
        }

        internal void StopIo()
        {
            StopTransmitter();
            StopReceiver();
            if (irqWorkerThread != null) {
                // Set stop flag, wake-up irqWorker thread, then wait.
                irqWorkerStop = true;
                //TODO: irq.Pulse();
                //TODO: irqWorkerThread.Join();
                irqWorkerThread = null;
            }
            this.ioRunning = false;
        }

        internal void SetEventRelay(IntelEventRelay intelEventRelay)
        {
            eventRelay = intelEventRelay;
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Setup functions
        //
        private void ResetDevice()
        {
            // Disable all interrupts
            DisableInterrupts();

            DebugWriteLine("CTRL pre-device-reset : {0:x8}\n",
                           DebugStub.ArgList(Read32(Register.CTRL)));

            Write32(Register.RECV_CTRL, 0);
            Write32(Register.TSMT_CTRL, TsmtCtrlBits.PAD_SHORT_PACKETS);
            Read32(Register.STATUS);

            // Allow pending PCI transactions to complete
            Delay(10);

            // Reset the device
            RegSetBits((int)Register.CTRL, CtrlBits.RST | CtrlBits.PHY_RST);

            // Wait for 3us before board is really reset
            Delay(3);

            Delay(100);

            Read32(Register.CTRL);

            // Set the control register to the proper initial values,
            // clearing RST and PHY_RST as a side-effect.
            Write32(Register.CTRL, CtrlBits.FD | CtrlBits.ASDE | CtrlBits.SLU);

            while ((Read32(Register.CTRL) & CtrlBits.RST) != 0) {
                DebugWriteLine(".");
            }
            DebugWriteLine("Autonegotiation complete");
        }

        private void SetupPhys()
        {
            if (this.cardType == CardType.I82545GM ) {
                Write32(Register.MDIC, Mdic.MdiRead);
                while ((Read32(Register.MDIC) & Mdic.Ready) == 0);
                uint mdic = Read32(Register.MDIC) & Mdic.DataMask;
                mdic |= Mdic.MdiWrite;
                mdic &= Mdic.PowerMask;
                Write32(Register.MDIC, mdic);
                while ((Read32(Register.MDIC) & Mdic.Ready) == 0);

                DumpPhy();

                uint ctrl = Read32(Register.CTRL);
                ctrl |= CtrlBits.SLU | CtrlBits.ASDE;
                ctrl &= ~(CtrlBits.ILOS | CtrlBits.FRCSPD | CtrlBits.FRCDPLX);
                Write32(Register.CTRL, ctrl);
                Delay(20);

                // Wait for link to come up
                int attempts = 5000;
                while ((MiiRead(PhyAddress, 1) & 0x4) == 0) {
                    Delay(1000);
                    if (0 == attempts--) {
                        DumpPhy();
                        DebugStub.Break();
                    }
                }

                DumpPhy();

                uint phyCtrl = MiiRead(PhyAddress, 0);
                phyCtrl |= 0x1200;  // Enable-AutoNeg + Restart-AutoNeg
                MiiWrite(PhyAddress, 0, phyCtrl);

                uint phyStat;
                attempts = 5000;
                do {
                    Delay(1000);
                    phyStat = MiiRead(PhyAddress, 1);
                    phyStat = MiiRead(PhyAddress, 1);
                } while ((phyStat & 0x20) == 0 && --attempts > 0); // wait for autoneg complete

                DebugStub.Assert((phyStat & 0x20) != 0);

                // Transfer settings from phy to ctrl
                uint phyPssr = MiiRead(PhyAddress, 17);
                ctrl = Read32(Register.CTRL);
                ctrl &= ~(CtrlBits.SPEED | CtrlBits.FD);
                if ((phyPssr & (1 << 13)) != 0) {
                    ctrl |= CtrlBits.FD;
                }

                ctrl |= ((phyPssr >> 14) & 3) << 8;
                ctrl |= CtrlBits.FRCSPD | CtrlBits.FRCDPLX;
                Write32(Register.CTRL, ctrl);

                Delay(1000000);

                DumpPhy();
            }
            else if (this.cardType == CardType.I82541PI) {
                // Use Internal Phys mode (SerDes is not possible for some 8254x cards)
                Write32BitRange(Register.CTRL_EXT,
                                CtrlExtBits.LINK_MODE_PHYS,
                                CtrlExtBits.LINK_MODE_LO_BIT,
                                CtrlExtBits.LINK_MODE_HI_BIT);
            }

            // We don't want flow control
            Write32(Register.FCAL,  0x0);
            Write32(Register.FCAH,  0x0);
            Write32(Register.FCT,   0x0);
            Write32(Register.FCTTV, 0x0);
        }

        private void SetupMac()
        {
            uint ral, rah;

            // Setup our Ethernet address
            macAddress = GetMacFromEeprom();

            DebugStub.Print("Setting Ethernet Mac Address to " + macAddress + ". ");

            GetMacHiLow(out ral, out rah, macAddress);
            rah = rah | RahRegister.ADDRESS_VALID;
            Write32(Register.RAL0, ral);
            Write32(Register.RAH0, rah);

            // Clear the mutlicast table array
            for (uint i = 0; i < MtaRegister.MTA_LENGTH; i++)
            {
                Write32(Register.MTA_START + (4*i), 0);
            }

            // Setup Descriptor buffers for rx
            ResetRxRingBuffer();

            // Setup Receiever Control flags
            Write32(Register.RECV_CTRL, (RecvCtrlBits.BROADCAST_ACCEPT |
                                         RecvCtrlBits.STRIP_CRC |
                                         RecvCtrlBits.LOOPBACK_MODE_DISABLE |
                                         RecvCtrlBits.MULTICAST_OFFSET_47_36 |
                                         RecvCtrlBits.BUFFER_SIZE_2KB |
                                         RecvCtrlBits.RECV_DESC_THRESHOLD_QUARTER));
            // Note: If MTU ever changes (e.g. for jumbo frames), the
            // recv buffer size will need to be increased.

            // Setup the rx interrupt delay
            Write32(Register.RECV_DELAY_TIMER, RxDelayTimers.RECV_DELAY_TIMER);
            Write32(Register.RECV_INT_ABS_TIMER, RxDelayTimers.RECV_ABSOLUTE_TIMER);

            // Enable IP and TCP checksum calculation offloading
            Write32(Register.RECV_CHECKSUM, (RecvChecksumBits.IP_CHECKSUM_ENABLE |
                                              RecvChecksumBits.TCP_CHECKSUM_ENABLE |
                                              RecvChecksumBits.IP6_CHECKSUM_ENABLE));

            // Setup Descriptor buffers for tx
            ResetTxRingBuffer();

            // Setup Transmit Control flags
            Write32(Register.TSMT_CTRL,
                    TsmtCtrlBits.PAD_SHORT_PACKETS |
                    TsmtCtrlBits.COLL_THRESHOLD_DEFAULT |
                    TsmtCtrlBits.COLL_DISTANCE_DEFAULT);

            // Setup Transmit Inter Frame Gap
            Write32(Register.TSMT_IPG, TsmtIpg.DEFAULT_IPG);

            // TODO enable transmit checksum offloading
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Helper functions
        //
        internal void GetMacHiLow(out uint addr_low,
                                  out uint addr_hi,
                                  EthernetAddress mac)
        {
            byte[] macBytes = mac.GetAddressBytes();
            addr_hi  = (uint) ((macBytes[5] << 8) |
                               (macBytes[4]));
            addr_low = (uint) ((macBytes[3] << 24) |
                               (macBytes[2] << 16) |
                               (macBytes[1] << 8) |
                               (macBytes[0]));
        }

        internal EthernetAddress GetMacFromEeprom()
        {
            ushort eepromData;

            byte[] macBytes = new byte[6];

            // Mac address is in reverse byte order in the EEPROM
            eepromData = ReadEepromWord(0);
            macBytes[0] = (byte) (eepromData & 0xff);
            macBytes[1] = (byte) (eepromData >> 8);

            eepromData = ReadEepromWord(1);
            macBytes[2] = (byte) (eepromData & 0xff);
            macBytes[3] = (byte) (eepromData >> 8);

            eepromData = ReadEepromWord(2);
            macBytes[4] = (byte) (eepromData & 0xff);
            macBytes[5] = (byte) (eepromData >> 8);

            return new EthernetAddress(macBytes);
        }

        private ushort ReadEepromWord(ushort eepromAddress)
        {
            uint eepromRead;

            // Write address required
            uint writeVal = (EerdRegister.Start |
                             ((uint) eepromAddress << eerdReg.AddressShift));

            Write32(Register.EERD, writeVal);

            // wait until read has completed
            do {
                eepromRead = Read32(Register.EERD);
            } while ((eepromRead & eerdReg.Done) == 0);

            // return data value
            return (ushort) (eepromRead >> EerdRegister.DataShift);
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Interrupt Handling
        //
        internal void EnableInterrupts()
        {
            // Clear existing interrupts
            Write32(Register.IMC, 0xffffffff);
            Read32(Register.ICR);

            // Set interrupts we are interested in
            RegSetBits((int)Register.IMS, (InterruptMasks.RXT0 | InterruptMasks.RXO |
                                      InterruptMasks.RXDMT0 |
                                      InterruptMasks.LSC | InterruptMasks.TXQE |
                                      InterruptMasks.TXDW));
        }

        internal void DisableInterrupts()
        {
            // Clear existing interrupts
            Write32(Register.IMC, 0xffffffff);
            Read32(Register.ICR);
        }

        private bool HandleInterrupts(uint intrCause)
        {
            if (intrCause == 0) {
                //TODO: return false;
            }
            //DebugPrint("HandleInterrupts ???\n");

            NicEventType ev = NicEventType.NoEvent;

            if ((intrCause & InterruptMasks.LSC) != 0) {
                DebugPrint("Link Status Change\n");
                ev |= NicEventType.LinkEvent;
            }

            if ((intrCause & InterruptMasks.RXSEQ) != 0) {
                DebugPrint("Sequence Error\n");
                ev |= NicEventType.LinkEvent;
            }

            if (((InterruptMasks.RXT0 |
                  InterruptMasks.RXO |
                  InterruptMasks.RXDMT0) & intrCause)  != 0) {
                ev |= NicEventType.ReceiveEvent;
            }

            // no transmit interupts are set, check rxbuffer to see
            // if any packets have been sent since last time
            if (txRingBuffer.NewTransmitEvent()) {
                ev |= NicEventType.TransmitEvent;
            }

            // TODO: not necessary
            if (rxRingBuffer.NewReceiveEvent()) {
                ev |= NicEventType.ReceiveEvent;
            }

            if (ev == NicEventType.NoEvent) {
                //                DebugPrint("HandleInterrupt: no event\n");
                return false;
            }

            if (eventRelay != null) {
                eventRelay.ForwardEvent(ev);
            } else {
                DebugPrint("event relay is NULL!\n");
            }

            return true;
        }

        private void IrqWorkerMain()
        {
            DebugPrint(
                "Intel {0} Ethernet Driver irq worker thread started.\n",
                DebugStub.ArgList(this.cardName)
                       );
            uint rcnt = 0;
            uint missed = 0;
            uint nobuf = 0;

            while (irqWorkerStop == false) {
                Thread.Yield(); //TODO: irq.WaitForInterrupt();
                uint icr = Read32(Register.ICR);
                HandleInterrupts(icr);

                rcnt += Read32(Register.TOTAL_RECV_PACKETS);
                missed += Read32(0x4010);
                nobuf += Read32(0x40a0);
                INucleusCalls.DebugPrintHex(10, rcnt - nobuf);
                INucleusCalls.DebugPrintHex(20, rcnt);
                INucleusCalls.DebugPrintHex(30, missed);

                //TODO: irq.AckInterrupt();
            }

            DisableInterrupts();
            DebugPrint(
                "Intel {0} Ethernet Driver irq worker thread stopped.\n",
                DebugStub.ArgList(this.cardName)
                       );
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Rx buffer operations
        //

        internal void PopulateRecvBuffer(PacketFifo fromUser)
        {
            if (fromUser.Count < 1) {
                return;
            }
            using (rxRingBuffer.thisLock.Lock()) {
                while (fromUser.Count > 0) {
                    rxRingBuffer.LockedPushRecvBuffer(fromUser.Pop());
                }
                Write32(Register.RECV_DESC_TAIL, rxRingBuffer.Head);
            }
        }

        internal void DrainRecvBuffer(PacketFifo toUser)
        {
            using (rxRingBuffer.thisLock.Lock()) {
                rxRingBuffer.LockedDrainRecvBuffer(toUser);
            }
        }

        private void ResetRxRingBuffer()
        {
            ulong descBase;
            uint descBaseLo, descBaseHi;

            rxRingBuffer.Reset();
            descBase = rxRingBuffer.BaseAddress.ToUInt64();
            descBaseLo = (uint)(0xffffffff & descBase);
            descBaseHi = (uint) (0xffffffff & (descBase >> 32));
            Write32(Register.RECV_DESC_BASE_LO, ByteOrder.HostToLittleEndian(descBaseLo));
            Write32(Register.RECV_DESC_BASE_HI, ByteOrder.HostToLittleEndian(descBaseHi));
            Write32(Register.RECV_DESC_LENGTH, ByteOrder.HostToLittleEndian(rxRingBuffer.DescLength));
            Write32(Register.RECV_DESC_HEAD, ByteOrder.HostToLittleEndian(rxRingBuffer.Head));
            Write32(Register.RECV_DESC_TAIL, ByteOrder.HostToLittleEndian(rxRingBuffer.Tail));
        }

        private void StartReceiver()
        {
            ResetRxRingBuffer();
            //            RegSetBits((int)Register.RECV_CTRL, RecvCtrlBits.RECV_ENABLE | RecvCtrlBits.UNICAST_PROMISCUOUS | RecvCtrlBits.MULTICAST_PROMISCUOUS);
            RegSetBits((int)Register.RECV_CTRL, RecvCtrlBits.RECV_ENABLE);

            DebugPrint("Receiver Enabled.\n");
        }

        private void StopReceiver()
        {
            RegClrBits((int)Register.RECV_CTRL, RecvCtrlBits.RECV_ENABLE);
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Tx buffer operations
        //

        internal void PopulateTsmtBuffer(PacketFifo fromUser)
        {
            DebugStub.Assert(this.ioRunning);

            // since no transmit interrupts are sent, we must check for
            // transmission events here
            if (txRingBuffer.NewTransmitEvent()) {
                NicEventType ev = NicEventType.TransmitEvent;
                if (eventRelay != null) {
                    eventRelay.ForwardEvent(ev);
                }
            }

            using (txRingBuffer.thisLock.Lock()) {
                while (fromUser.Count > 0) {
                    Packet packet = fromUser.Pop();
                    txRingBuffer.LockedPushTsmtBuffer(packet);
                }
                // update hardware tail pointer
                // so that hardware knows it has new packets to transmit
                Write32(Register.TSMT_DESC_TAIL, txRingBuffer.Head);  // sw head is hw tail
            }
        }

        internal void DrainTsmtBuffer(PacketFifo toUser)
        {
            using (txRingBuffer.thisLock.Lock()) {
                txRingBuffer.LockedDrainTsmtBuffer(toUser);
            }
        }

        private void ResetTxRingBuffer()
        {
            ulong descBase;
            uint descBaseLo, descBaseHi;

            txRingBuffer.Reset();
            descBase = txRingBuffer.BaseAddress.ToUInt64();
            descBaseLo = (uint)(0xffffffff & descBase);
            descBaseHi = (uint) (0xffffffff & (descBase >> 32));
            Write32(Register.TSMT_DESC_BASE_LO, ByteOrder.HostToLittleEndian(descBaseLo));
            Write32(Register.TSMT_DESC_BASE_HI, ByteOrder.HostToLittleEndian(descBaseHi));
            Write32(Register.TSMT_DESC_LENGTH, ByteOrder.HostToLittleEndian(txRingBuffer.DescLength));
            Write32(Register.TSMT_DESC_HEAD, ByteOrder.HostToLittleEndian(txRingBuffer.Head));
            Write32(Register.TSMT_DESC_TAIL, ByteOrder.HostToLittleEndian(txRingBuffer.Tail));
        }

        private void StartTransmitter()
        {
            ResetTxRingBuffer();
            RegSetBits((int)Register.TSMT_CTRL, TsmtCtrlBits.TSMT_ENABLE);

            DebugPrint("Transmitter Enabled.\n");
        }

        private void StopTransmitter()
        {
            RegClrBits((int)Register.TSMT_CTRL, TsmtCtrlBits.TSMT_ENABLE);
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Driver Details
        //

        internal string DriverName
        {
            get { return string.Format("Intel {0} Ethernet Driver", this.cardName); }
        }

        internal string DriverVersion
        {
            get { return "0.1"; }
        }

        internal EthernetAddress getMacAddress
        {
            get { return macAddress; }
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // MII
        //

        private uint MiiRead(uint phy, uint register)
        {
            uint mdic = (((phy & Mdic.PhyMask) << Mdic.PhyRoll) |
                         ((register & Mdic.RegMask) << Mdic.RegRoll) |
                         Mdic.MdiRead);

            Write32(Register.MDIC, mdic);
            do {
                mdic = Read32(Register.MDIC);
                DebugStub.Assert((mdic & Mdic.Error) == 0);
            } while ((mdic & Mdic.Ready) == 0);

            return mdic & Mdic.DataMask;
        }

        private uint MiiWrite(uint phy, uint register, uint value)
        {
            DebugStub.Assert((value & ~Mdic.DataMask) == 0);

            uint mdic = (((phy & Mdic.PhyMask) << Mdic.PhyRoll) |
                         ((register & Mdic.RegMask) << Mdic.RegRoll) |
                         Mdic.MdiWrite);

            mdic |= (uint)value;

            Write32(Register.MDIC, mdic);
            do {
                mdic = Read32(Register.MDIC);
                DebugStub.Assert((mdic & Mdic.Error) == 0);
            } while ((mdic & Mdic.Ready) == 0);

            return mdic & Mdic.DataMask;
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Register accessors / modifiers / utilities
        //

        private uint Read32(uint offset)
        {
            return ioMemory.Read32((int) offset);
        }

        private void Write32(uint offset, uint value)
        {
            ioMemory.Write32((int) offset, value);
        }

        private void Write32BitRange(uint offset,
                                      uint new_val,
                                      int  hiBit,
                                      int  loBit)
        {
            uint write_val = SetValueBits(Read32(offset), new_val, hiBit, loBit);
            Write32(offset, write_val);
        }

        private void RegSetBits(int offset, uint bits)
        {
            ioMemory.Write32(offset, ioMemory.Read32(offset) | bits);
        }

        private void RegClrBits(int offset, uint bits)
        {
            ioMemory.Write32(offset, ioMemory.Read32(offset) & ~bits);
        }

        private uint SetValueBits(uint value,
                                  uint bits,
                                  int  hiBit,
                                  int  loBit)
        {
            int width = (hiBit - loBit) + 1;
            uint mask =  (1u << width) - 1u;
            bits = (bits & mask);
            value &= ~(mask << loBit);
            value |= bits << loBit;
            return value;
        }

        private void SetBit(ref uint value, int bit)
        {
            value = value | (1u << bit);
        }

        private void ClearBit(ref uint value, int bit)
        {
            value = value & ~(1u << bit);
        }

        private static void Delay(int us)
        {
            long expiry = DateTime.Now.Ticks + (us * 10);
            while (DateTime.Now.Ticks < expiry);
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Debug Helper Functions
        //

        [Conditional("DEBUG_INTEL")]
        internal static void DebugPrint(string format, object arglist)
        {
            DebugStub.Print(format, arglist);
        }

        [Conditional("DEBUG_INTEL")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print(format);
        }

        [Conditional("DEBUG_INTEL")]
        internal static void DebugWriteLine(string format, object arglist)
        {
            DebugStub.WriteLine(format, arglist);
        }

        [Conditional("DEBUG_INTEL")]
        internal static void DebugWriteLine(string format)
        {
            DebugStub.WriteLine(format);
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // Debugging methods
        //
        [Conditional("DEBUG_INTEL")]
        private void DumpBufferDebugRegisters()
        {
            // TODO, uses Tracing log
            DebugPrint("Device Control    {0:x8} Device Status     {1:x8}\n",
                       DebugStub.ArgList(Read32(Register.CTRL),
                                 Read32(Register.STATUS)));

            //DebugPrint("PCI Status {0:x4}", DebugStub.ArgList(this.pciConfig.Status));

            DebugPrint("Recv Control      {0:x8} Tsmt Control      {1:x8}\n",
                       DebugStub.ArgList(Read32(Register.RECV_CTRL),
                                 Read32(Register.TSMT_CTRL)));

            DebugPrint("RDTR              {0:x8} RADV              {1:x8}\n",
                       DebugStub.ArgList(Read32(0x2820), Read32(0x282c)));

            DebugPrint("Total Transmit    {0:x8} Total Received    {1:x8}\n",
                       DebugStub.ArgList(Read32(Register.TOTAL_TSMT_PACKETS),
                                 Read32(Register.TOTAL_RECV_PACKETS)));

            DebugPrint("Interrupt Mask    {0:x8} Rx Error Count    {1:x8}\n",
                       DebugStub.ArgList(Read32(Register.IMS),
                                 Read32(Register.RX_ERR_COUNT)));

            DebugPrint("Recv Addr High    {0:x8} Recv Addr Low     {1:x8}\n",
                       DebugStub.ArgList(Read32(Register.RAH0),
                                 Read32(Register.RAL0)));

            DebugPrint("Recv Desc Head    {0:x8} Recv Desc Tail    {1:x8}\n",
                       DebugStub.ArgList(Read32(Register.RECV_DESC_HEAD),
                                 Read32(Register.RECV_DESC_TAIL)));

            DebugPrint("Tsmt Desc Head    {0:x8} Tsmt Desc Tail    {1:x8}\n",
                       DebugStub.ArgList(Read32(Register.TSMT_DESC_HEAD),
                                 Read32(Register.TSMT_DESC_TAIL)));
        }

        [Conditional("DEBUG_INTEL")]
        private void DumpPhy()
        {
            for (uint i = 0; i < 32; i += 8) {
                DebugWriteLine("PHY {0:x4} : {1:x4} {2:x4} {3:x4} {4:x4} {5:x4} {6:x4} {7:x4} {8:x4}",
                               DebugStub.ArgList(i,
                                         MiiRead(PhyAddress, i + 0),
                                         MiiRead(PhyAddress, i + 1),
                                         MiiRead(PhyAddress, i + 2),
                                         MiiRead(PhyAddress, i + 3),
                                         MiiRead(PhyAddress, i + 4),
                                         MiiRead(PhyAddress, i + 5),
                                         MiiRead(PhyAddress, i + 6),
                                         MiiRead(PhyAddress, i + 7))
                          );
            }
        }

        //#if DEBUG_INTEL
#if false
        // Occasionally helpful when debugging.

        Thread statsThread = null;

        internal void StartStatistics()
        {
            DebugStub.Assert(statsThread == null);
            statsThread = new Thread(new ThreadStart(this.StatisticsMain));
            statsThread.Start();
        }

        internal void ReportChanges(uint[] now)
        {
            DebugWriteLine("Changes.");
            for (int i = 0; i < now.Length; i++) {
                if (now[i] != 0) {
                    DebugWriteLine("{0} [0x40{1:x1}] -> {2}",
                                   DebugStub.ArgList(i, i * 4, now[i]));
                }
            }

            rxRingBuffer.Dump();
            DebugWriteLine("Rx head {0:x8} tail {1:x8}",
                          DebugStub.ArgList(Read32(Register.RECV_DESC_HEAD),
                                    Read32(Register.RECV_DESC_TAIL)));
            DebugWriteLine("ICS = {0:x8} ICR = {1:x8}",
                           DebugStub.ArgList(Read32(Register.ICS),
                                     Read32(Register.ICR)));
        }

        internal void StatisticsMain()
        {
            uint [] counters1 = new uint[64];

            for (;;) {
                Thread.Sleep(TimeSpan.FromSeconds(10));
                GetStatistics(counters1);
                ReportChanges(counters1);
            }
        }

        internal void GetStatistics(uint [] counters)
        {
            for (uint i = 0; i < counters.Length; i++) {
                counters[i] = Read32(0x4000 + i * 4);
            }
        }
#endif
    }
}
