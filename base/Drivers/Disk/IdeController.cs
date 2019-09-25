////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IdeController.cs
//
//  Base Classes and Interfaces for interacting with ATA
//
//  References used:
//  "AT Attachment Interface with Extension (ATA-2)", Revision 4c, DRAFT
//          09/03/97, ISO Working Group T13, http://www.t13.org/
//
//  "AT Attachment 8 - ATA/ATAPI Command Set (ATA8-ACS)", Revision 0, DRAFT
//          08/17/04, ISO Working Group T13, http://www.t13.org/
//

#define DEBUG_SHARED_IRQ

using System;
using System.Collections;
using System.Text;
using System.Threading;
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Drivers.IDE;
using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.Drivers.IDE
{
    public enum IdeSet
    {
        IDE_SET_READ_AHEAD = 0,
        IDE_UNSET_READ_AHEAD,
        IDE_SET_MULTIPLE,
        IDE_SET_NO_REVERT,
        IDE_SET_WRITE_CACHE,
        IDE_SET_MAX_PIO,
        IDE_SET_MAX_UDMA,
    };

    [CLSCompliant(false)]
    public class IdeController
    {
        public const int        PollLoopCount = 1000000;
        public string!          ControllerNameInternal;
        private bool            busMasterDmaAvailable;
        private IoPort[]!       CommandBlock;
        private IoPort[]!       ControlBlock;
        private IdeConfig!      ideConfigHandle;
        private String!         instanceName;
        private IdeDiskConfig   ideDisk1Config;
        private IdeDiskConfig   ideDisk2Config;
        private Thread          irqWorker;
        private bool            irqWorkerStop;
        private bool            initialized;
        private volatile bool   commandPending = false;
        private volatile bool   identifyPending = false;
        private byte            pollStatus = 0;
        private int             cyclesPerReadStatus;
        private int             delay400ns;
        public volatile bool    CatchBug;
        public volatile int     CatchCount;

        public string ControllerName
        {
            get { return ControllerNameInternal; }
        }

        public void SetCommandPending(bool val)
        {
            commandPending = val;
            //Tracing.Log(Tracing.Debug," Command pending set to {0}", commandPending ? "true" : "false");
        }

        public IdeConfig GetConfig()
        {
            return ideConfigHandle;
        }

        public bool GetCommandPending()
        {
            //Tracing.Log(Tracing.Debug," Command pending set to {0}", commandPending ? "true" : "false");
            return commandPending;
        }

        public void SetIdentifyInProgress(bool value)
        {
            identifyPending = value;
        }

        public bool GetIdentifyInProgress()
        {
            return identifyPending;
        }

        public ushort ReadDataPort()
        {
            return ((!)CommandBlock[0]).Read16();
        }

        public void WriteDataPort(ushort value)
        {
            ((!)CommandBlock[0]).Write16(value);
        }

        public byte ReadErrorPort()
        {
            return ((!)CommandBlock[1]).Read8();
        }

        public void WriteFeaturesPort(byte value)
        {
            ((!)CommandBlock[1]).Write8(value);
        }

        public byte ReadSectorCountPort()
        {
            return ((!)CommandBlock[2]).Read8();
        }

        public void WriteSectorCountPort(byte value)
        {
            ((!)CommandBlock[2]).Write8(value);
        }

        public byte ReadLBALowPort()
        {
            return ((!)CommandBlock[3]).Read8();
        }
        public void WriteLBALowPort(byte value)
        {
            ((!)CommandBlock[3]).Write8(value);
        }

        public byte ReadLBAMidPort()
        {
            return ((!)CommandBlock[4]).Read8();
        }
        public void WriteLBAMidPort(byte value)
        {
            ((!)CommandBlock[4]).Write8(value);
        }

        public byte ReadLBAHighPort()
        {
            return ((!)CommandBlock[5]).Read8();
        }
        public void WriteLBAHighPort(byte value)
        {
            ((!)CommandBlock[5]).Write8(value);
        }

        public byte ReadDeviceHeadPort()
        {
            return ((!)CommandBlock[6]).Read8();
        }

        public void WriteDeviceHeadPort(byte value)
        {
            ((!)CommandBlock[6]).Write8(value);
        }

        public byte ReadStatusPort()
        {
            return ((!)CommandBlock[7]).Read8();
        }

        public int ReadFullStatus()
        {
            byte nStatus = ReadAlternateStatusPort();
            if ((nStatus & (byte)ATA6.IdeStatus.ERR) > 0) {
                return (int)(nStatus | (((int)ReadErrorPort()) << 8));
            }
            return (int)nStatus;

        }

        public void WriteCommandPort(byte value)
        {
            ((!)CommandBlock[7]).Write8(value);
        }

        public byte ReadAlternateStatusPort()
        {
            return ((!)ControlBlock[2]).Read8();
        }

        public void WriteControlPort(byte value)
        {
            ((!)ControlBlock[2]).Write8(value);
        }

#if false
        public IoPort DataPort;
        public IoPort ErrorPort;
        public IoPort SectorCountPort;
        public IoPort LBAlowPort;
        public IoPort LBAmidPort;
        public IoPort LBAhighPort;
        public IoPort DeviceHeadPort;
        public IoPort StatusPort;
        public IoPort CommandPort;
#endif
        private IdeController(DiskResources! resources, string! instanceName)
        {
            DebugStub.Print("Entering IdeController\n");
            delay400ns = CalculateDelay400nsCount();

            this.ideConfigHandle = new IdeConfig(resources.irq,
                                                 resources.command,
                                                 resources.control,
                                                 true,
                                                 resources.dma,
                                                 this);

            this.instanceName = instanceName;
            IoPort[]! CommandBlock = this.CommandBlock = new IoPort[8];
            IoPort[]! ControlBlock = this.ControlBlock = new IoPort[8];
            ControllerNameInternal = String.Empty;

            IoPortRange commandPorts = resources.command;
            IoPortRange controlPorts = resources.control;

            CommandBlock[0] = commandPorts.PortAtOffset(0, 2, Access.ReadWrite); //Data Port 16bits
            CommandBlock[1] = commandPorts.PortAtOffset(1, 1, Access.ReadWrite); //Error Port
            CommandBlock[2] = commandPorts.PortAtOffset(2, 1, Access.ReadWrite); //SectorCount
            CommandBlock[3] = commandPorts.PortAtOffset(3, 1, Access.ReadWrite); //LBA low
            CommandBlock[4] = commandPorts.PortAtOffset(4, 1, Access.ReadWrite); //LBA mid
            CommandBlock[5] = commandPorts.PortAtOffset(5, 1, Access.ReadWrite); //LBA high
            CommandBlock[6] = commandPorts.PortAtOffset(6, 1, Access.ReadWrite); //DeviceHead
            CommandBlock[7] = commandPorts.PortAtOffset(7, 1, Access.ReadWrite); //Status & command
//
//          DataPort        = commandPorts.PortAtOffset(0, 2, Access.ReadWrite); //Data Port 16bits
//          ErrorPort       = commandPorts.PortAtOffset(1, 1, Access.Read);      //Error Port
//          SectorCountPort = commandPorts.PortAtOffset(2, 1, Access.ReadWrite); //SectorCount
//          LBAlowPort      = commandPorts.PortAtOffset(3, 1, Access.ReadWrite); //LBA low
//          LBAmidPort      = commandPorts.PortAtOffset(4, 1, Access.ReadWrite); //LBA mid
//          LBAhighPort     = commandPorts.PortAtOffset(5, 1, Access.ReadWrite); //LBA high
//          DeviceHeadPort  = commandPorts.PortAtOffset(6, 1, Access.ReadWrite); //DeviceHead
//          StatusPort      = commandPorts.PortAtOffset(7, 1, Access.Read);      //Status
//          CommandPort      commandPorts.PortAtOffset(7, 1, Access.Write);     //Command
//

            ControlBlock[2] = controlPorts.PortAtOffset(2, 2, Access.ReadWrite);
        }

        internal static IdeController! Create(DiskResources! resources, string! instanceName)
        {
            IdeController controller = new IdeController(resources, instanceName);

            controller.ResetController();
            IdeConfig! ideConfigHandle = controller.ideConfigHandle;

            if (ideConfigHandle.UseDma) {
                ideConfigHandle.BusMasterDma = new BusMasterDma(ideConfigHandle);
                controller.busMasterDmaAvailable = true;

                controller.ControllerNameInternal =
                        String.Format("controller at 0x{0:x4},BM@0x{1:x4},IRQ={2}",
                        ideConfigHandle.CommandBase,
                        ideConfigHandle.DmaBase,
                        ideConfigHandle.Interrupt);

                //
                // Set up Interrupt handling
                //
                ideConfigHandle.CommandEndEvent = new AutoResetEvent(false);
                ideConfigHandle.IdentifyEndEvent = new AutoResetEvent(false);


                ideConfigHandle.Irq = (!)ideConfigHandle.Interrupt.IrqAtOffset(0);
                ideConfigHandle.Irq.RegisterInterrupt();

                controller.irqWorker     = new Thread(new ThreadStart(controller.IrqWorkerMain));
                controller.irqWorkerStop = false;
                controller.irqWorker.Start();
                controller.initialized = true;
            }
            else {
                controller.busMasterDmaAvailable = false;
                controller.ControllerNameInternal = String.Format("PIO IDE controller at 0x{0:x4},{1:x4}",
                    ideConfigHandle.CommandBase, ideConfigHandle.ControlBase);
            }
            return controller;
        }

        public void Initialize()
        {
            Tracing.Log(Tracing.Debug,"Ide Controller Bus: initialize");
        }

        public void Finalize()
        {
            try {
                irqWorkerStop = true;
                ideConfigHandle.Irq.Pulse();    // Wake up irqWorker
                irqWorker.Join();
                ideConfigHandle.Irq.ReleaseInterrupt();
            }
            finally {
            }
        }

        public void ResetController()
        {
            bool iflag = PrivilegedGate.DisableInterrupts();
            try {
                // Post the software reset bit
                WriteControlPort(ATA6.DeviceControlSRST);

                // a 5ns delay is needed after issuing the reset and before
                // issuing the next command
                int spin = delay400ns * 30;
                Tracing.Log(Tracing.Debug," spin value for 5 microSeconds ="+spin);
                Thread.SpinWait(spin);

                WriteControlPort(0);

                // the spec says you need to wait 2ms here.
                // my experience has been > 100ms are needed to recognize Seagate drives
                Thread.Sleep(TimeSpan.FromMilliseconds(125));

                if (!PollBSY(false)) {
                    Tracing.Log(Tracing.Debug,
                                "IDE Controller: controller Reset Aborted, No Drives Present or responding.\n");
                }
                FindDisks();
            }
            finally {
                PrivilegedGate.RestoreInterrupts(iflag);
            }
        } //resetcontroller

        private void FindDisks()
        {
            // Device 0 now must post to the Error Register
            byte errorBits;
            errorBits = ReadErrorPort();
            //Tracing.Log(Tracing.Debug,"IDE controller: controller Reset finished, Error reg: 0x{0:x2}\n", errorBits);
            DebugStub.Print("  IDE Reset: {0:x2}\n", __arglist(errorBits));

            if ((errorBits & 0x1) > 0 && ReadLBALowPort() == 1) {
                DebugStub.Print("  IDE Master Signature {0:x2} {1:x2}\n",
                                __arglist(ReadLBAMidPort(), ReadLBAHighPort()));
                if (ReadLBAMidPort() == 0 && ReadLBAHighPort() == 0) {
                    DebugStub.Print("    IDE Found Master Disk\n");
                    ideDisk1Config = new IdeDiskConfig(ideConfigHandle, 0, instanceName, false);
                    //SOSP hack
                    DiskDriverControl.SetMasterDiskConfig(ideDisk1Config);

                }
                else if (ReadLBAMidPort() == 0x14 && ReadLBAHighPort() == 0xEB) {
                    DebugStub.Print("    IDE Found Master ATAPI16 Device\n");
                    ideDisk1Config = new IdeDiskConfig(ideConfigHandle, 0, instanceName, true);
                    //SOSP hack
                    DiskDriverControl.SetMasterDiskConfig(ideDisk1Config);
                }
                else {
                    DebugStub.Print("    IDE Unknown Master Signature {0:x2} {1:x2}\n",
                                    __arglist(ReadLBAMidPort(), ReadLBAHighPort()));
                    Tracing.Log(Tracing.Debug,"IDEcontroller: Master device has unknown signature 0x{0:x2} 0x{1:x2}.\n",
                        (UIntPtr) ReadLBAMidPort(), (UIntPtr) ReadLBAHighPort());
                }
            }
            else {
                DebugStub.Print("IDEcontroller: Master is missing\n");
                Tracing.Log(Tracing.Debug,"IDEcontroller: Master is missing");
            }

            //
            //  Slave Device
            //

            SelectDevice(1, false);
            if (!PollDRDY(true)) {
                DebugStub.Print("IDEcontroller: Slave is missing\n");
                Tracing.Log(Tracing.Debug,"IdeController: Slave is missing");
                return;
            }
            if (ReadSectorCountPort() == 1 && ReadLBALowPort() == 1) {
                if ((errorBits & 0x80) != 0) {
                    Tracing.Log(Tracing.Debug,"IdeController: Slave device reports failure.\n");
                }
                else {
                    DebugStub.Print("  IDE Slave Signature {0:x2} {1:x2}\n",
                                    __arglist(ReadLBAMidPort(), ReadLBAHighPort()));
                    if (ReadLBAMidPort() == 0 && ReadLBAHighPort() == 0) {
                        DebugStub.Print("    IDE Found Slave Disk\n");
                        ideDisk2Config = new IdeDiskConfig(ideConfigHandle, 1, instanceName, false);
                        //SOSP hack
                        DiskDriverControl.SetSlaveDiskConfig(ideDisk2Config);
                    }
                    else if (ReadLBAMidPort() == 0x14 && ReadLBAHighPort() == 0xEB) {
                        DebugStub.Print("    IDE Found Slave ATAPI16 Device\n");
                        ideDisk2Config = new IdeDiskConfig(ideConfigHandle, 1, instanceName, true);
                        //SOSP hack
                        DiskDriverControl.SetSlaveDiskConfig(ideDisk2Config);
                    }
                    else {
                        DebugStub.Print("    IDE Unknown Slave Signature {0:x2} {1:x2}\n",
                                        __arglist(ReadLBAMidPort(), ReadLBAHighPort()));
                        Tracing.Log(Tracing.Debug,"Controller: Slave device has unknown signature 0x{0:x2} 0x{1:x2}.\n",
                            (UIntPtr) ReadLBAMidPort(), (UIntPtr) ReadLBAHighPort());
                    }
                }
            }
            else {
                DebugStub.Print("IDEcontroller: Slave is missing\n");
                Tracing.Log(Tracing.Debug,"IdeController: Slave is missing.\n");
            }
        }

        private void IrqWorkerMain()
        {
            Tracing.Log(Tracing.Audit, "Start of worker thread.");
            byte status;
            int  countSpurious = 0;
            while (irqWorkerStop == false) {
                ideConfigHandle.Irq.WaitForInterrupt();

                bool iflag = PrivilegedGate.DisableInterrupts();
                bool doNotAck = false;
#if DEBUG_SHARED_IRQ
                //Tracing.Log(Tracing.Debug, "Interrupt signaled.");
#endif // DEBUG_SHARED_IRQ
                try {

                    Tracing.Log(Tracing.Debug,"wakeup {0:x}",
                        ideConfigHandle.BusMasterDma.InterruptHigh() ? (UIntPtr) 1 : (UIntPtr) 0 );

                    //
                    // "The IDE Driver is required to do a read of the [BM] controller status
                    //  register after receiving an interrupt. If the status register returns with the
                    //  Interrupt bit set then the driver knows the IDE device generated the interrupt
                    //  (important for shared interrupts)"

                    if (!ideConfigHandle.BusMasterDma.InterruptHigh()) {
                        //DebugStub.Break();
                        doNotAck = true ;
                    }
                    else {
                        if (CatchBug) {
                            Tracing.Log(Tracing.Debug,"CatchCount ={0}",(UIntPtr) CatchCount);
                            if (CatchCount-- <= 0) {
                                //DebugStub.Break();
                                 CatchBug = false;
                            }
                        }
                        status = ReadStatusPort();
                        if ((status & 0x1) > 0) {
                            Tracing.Log(Tracing.Debug,"ERROR: status={0}",(UIntPtr) status);

                            // Commented this out, this is preventing boot on some platforms
                            // DebugStub.Break(); //error
                        }
                        if (((status & (byte)ATA6.IdeStatus.DRDY) == 0) ||
                            ((status & (byte)ATA6.IdeStatus.ERR) != 0) )
                            {
                                ATA6.DebugQueryStatus(this);
                            }

                        //Tracing.Log(Tracing.Debug," IrqW status {0:x}",(UIntPtr) status);
                        ideConfigHandle.BusMasterDma.Disarm();

                        if (GetCommandPending()) {
                            SetCommandPending(false);
                            ideConfigHandle.CommandEndEvent.Set();
                            //Tracing.Log(Tracing.Debug,"setting CommandEndEvent");
                        }
                        else if (GetIdentifyInProgress()) {
                            SetIdentifyInProgress(false);
                            ideConfigHandle.IdentifyEndEvent.Set();
                        }
                        else {
                            Tracing.Log(Tracing.Debug,
                                        "   Spurious IDE interrupt on {0}\n",
                                        ControllerNameInternal);
                            if (countSpurious++ > 50) {
                                DebugStub.Break();
                            }
                        }
                    }
                }
                finally {
                    if (!doNotAck) {
                        ideConfigHandle.Irq.AckInterrupt();
#if DEBUG_SHARED_IRQ
                        Tracing.Log(Tracing.Debug,"ACKing {0}",
                        ControllerNameInternal);
#endif //DEBUG_SHARED_IRQ
                    }
                    else {
#if DEBUG_SHARED_IRQ
                        Tracing.Log(Tracing.Debug,"NACKing {0}",
                                    ControllerNameInternal);
#endif //DEBUG_SHARED_IRQ
                    }
                    PrivilegedGate.RestoreInterrupts(iflag);
                }
            }
        }
        public bool PollBSY(bool level)
        {
            Delay400ns();

            //TODO: FIXFIX PollLoopCount is a somewhat arbitrary number
            // > 2000 is needed to make SET_FEATURES work on real HW
            for (int i = 0; i < PollLoopCount; i++) {
                pollStatus = ReadStatusPort();
                if (level && (pollStatus & (byte)ATA6.IdeStatus.BSY) > 0) {

                    return true;
                }
                if (!level && (pollStatus & (byte)ATA6.IdeStatus.BSY) == 0) {
                    return true;
                }
            }
            Tracing.Log(Tracing.Debug," BSY failed to post in 400ns");
            return false;
        }

        public bool PollDRDY(bool level)
        {
            // TODO: FIXFIX PollLoopCount is a somewhat arbitrary number
            // > 2000 is needed to make SET_FEATURES work on real HW
            // level, true = high (1), false = low (0)
            for (int i = 0; i < PollLoopCount; i++) {
                byte pollStatus = ReadStatusPort();
                if (level && (pollStatus & (byte)ATA6.IdeStatus.DRDY) > 0) {
                    return true;
                }
                if (!level && (pollStatus & (byte)ATA6.IdeStatus.DRDY) == 0) {
                    return true;
                }
            }
            Tracing.Log(Tracing.Debug," DRDY failed to post in 400ns");
            return false;
        }

        public bool PollDRQ(bool level)
        {
            // level, true = high (1), false = low (0)

            Delay400ns();

            pollStatus = ReadStatusPort();
            if (level && (pollStatus & (byte)ATA6.IdeStatus.DRQ) > 0) {
                return true;
            }
            if (!level && (pollStatus & (byte)ATA6.IdeStatus.DRQ) == 0) {
                return true;
            }
            Tracing.Log(Tracing.Debug," DRQ failed to post in 400ns");
            return false;
        }

        public const byte IDE_FEATURE_ENABLE_WRITE_CACHE = 0x02;   // Enable write caching.
        public const byte IDE_FEATURE_SET_TRANSFER_MODE  = 0x03;   // Set the transfer mode.
        public const byte IDE_FEATURE_ENABLE_READ_AHEAD  = 0xAA;   // Enable read look ahead.
        public const byte IDE_FEATURE_DISABLE_READ_AHEAD = 0x55;   // Disable read look ahead.
        public const byte IDE_FEATURE_DISABLE_DEFAULTS   = 0x66;   // Disable revert to defaults on reset.

        public const byte IDE_MODE_SET_PIO_FLOW_CONTROL  = 0x08;   // page 176
        public const byte IDE_MODE_SET_ULTRA_DMA         = 0x40;   // page 176


        public bool IssueSet(IdeSet setType, ref IdentifyDeviceInformation ident)
        {
            ushort usFullStatus;
            byte nMode =0;

            bool iflag = PrivilegedGate.DisableInterrupts();
            if (!PollBSY(false)) {
                ATA6.DebugQueryStatus(this);
                DebugStub.Break();
            }
            try {
                switch (setType) {
                    case IdeSet.IDE_SET_MULTIPLE:
                        //AddTrace(GetPC(), ReadFullStatus());
                        //WriteSectorCountPort(m_nMaxBlockTransfer);
                        break;

                    case IdeSet.IDE_SET_MAX_UDMA:
                        nMode = (byte)((ident.UltraDmaSupported) ?
                                            ident.HighestUltraDmaMode : (byte) 0);
                        WriteFeaturesPort(IDE_FEATURE_SET_TRANSFER_MODE);
                        WriteSectorCountPort((byte)(IDE_MODE_SET_ULTRA_DMA | nMode));
                        WriteCommandPort((byte)ATA6.IdeCommand.SetFeature);
                        break;

                    case IdeSet.IDE_SET_READ_AHEAD:
                        //AddTrace(GetPC(), ReadFullStatus());
                        WriteFeaturesPort(IDE_FEATURE_ENABLE_READ_AHEAD);
                        break;

                    case IdeSet.IDE_UNSET_READ_AHEAD:
                        //AddTrace(GetPC(), ReadFullStatus());
                        WriteFeaturesPort(IDE_FEATURE_DISABLE_READ_AHEAD);
                        break;

                    case IdeSet.IDE_SET_WRITE_CACHE:
                        //AddTrace(GetPC(), ReadFullStatus());
                        WriteFeaturesPort(IDE_FEATURE_ENABLE_WRITE_CACHE);
                        break;

                    case IdeSet.IDE_SET_NO_REVERT:
                        //AddTrace(GetPC(), ReadFullStatus());
                        WriteFeaturesPort(IDE_FEATURE_DISABLE_DEFAULTS);
                        break;

                }

                WriteCommandPort((byte)ATA6.IdeCommand.SetFeature);
                if (!PollBSY(false)) {
                    ATA6.DebugQueryStatus(this);
                    DebugStub.Break();
                }
                byte status1 = ReadStatusPort();
                Tracing.Log(Tracing.Debug,"status={0}",(UIntPtr)status1);
            }
            finally {
                PrivilegedGate.RestoreInterrupts(iflag);
            }

            return true;
        }

        public void Delay400ns()
        {
            Thread.SpinWait(delay400ns);
        }

        public void SelectDevice(int device, bool atapi)
        {
            // REVIEW: should we be caching the last setting to avoid
            // lots of io port reading/writing?
            byte val = 0;

            if (device > 0) {
                val = ATA6.DriveSelect;
            }
            if (atapi) {
                val |= (byte) ATA6.IdeCommand.AtapiPacket;
            }
            // REVIEW:  what is the minimum requirement ?
            //PollBSY(false);  // wait for bus to be idle
            WriteDeviceHeadPort(val);
            //PollBSY(false);  // wait for bus to be idle
        }

        // TODO: This doesn't work, need to fix it some how.
        public SortedList Enumerate()
        {
            SortedList found = new SortedList();
            if (ideDisk1Config != null) {
                found.Add("/Disk1", ideDisk1Config);
            }
            if (ideDisk2Config != null) {
                found.Add("/Disk2", ideDisk2Config);
            }
            return found;
        }

        private static int CalculateDelay400nsCount()
        {
            ulong cyclesPerSecond = (ulong)Processor.CyclesPerSecond;
            ulong cycleCountStart;
            ulong cycleCountEnd;
            int spinCount = 1000;

            bool iflag = PrivilegedGate.DisableInterrupts();
            try {
                cycleCountStart = Processor.CycleCount;
                Thread.SpinWait(spinCount);
                cycleCountEnd   = Processor.CycleCount;
            }
            finally {
                PrivilegedGate.RestoreInterrupts(iflag);
            }

            ulong cycles   = cycleCountEnd - cycleCountStart;
            ulong iCount   = cycles / (ulong)spinCount;
            ulong cp100NS  = cyclesPerSecond / 10000000; //cycles per 100ns
            if (cp100NS < 1) {
                DebugStub.Print(" slow machine!! setting cp100NS to 1 \n");
                cp100NS = 1;
            }

            int delay400nsCount = (int) ((cp100NS/iCount) *4); //loop iterations needed for 400ns
            if (delay400nsCount < 100) {
                //delay400nsCount = 100;  //FIXFIX:  hack for VPC; CycleCount is not virtual!
                DebugStub.Print("  VPC: setting delay400 spin count to {0}\n",
                                __arglist(delay400nsCount));
            }

            // now check
            iflag = PrivilegedGate.DisableInterrupts();
            ulong s = Processor.CycleCount;
            Thread.SpinWait(delay400nsCount);
            ulong e = Processor.CycleCount;
            PrivilegedGate.RestoreInterrupts(iflag);

            DebugStub.Print("  CyclesPerSecond={0}, cyclesPer100ns={1},cyclesPerLoop={2} Delay loopCount={3}\n",
                            __arglist((ulong)cyclesPerSecond,
                                      (ulong)cp100NS,
                                      (ulong)iCount,
                                      (ulong)delay400nsCount));

            DebugStub.Print("  delay400 took {0} instructions or ~{1} nanoseconds\n",
                            __arglist((ulong)(e-s),
                                      (ulong)(((e-s)/cp100NS))* 100 ));

            return delay400nsCount;
        }
    }
}
