////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ATA6.cs
//
//  Base Classes and Interfaces for interacting with ATA
//
//  References used:
//  "AT Attachment with Packet Interface with Extension 6 (ATA/ATAPI-6-)",
//           ISO Working Group T13, http://www.t13.org/
//

using System;
using System.Text;
using System.Threading;
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Drivers.IDE;
using Microsoft.Singularity.V1.Services;
using Microsoft.Contracts;

namespace Microsoft.Singularity.Drivers.IDE
{
    [CLSCompliant(false)]
    public class IdeDiskConfig
    {
        public IdeConfig ControllerConfig;
        public byte     DiskNumber;
        public bool     Atapi;
        public String!  DeviceName;
        public String!  Id;

        public IdeDiskConfig(IdeConfig config, byte num, String! deviceName, bool atapi)
        {
            ControllerConfig = config;
            DiskNumber = num;
            Atapi = atapi;
            Id = "/ata/disk";
            DeviceName = deviceName;
            // Used to be "/dev/disk0", but now we use the instance name.

            base();
        }
    }

    public class IdeConfig
    {
        public IoIrqRange       Interrupt;
        public bool             UseDma;
        public IoPortRange      DmaBase;
        public IoPortRange      CommandBase;
        public IoPortRange      ControlBase;
        public IdeController!   IdeController;
        public BusMasterDma     BusMasterDma;
        public IoIrq/*[!]*/     Irq;
        public AutoResetEvent/*[!]*/ CommandEndEvent;
        public AutoResetEvent/*[!]*/ IdentifyEndEvent;
        public String           Id;

        public IdeConfig(IoIrqRange! interrupt,
                         IoPortRange! command,
                         IoPortRange! control,
                         bool useDma,
                         IoPortRange! bmBaseAddr,
                         [Delayed]
                         IdeController! ideController
            )
        {
            Interrupt       = interrupt;
            CommandBase     = command;
            ControlBase     = control;
            UseDma          = useDma;
            DmaBase         = bmBaseAddr;
            IdeController   = ideController;

            Id = "/ata/controller";
            Tracing.Log(Tracing.Debug,"IdeConfig: INT={1} cmd={2:x4}, ctrl={3:x4}, DMA@{4:x4}\n",
                        (UIntPtr)interrupt.Irq,
                        (UIntPtr)command.Port,
                        (UIntPtr)control.Port,
                        (UIntPtr)bmBaseAddr.Port);
        }
    }

    [CLSCompliant(false)]
    public struct IdentifyDeviceInformation
        // Information Returned to host via the IdentifyDeviceInformation command
    {
        public bool     RemovableMediaDevice;   // Word 0, Bit 7
        public bool     RemovableController;    // Word 0, Bit 6
        public ushort   CylinderCount;          // word 1
        public ushort   HeadCount;              // word 3
        public ushort   SectorCountPerTrack;    // Word 6
        public string   SerialNumber;           // Words 10 to 19
        public ushort   NumberOfBytesAvailInVendorCommand; // Word 22
        public string   FirmwareRevision;       // Words 23 to 26
        public string   ModelNumber;            // Words 27 to 47
        public bool     SupportsMultiple;       // Word 47, bits 7 to 0 == 0
        public ushort   MaximumMultipleSectorCount; // Word 47, bits 7 to 0

        public bool     StandbyTimer;           // Word 49, bit 13

        public bool     IORDYSupported;         // Word 49, bit 11
        public bool     IORDYDisableable;       // Word 49, bit 10
        public bool     LBASupported;           // Word 49, bit 9
        public bool     DMASupported;           // Word 49, bit 8

        public bool     Word88Valid;            // Word 53, bit 2
        public bool     UltraDmaSupported;      // Word 53, bit 2 (same)
        public bool     Words64to70Valid;       // Word 53, bit 1
        public bool     Words54to58Valid;       // Word 53, bit 0

        // Words 54-58 are valid if word 53, bit 0 is set.

        public ushort   CurrentLogicalCylinderCount;    // Word 54
        public ushort   CurrentLogicalHeadCount;        // Word 55
        public ushort   CurrentLogicalSectorCount;      // Word 56
        public uint     CurrentCapacityInSectors;       // Word 57-58
        public bool     MultipleSectorSettingValid;     // Word 59, bits 8
        public ushort   CurrentSectorCountPerInterrupt; // Word 59
        public uint     TotalAddressableSectors;        // Word 60-61
        public ushort   MultiwordDMATransferMode;       // Word 63, 15-8
        public ushort   MultiwordDMATransferModes;      // Word 63, 7-0

        // Words 64-70 are valid if word 53, bit 1 is set.

        public ushort   PIODMATransferModes; // Word 64, bits 7-0
        public ushort   MinimumMultiwordDMACycleTime; // in nanoseconds Word 65
        public ushort   RecommendedMultiwordDMACycleTime; // in nanoseconds Word 66
        public ushort   MinimumPIOCycleTimeWithFlowControl; // in nanoseconds Word 67
        public ushort   MinimumPIOCycleTimeWithIORDY; // in nanoseconds Word 68

        public ushort   QueueDepth; // word 75,  value == depth-1
        public ushort   MajorVersion;  //word 80
        public ushort   MinorVersion;  //word 81

        public ushort   FeatureSet1Supported;
        public bool     NOPSupported;  // word 82, bit 14
        public bool     ReadBufferSupported;  // word 82, bit 13
        public bool     WriteBufferSupported;  // word 82, bit 12
        public bool     HostProtectedAreaSupported;  // word 82, bit 10
        public bool     DeviceResetSupported;  // word 82, bit 9
        public bool     ServiceInterruptSupported;  // word 82, bit 8
        public bool     ReleaseInterruptSupported;  // word 82, bit 7
        public bool     LookAheadSupported;  // word 82, bit 6
        public bool     WriteCacheSupported;  // word 82, bit 5
        public bool     PacketSupported;  // word 82, bit 4
        public bool     PowerManagementSupported;  // word 82, bit 3
        public bool     RemovableMediaSupported;  // word 82, bit 2
        public bool     SecurityModeSupported;  // word 82, bit 1
        public bool     SmartSupported;  // word 82, bit 0

        public ushort   FeatureSet2Supported;
        public bool     FlushCacheExtSupported;  // word 83, bit 13
        public bool     FlushCacheSupported;  // word 83, bit 12
        public bool     DeviceConfigurationOverlaySupported;  // word 83, bit 11
        public bool     LBA48Supported;  // word 83, bit 10
        public bool     AutomaticAcousticManagementSupported;  // word 83, bit 9
        public bool     SetMaxSecuritySupported;  // word 83, bit 8
        public bool     AddressOffsetrAreaBootSupported;  // word 83, bit 7
        public bool     SetFeaturesSupported;  // word 83, bit 6
        public bool     PowerUpInStandbySupported;  // word 83, bit 5
        public bool     RemovableMediaStatusNotificationSupported;  // word 83, bit 4
        public bool     APMSupported;  // word 83, bit 3
        public bool     CFASupported;  // word 83, bit 2
        public bool     QueuedDMASupported;  // word 83, bit 1
        public bool     DownloadMicrocodeSupported;  // word 83, bit 0

        public ushort   FeatureSet3Supported;
        public bool     GeneralPurposeLoggingSupported;  // word 83, bit 5
        public bool     MediaCardPssThroughSupported;  // word 83, bit 3
        public bool     MediaSerialNumberSupported;  // word 83, bit 2
        public bool     SmartSelfTestSupported;  // word 83, bit 1
        public bool     SmartErrorLogSupported;  // word 83, bit 0

        public bool     EnabledDataValid;   // word 87, bits 15,14 (0x8000)

        public ushort   FeatureSet1Enabled;
        public bool     NOPEnabled;  // word 85, bit 14
        public bool     ReadBufferEnabled;  // word 85, bit 13
        public bool     WriteBufferEnabled;  // word 85, bit 12
        public bool     HostProtectedAreaEnabled;  // word 85, bit 10
        public bool     DeviceResetEnabled;  // word 85, bit 9
        public bool     ServiceInterruptEnabled;  // word 85, bit 8
        public bool     ReleaseInterruptEnabled;  // word 85, bit 7
        public bool     LookAheadEnabled;  // word 85, bit 6
        public bool     WriteCacheEnabled;  // word 85, bit 5
        public bool     PacketEnabled;  // word 85, bit 4
        public bool     PowerManagementEnabled;  // word 85, bit 3
        public bool     RemovableMediaEnabled;  // word 85, bit 2
        public bool     SecurityModeEnabled;  // word 85, bit 1
        public bool     SmartEnabled;  // word 85, bit 0

        public ushort   FeatureSet2Enabled;
        public bool     FlushCacheExtEnabled;  // word 86, bit 13
        public bool     FlushCacheEnabled;  // word 86, bit 12
        public bool     DeviceConfigurationOverlayEnabled;  // word 86, bit 11
        public bool     LBA48Enabled;  // word 86, bit 10
        public bool     AutomaticAcousticManagementEnabled;  // word 86, bit 9
        public bool     SetMaxSecurityEnabled;  // word 86, bit 8
        public bool     AddressOffsetrAreaBootEnabled;  // word 86, bit 7
        public bool     SetFeaturesEnabled;  // word 86, bit 6
        public bool     PowerUpInStandbyEnabled;  // word 86, bit 5
        public bool     RemovableMediaStatusNotificationEnabled;  // word 86, bit 4
        public bool     APMEnabled;  // word 86, bit 3
        public bool     CFAEnabled;  // word 86, bit 2
        public bool     QueuedDMAEnabled;  // word 86, bit 1
        public bool     DownloadMicrocodeEnabled;  // word 86, bit 0

        public ushort   FeatureSet3Enabled;
        public bool     GeneralPurposeLoggingEnabled;  // word 87, bit 5
        public bool     MediaCardPssThroughEnabled;  // word 87, bit 3
        public bool     MediaSerialNumberEnabled;  // word 87, bit 2
        public bool     SmartSelfTestEnabled;  // word 87, bit 1
        public bool     SmartErrorLogEnabled;  // word 87, bit 0


        //word 88 UltraDMA
        public ushort     UltraDmaModes;          //word 88
        public byte     HighestUltraDmaMode;    // Highest UDMA mode supported;
        public bool     UltraDmaMode5Selected;  //word 88. bit 13
        public bool     UltraDmaMode4Selected;  //word 88. bit 12
        public bool     UltraDmaMode3Selected;  //word 88. bit 11
        public bool     UltraDmaMode2Selected;  //word 88. bit 10
        public bool     UltraDmaMode1Selected;  //word 88. bit 9
        public bool     UltraDmaMode0Selected;  //word 88. bit 8

        public bool     UltraDmaMode5Supported;  //word 88. bit 5
        public bool     UltraDmaMode4Supported;  //word 88. bit 4
        public bool     UltraDmaMode3Supported;  //word 88. bit 3
        public bool     UltraDmaMode2Supported;  //word 88. bit 2
        public bool     UltraDmaMode1Supported;  //word 88. bit 1
        public bool     UltraDmaMode0Supported;  //word 88. bit 0

        public ulong    MaxLBASectors;           //words 100-103
   }

#region ATA6
    public class ATA6
    {
        internal static string WordsToString(ushort[]! DriveData, int Start, int End)
        {
            int iter;
            int length = End - Start;
            ASCIIEncoding xlate = new ASCIIEncoding();
            byte[] tempBuffer = new byte[(End - Start) * 2];

            for (iter = 0; iter < length; iter++) {
                tempBuffer[iter * 2 + 1] = (byte)(DriveData[Start + iter] & (ushort)0xFF);
                tempBuffer[iter * 2] = (byte)((DriveData[Start + iter] >> 8) & (ushort)0xFF);
            }

            string ret =  xlate.GetString(tempBuffer);

            if (ret != null) {
                ret = ret.Trim();
            }

            return ret;
        }

        static byte HighestBitSet(ushort uiBits)
        {
            ushort uiMask = 0x80;
            for (ushort nBit = 8; nBit > 0; nBit--, uiMask >>= 1) {
                if ((uiBits & uiMask) > 0) {
                    return (byte)nBit;
                }
            }
            return 0;
        }

        //public static uint    MAX_SUPPORTED_SECTORS = 2048 * 128;
        //public static uint    MAX_SUPPORTED_SECTORS = 16383 * 16 * 63;

        public static IdentifyDeviceInformation ParseIdentifyInformation(ushort[]! DriveData)
        {
            IdentifyDeviceInformation temp = new IdentifyDeviceInformation();
            temp.RemovableMediaDevice = (DriveData[0] & (1<<7)) > 0;
            temp.CylinderCount = DriveData[1];
            temp.HeadCount = DriveData[3];
            temp.SectorCountPerTrack = DriveData[6];
            temp.SerialNumber = WordsToString(DriveData, 10, 19);
            temp.NumberOfBytesAvailInVendorCommand = DriveData[22];
            temp.FirmwareRevision = WordsToString(DriveData, 23, 26);
            temp.ModelNumber = WordsToString(DriveData, 27, 46);
            if ((DriveData[47] & (0xFF)) == 0) {
                temp.SupportsMultiple = false;
            }
            else {
                temp.SupportsMultiple = true;
                temp.MaximumMultipleSectorCount = (ushort)(DriveData[47] & 0xFF);
            }

            temp.StandbyTimer      = ((DriveData[49] & (1 << 13))) > 0;
            temp.IORDYSupported    = ((DriveData[49] & (1 << 11))) > 0;
            temp.IORDYDisableable  = ((DriveData[49] & (1 << 10))) > 0;
            temp.LBASupported      = ((DriveData[49] & (1 << 9)))  > 0;
            temp.DMASupported      = ((DriveData[49] & (1 << 8)))  > 0;
            //UltraDMA supported
            temp.Word88Valid       = ((DriveData[53] & (1 << 2)))  > 0;
            temp.UltraDmaSupported = temp.Word88Valid;
            //this bit should always be true unless device is CFA or PCMCIA
            temp.Words64to70Valid  = ((DriveData[53] & (1 << 1)))  > 0;
            //obsolete
            temp.Words54to58Valid = ((DriveData[53] & (1 << 0)))  > 0;

            // word 59:  multiple sector setting
            temp.MultipleSectorSettingValid = (DriveData[59] & (1 << 8)) > 0;
            temp.CurrentSectorCountPerInterrupt = (ushort)(DriveData[59] & 0xFF);

            // words 60,61: Total # of addressable sectors (+1)
            temp.TotalAddressableSectors = ((uint)DriveData[61] << 16) | (uint)DriveData[60];
#if obsolete
            if (temp.TotalAddressableSectors > MAX_SUPPORTED_SECTORS) {
                temp.TotalAddressableSectors = MAX_SUPPORTED_SECTORS;
            }
#endif
            // word 63:  should be 0 if UltraDMA is supported
            // bit 10: MDMA mode 2 selected
            // bit 09: MDMA mode 1 selected
            // bit 08: MDMA mode 0 selected

            // bit 02: MDMA mode 2 supported
            // bit 01: MDMA mode 1 supported
            // bit 00: MDMA mode 0 supported

            temp.MultiwordDMATransferMode = (ushort)((DriveData[63] & 0xFF00) >> 8);
            temp.MultiwordDMATransferModes = (ushort)(DriveData[63] & 0xFF);

            temp.PIODMATransferModes = (ushort)(DriveData[64] & 0xFF);
            temp.MinimumMultiwordDMACycleTime = DriveData[65];
            temp.RecommendedMultiwordDMACycleTime = DriveData[66];
            temp.MinimumPIOCycleTimeWithFlowControl = DriveData[67];
            temp.MinimumPIOCycleTimeWithIORDY = DriveData[68];

            // value == maximum queue depth -1  (max = 31 +1)
            temp.QueueDepth = (ushort)(DriveData[75] & 0x1F);

            temp.MajorVersion = DriveData[80];
            temp.MinorVersion = DriveData[81];

            //Feature sets
            temp.FeatureSet1Supported = DriveData[82];
            temp.FeatureSet2Supported = DriveData[83];
            temp.FeatureSet3Supported = DriveData[84];
            temp.FeatureSet1Enabled   = DriveData[85];
            temp.FeatureSet2Enabled   = DriveData[86];
            temp.FeatureSet3Enabled   = DriveData[87];

            temp.LBA48Supported       = ((DriveData[83] & (1 << 10))) > 0;
            temp.LBA48Enabled         = ((DriveData[86] & (1 << 10))) > 0;

            temp.QueuedDMASupported   = ((DriveData[83] & (1 << 1)))  > 0;
            temp.QueuedDMAEnabled     = ((DriveData[86] & (1 << 1)))  > 0;

            if (temp.UltraDmaSupported) {
                temp.UltraDmaModes = DriveData[88];
                temp.HighestUltraDmaMode =
                    (byte) (HighestBitSet((ushort)(temp.UltraDmaModes & 0x3f)) - (byte) 1);
            }
            
            if (temp.LBA48Supported) {
                temp.MaxLBASectors =  ((ulong)DriveData[103] << 48) 
                                    | ((ulong)DriveData[102] << 32)
                                    | ((ulong)DriveData[101] << 16)
                                    |  (ulong)DriveData[100]; 
                DebugStub.WriteLine("Disk Device supports LBA 48\n");
                DebugStub.WriteLine("Total LBA sectors ={0}",__arglist(temp.MaxLBASectors));
                //controller.WriteCommandPort( (byte) ATA6.IdeCommand.ReadNativeMaxAddressExt);
                //controller.Delay400ns(); 
                //DebugStub.WriteLine("ReadNativeMaxAddressExt:");
                //ShowOffsetAndCount();  
            }
            else {
                temp.MaxLBASectors =  temp.TotalAddressableSectors; 
            }

            if  (temp.UltraDmaSupported) {
                DebugStub.WriteLine("Disk Device supports Ultra DMA modes={0:x4},highest={1}",
                                    __arglist(temp.UltraDmaModes,temp.HighestUltraDmaMode));
            }

            return temp;
        }

        public static
        IdentifyDeviceInformation GetDeviceIdentification(IdeController! controller,
                                                          int devsel, bool atapi)
        {
            ushort[] identifyData = new ushort[256];

            if (!controller.PollBSY(false)) {
                // should fail here.
            }
            controller.SelectDevice(devsel, atapi);

            //DebugStub.Print(" IDE GetDeviceIdentification starting\n");
            bool iflag = PrivilegedGate.DisableInterrupts();
            try {
                controller.SetIdentifyInProgress(true);
                controller.PollDRDY(true);
                byte cmd = (atapi)? (byte)IdeCommand.IdentifyPacketDevice:
                                    (byte)IdeCommand.IdentifyDevice;
                controller.WriteCommandPort(cmd); //will post interrupt
                controller.Delay400ns();
                Tracing.Log(Tracing.Debug,"status={0}",(UIntPtr) controller.ReadFullStatus());
                controller.PollDRDY(true); // Device indicates ready.
            }
            finally {
                PrivilegedGate.RestoreInterrupts(iflag);
            }

            IdeConfig config = controller.GetConfig();
            bool success = (config != null) && config.IdentifyEndEvent.WaitOne(TimeSpan.FromMilliseconds(250));

            if (!success) {
                //DebugStub.Break();
                Tracing.Log(Tracing.Debug," IDE GetDeviceIdentification did NOT receive  interrupt\n");
                controller.SetIdentifyInProgress(false);
            }

            //DebugStub.Print(" IDE GetDeviceIdentification received interrupt\n");

            // XXX: We should check for an Error condition here.
            // XXX: We should check for the ATAPI signature here.

            byte statusBits = controller.ReadAlternateStatusPort();
            if ((statusBits & (byte)ATA6.IdeStatus.ERR) > 0) {
                Tracing.Log(Tracing.Debug,"ERR reported in status after IdentifyDevice!\n");
                DebugStub.Break();
            }

            for (int i = 0; i < 256; i++) {
                identifyData[i] = controller.ReadDataPort();
            }

            IdentifyDeviceInformation ident = ParseIdentifyInformation(identifyData);

////        if (atapi)
            if (ident.ModelNumber == "Virtual CD") // SECTOR_SIZE is actually 2048
                ident.MaxLBASectors = 650 * 1024 * 1024 / IdeRequest.SECTOR_SIZE;
                                                   // for IdeDisk::ReadWrite tests
            return ident;
        }

        public static void DebugQueryStatus(IdeController! controller)
        {
            byte statusBits = controller.ReadAlternateStatusPort();
            byte errorBits = controller.ReadErrorPort();

            Tracing.Log(Tracing.Debug,"ATAcontroller: Status Register({0:x2}): ",statusBits);
            Tracing.Log(Tracing.Debug, ((statusBits & (byte) ATA6.IdeStatus.BSY) > 0)
                        ? "BSY " : "!bsy ");
            Tracing.Log(Tracing.Debug, ((statusBits & (byte)ATA6.IdeStatus.DRDY) > 0)
                        ? "DRDY " : "!drdy ");
            Tracing.Log(Tracing.Debug, ((statusBits & (byte)ATA6.IdeStatus.DWF) > 0)
                        ? "DWF " : "!dwf ");
            Tracing.Log(Tracing.Debug, ((statusBits & (byte)ATA6.IdeStatus.DSC) > 0)
                        ? "DSC " : "!dsc ");
            Tracing.Log(Tracing.Debug, ((statusBits & (byte)ATA6.IdeStatus.DRQ) > 0)
                        ? "DRQ " : "!drq ");
            Tracing.Log(Tracing.Debug, ((statusBits & (byte)ATA6.IdeStatus.CORR) > 0)
                        ? "CORR " : "!corr ");
            Tracing.Log(Tracing.Debug, ((statusBits & (byte)ATA6.IdeStatus.IDX) > 0)
                        ? "IDX " : "!idx");
            Tracing.Log(Tracing.Debug, ((statusBits & (byte)ATA6.IdeStatus.ERR) > 0)
                        ? "ERR " : "!err ");
            Tracing.Log(Tracing.Debug,"\n");

            Tracing.Log(Tracing.Debug,"ATAcontroller: Error Register:({0:x2}): ",errorBits);
            Tracing.Log(Tracing.Debug, ((errorBits & (byte)ATA6.IdeError.UNC) > 0)
                        ? "UNC " : "!unc ");
            Tracing.Log(Tracing.Debug, ((errorBits & (byte)ATA6.IdeError.MC) > 0)
                        ? "MC " : "!mc ");
            Tracing.Log(Tracing.Debug, ((errorBits & (byte)ATA6.IdeError.IDNF) > 0)
                        ? "IDNF " : "!idnf ");
            Tracing.Log(Tracing.Debug, ((errorBits & (byte)ATA6.IdeError.ABRT) > 0)
                        ? "ABRT " : "!abrt ");
            Tracing.Log(Tracing.Debug, ((errorBits & (byte)ATA6.IdeError.MCR) > 0)
                        ? "MCR " : "!mcr ");
            Tracing.Log(Tracing.Debug, ((errorBits & (byte)ATA6.IdeError.TK0NF) > 0)
                        ? "TK0NF " : "!tk0nf ");
            Tracing.Log(Tracing.Debug, ((errorBits & (byte)ATA6.IdeError.AMNF) > 0)
                        ? "AMNF " : "!amnf ");
            Tracing.Log(Tracing.Debug,"\n");

            ushort lbaLow = controller.ReadLBALowPort();
            ushort lbaMid = controller.ReadLBAMidPort();
            ushort lbaHigh = controller.ReadLBAHighPort();
            Tracing.Log(Tracing.Debug,"LBA={0:x2},{1:x2},{2:x2}\n",
                        (UIntPtr)lbaHigh, (UIntPtr)lbaMid, (UIntPtr)lbaLow);
        }

        public enum IdeCommand
        {
            Nop                     = 0x00,
            Read                    = 0x20,
            ReadNoRetry             = 0x21,
            ReadLong                = 0x22,
            ReadLongNoRetry         = 0x23,
            ReadDmaExt              = 0x25,
            ReadDmaQueuedExt        = 0x26,
            ReadNativeMaxAddressExt = 0x27, 
            Write                   = 0x30,
            WriteNoRetry            = 0x31,
            WriteLong               = 0x32,
            WriteLongNoRetry        = 0x33,
            WriteDmaExt             = 0x35,
            WriteDmaQueuedExt       = 0x36,
            WriteVerify             = 0x3C,
            ReadVerify              = 0x40,
            ReadVerifyNoRetry       = 0x41,
            FormatTrack             = 0x50,
            Seek                    = 0x70,
            ExecuteDeviceDiagnostic = 0x90,
            InitializeDeviceParameters = 0x91,
            DownloadMicrocode       = 0x92,
            AtapiPacket             = 0xA0,
            IdentifyPacketDevice    = 0xA1,
            ReadMultiple            = 0xC4,
            WriteMultiple           = 0xC5,
            SetMultipleMode         = 0xC6,
            ReadDmaQueued           = 0xC7,
            ReadDmaRetry            = 0xC8,
            ReadDmaNoRetry          = 0xC9,
            WriteDmaRetry           = 0xCA,
            WriteDmaNoRetry         = 0xCB,
            WriteDmaQueued          = 0xCC,
            AcknowledgeMediaChange  = 0xDB,
            BootPostBoot            = 0xDC,
            BootPreBoot             = 0xDD,
            DoorLock                = 0xDE,
            DoorUnLock              = 0xDF,
            ReadBuffer              = 0xE4,
            WriteBuffer             = 0xE8,
            WriteSame               = 0xE9,
            IdentifyDevice          = 0xEC,
            MediaEject              = 0xED,
            SetFeature              = 0xEF,
        }

        public enum Atapi : byte
        {
            DMA   = 0x01,
            Read  = 0x28,
        }

        public enum IdeStatus : byte
        {
            BSY   = 0x80,
            DRDY  = 0x40,
            DWF   = 0x20,
            DSC   = 0x10,
            DRQ   = 0x08,
            CORR  = 0x04,
            IDX   = 0x02,
            ERR   = 0x01,
        }
        public enum IdeError
        {
            UNC        = 0x40,
            MC         = 0x20,
            IDNF       = 0x10,
            ABRT       = 0x08,
            MCR        = 0x04,
            TK0NF      = 0x02,
            AMNF       = 0x01,
        }
        public const byte DriveSelect = 0x10; // Low = Master, High = Slave

        public const bool High = true;
        public const bool Low = false;

        public const byte DeviceControlSRST = 0x04;
        public const byte DeviceControlnIEN = 0x02; // note active low
        
        // High Order Bit, used to read LBA 48 "previous" values in low,mid,and high port queues
        public const byte DeviceControlHOB  = 0x80;
    }
#endregion
}
