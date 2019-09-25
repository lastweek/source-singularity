///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AcpiTables.cs
//
//  Note:
//    Pages 95-104 of ACPI 3.0 Spec.

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using Microsoft.Singularity.Io;

    public enum FadtFlags : uint
    {
        WBINVD                               = 1u << 0,
        WBINVD_FLUSH                         = 1u << 1,
        PROC_C1                              = 1u << 2,
        P_LVL2_UP                            = 1u << 3,
        PWR_BUTTON                           = 1u << 4,
        SLP_BUTTON                           = 1u << 5,
        FIX_RTC                              = 1u << 6,
        RTC_S4                               = 1u << 7,
        TMR_VAL_EXT                          = 1u << 8,
        DCK_CAP                              = 1u << 9,
        RESET_REG_SUP                        = 1u << 10,
        SEALED_CASE                          = 1u << 11,
        HEADLESS                             = 1u << 12,
        CPU_SW_SLP                           = 1u << 13,
        PCI_EXP_WAK                          = 1u << 14,
        USE_PLATFORM_CLOCK                   = 1u << 15,
        S4_RTC_STS_VALID                     = 1u << 16,
        REMOTE_POWER_ON_CAPABLE              = 1u << 17,
        FORCE_APIC_CLUSTER_MODEL             = 1u << 18,
        FORCE_APIC_PHYSICAL_DESTINATION_MODE = 1u << 19,
    };

    public class Fadt
    {
        public const string Signature = "FACP";

        private IoMemory          region;
        private SystemTableHeader header;

        public Fadt(IoMemory region, SystemTableHeader header)
        {
            this.region = region;
            this.header = header;
        }

        private byte Read8(int offset)
        {
            return region.Read8(offset - (int) SystemTableHeader.Length);
        }

        private ushort Read16(int offset)
        {
            return region.Read16(offset - (int) SystemTableHeader.Length);
        }

        private uint Read32(int offset)
        {
            return region.Read32(offset - (int) SystemTableHeader.Length);
        }

        private ulong Read64(int offset)
        {
            return region.Read64(offset - (int) SystemTableHeader.Length);
        }

        private Gas ReadGas(int offset)
        {
            return new Gas(Read32(offset), Read64(offset + 4));
        }

        // --- BEGIN GENERATED REGION ---

        public uint FIRMWARE_CTRL        { get { return Read32(36); } }
        public uint DSDT                 { get { return Read32(40); } }
        public byte Preferred_PM_Profile { get { return Read8(45); } }
        public ushort SCI_INT            { get { return Read16(46); } }
        public uint SMI_CMD              { get { return Read32(48); } }
        public byte ACPI_ENABLE          { get { return Read8(52); } }
        public byte ACPI_DISABLE         { get { return Read8(53); } }
        public byte S4BIOS_REQ           { get { return Read8(54); } }
        public byte PSTATE_CNT           { get { return Read8(55); } }
        public uint PM1a_EVT_BLK         { get { return Read32(56); } }
        public uint PM1b_EVT_BLK         { get { return Read32(60); } }
        public uint PM1a_CNT_BLK         { get { return Read32(64); } }
        public uint PM1b_CNT_BLK         { get { return Read32(68); } }
        public uint PM2_CNT_BLK          { get { return Read32(72); } }
        public uint PM_TMR_BLK           { get { return Read32(76); } }
        public uint GPE0_BLK             { get { return Read32(80); } }
        public uint GPE1_BLK             { get { return Read32(84); } }
        public byte PM1_EVT_LEN          { get { return Read8(88); } }
        public byte PM1_CNT_LEN          { get { return Read8(89); } }
        public byte PM2_CNT_LEN          { get { return Read8(90); } }
        public byte PM_TMR_LEN           { get { return Read8(91); } }
        public byte GPE0_BLK_LEN         { get { return Read8(92); } }
        public byte GPE1_BLK_LEN         { get { return Read8(93); } }
        public byte GPE1_BASE            { get { return Read8(94); } }
        public byte CST_CNT              { get { return Read8(95); } }
        public ushort P_LVL2_LAT         { get { return Read16(96); } }
        public ushort P_LVL3_LAT         { get { return Read16(98); } }
        public ushort FLUSH_SIZE         { get { return Read16(100); } }
        public ushort FLUSH_STRIDE       { get { return Read16(102); } }
        public byte DUTY_OFFSET          { get { return Read8(104); } }
        public byte DUTY_WIDTH           { get { return Read8(105); } }
        public byte DAY_ALRM             { get { return Read8(106); } }
        public byte MON_ALRM             { get { return Read8(107); } }
        public byte CENTURY              { get { return Read8(108); } }
        public ushort IAPC_BOOT_ARCH     { get { return Read16(109); } }
        public uint Flags                { get { return Read32(112); } }
        public Gas RESET_REG             { get { return ReadGas(116); } }
        public byte RESET_VALUE          { get { return Read8(128); } }
        public ulong X_FIRMWARE_CTRL     { get { return Read64(132); } }
        public ulong X_DSDT              { get { return Read64(140); } }
        public Gas X_PM1a_EVT_BLK        { get { return ReadGas(148); } }
        public Gas X_PM1b_EVT_BLK        { get { return ReadGas(160); } }
        public Gas X_PM1a_CNT_BLK        { get { return ReadGas(172); } }
        public Gas X_PM1b_CNT_BLK        { get { return ReadGas(184); } }
        public Gas X_PM2_CNT_BLK         { get { return ReadGas(196); } }
        public Gas X_PM_TMR_BLK          { get { return ReadGas(208); } }
        public Gas X_GPE0_BLK            { get { return ReadGas(220); } }
        public Gas X_GPE1_BLK            { get { return ReadGas(232); } }

        // --- END GENERATED REGION ---

        public static Fadt Create(SystemTableHeader header)
        {
            IoMemory region = IoMemory.MapPhysicalMemory(header.PostHeaderAddress,
                                                         header.PostHeaderLength,
                                                         true, false);
            int sum = (header.Checksum + AcpiChecksum.Compute(region)) & 0xff;
            if (sum != 0) {
                return null;
            }
            return new Fadt(region, header);
        }
    }
}
