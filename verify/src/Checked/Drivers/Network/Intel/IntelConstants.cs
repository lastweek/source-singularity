///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

namespace Microsoft.Singularity.Drivers.Network.Intel
{
    //
    // Memory Mapped Register offsets
    //
    internal struct Register
    {
        // control / status
        internal const uint CTRL                = 0x0000;
        internal const uint STATUS              = 0x0008;

        // EEPROM access
        internal const uint EECD                = 0x0010;
        internal const uint EERD                = 0x0014;
        internal const uint FLA                 = 0x001c;

        // Device controls
        internal const uint CTRL_EXT            = 0x0018;
        internal const uint MDIC                = 0x0020;
        internal const uint FCAL                = 0x0028;
        internal const uint FCAH                = 0x002C;
        internal const uint FCT                 = 0x0030;
        internal const uint VET                 = 0x0038;
        internal const uint FCTTV               = 0x0170;
        internal const uint TXCW                = 0x0178;
        internal const uint RXCW                = 0x0180;
        internal const uint LED_CTRL            = 0x0e00;

        // DMA
        internal const uint PBA                 = 0x1000;

        // Interrupts
        internal const uint ICR                 = 0x00c0;
        internal const uint ITR                 = 0x00c4;
        internal const uint ICS                 = 0x00c8;
        internal const uint IMS                 = 0x00d0;
        internal const uint IMC                 = 0x00d8;

        // Receive
        internal const uint RECV_CTRL           = 0x0100;

        internal const uint FLOW_CTRL_RECV_LO   = 0x2160;
        internal const uint FLOW_CTRL_RECV_HI   = 0x2168;
        internal const uint RECV_DESC_BASE_LO   = 0x2800;
        internal const uint RECV_DESC_BASE_HI   = 0x2804;
        internal const uint RECV_DESC_LENGTH    = 0x2808;
        internal const uint RECV_DESC_HEAD      = 0x2810;
        internal const uint RECV_DESC_TAIL      = 0x2818;
        internal const uint RECV_DELAY_TIMER    = 0x2820;
        internal const uint RECV_INT_ABS_TIMER  = 0x282c;
        internal const uint RECV_SML_PKT_INT    = 0x2c00;

        internal const uint RECV_CHECKSUM       = 0x5000;

        internal const uint MTA_START           = 0x5200;

        internal const uint RAL0                = 0x5400;
        internal const uint RAH0                = 0x5404;

        // Transmit
        internal const uint TSMT_CTRL           = 0x0400;
        internal const uint TSMT_IPG            = 0x0410;
        internal const uint TSMT_IFS_THROTTLE   = 0x0458;
        internal const uint TSMT_DESC_BASE_LO   = 0x3800;
        internal const uint TSMT_DESC_BASE_HI   = 0x3804;
        internal const uint TSMT_DESC_LENGTH    = 0x3808;
        internal const uint TSMT_DESC_HEAD      = 0x3810;
        internal const uint TSMT_DESC_TAIL      = 0x3818;
        internal const uint TSMT_INT_DELAY      = 0x3820;

        // stats
        internal const uint RX_ERR_COUNT        = 0x400c;
        internal const uint TOTAL_RECV_PACKETS  = 0x40d0;
        internal const uint TOTAL_TSMT_PACKETS  = 0x40d4;
    }

    // Bits for control reg
    internal struct CtrlBits
    {
        internal const uint FD                  = 1u << 0;
        internal const uint LRST                = 1u << 3;
        internal const uint ASDE                = 1u << 5;
        internal const uint SLU                 = 1u << 6;
        internal const uint ILOS                = 1u << 7;
        internal const uint FRCSPD              = 1u << 11;
        internal const uint FRCDPLX             = 1u << 12;
        internal const uint SDP0_DATA           = 1u << 18;
        internal const uint SDP1_DATA           = 1u << 19;
        internal const uint ADVD3WUC            = 1u << 20;
        internal const uint EN_PHYS_PWR_MGMT    = 1u << 21;
        internal const uint SDP0_IODIR          = 1u << 22;
        internal const uint SDP1_IODIR          = 1u << 23;
        internal const uint RST                 = 1u << 26;
        internal const uint RFCE                = 1u << 27;
        internal const uint TFCE                = 1u << 28;
        internal const uint VME                 = 1u << 30;
        internal const uint PHY_RST             = 1u << 31;

        internal const uint SPEED_10Mb          = 0u;
        internal const uint SPEED_100Mb         = 1u << 8;
        internal const uint SPEED_1000Mb        = 2u << 8;
        internal const uint SPEED               = 3u << 8;
    }

    // Bits for setting the interrupt mask

    internal struct InterruptMasks
    {
        internal const uint TXDW                = 1u << 0;
        internal const uint TXQE                = 1u << 1;
        internal const uint LSC                 = 1u << 2;
        internal const uint RXSEQ               = 1u << 3;
        internal const uint RXDMT0              = 1u << 4;
        internal const uint RXO                 = 1u << 6;
        internal const uint RXT0                = 1u << 7;
        internal const uint MDAC                = 1u << 9;
        internal const uint RXCFG               = 1u << 10;
        internal const uint PHYINT              = 1u << 12;
        internal const uint TXD_LOW             = 1u << 15;
        internal const uint SRPD                = 1u << 16;
    }

    // Bits for extended control reg
    internal struct CtrlExtBits
    {
        internal const uint PHY_INTERUPT        = 1u << 5;
        internal const uint ASD_CHECK           = 1u << 12;
        internal const uint EE_RST              = 1u << 13;
        internal const uint SPD_BYPASS          = 1u << 15;
        internal const uint RO_DIS              = 1u << 17;
        internal const uint VREG_POWER_DOWN     = 1u << 21;

        internal const int LINK_MODE_LO_BIT     = 22;
        internal const int LINK_MODE_HI_BIT     = 23;
        internal const uint LINK_MODE_PHYS      = 0u;
        internal const uint LINK_MODE_SERDES    = 2u;
        internal const uint LINK_MODE_EXT_TBI   = 3u;

    }

    internal struct RecvCtrlBits
    {
        internal const uint RECV_ENABLE             = 1u << 1;
        internal const uint STORE_BAD_PKTS          = 1u << 2;
        internal const uint UNICAST_PROMISCUOUS     = 1u << 3;
        internal const uint MULTICAST_PROMISCUOUS   = 1u << 4;
        internal const uint LONG_PKT_ENABLE         = 1u << 5;
        internal const uint BROADCAST_ACCEPT        = 1u << 15;
        internal const uint VLAN_FILTER_ENABLE      = 1u << 18;
        internal const uint CANONICAL_FORM_ENABLE   = 1u << 19;
        internal const uint DISCARD_PAUSE_FRAMES    = 1u << 22;
        internal const uint PASS_MAC_CTRL_FRAMES    = 1u << 23;
        internal const uint STRIP_CRC               = 1u << 26;

        internal const uint LOOPBACK_MODE_DISABLE   = 0u << 6;
        internal const uint LOOPBACK_MODE_ENABLE    = 3u << 6;

        internal const uint RECV_DESC_THRESHOLD_HALF   = 0u << 8;
        internal const uint RECV_DESC_THRESHOLD_QUARTER= 1u << 8;
        internal const uint RECV_DESC_THRESHOLD_EIGHTH = 2u << 8;

        internal const int MULTICAST_OFFSET_LO_BIT  = 12;
        internal const int MULTICAST_OFFSET_HI_BIT  = 13;
        internal const uint MULTICAST_OFFSET_47_36  = 0u;
        internal const uint MULTICAST_OFFSET_46_35  = 1u;
        internal const uint MULTICAST_OFFSET_45_34  = 2u;
        internal const uint MULTICAST_OFFSET_43_32  = 3u;

        internal const uint BUFFER_SIZE_MASK        = 0x02030000;
        internal const uint BUFFER_SIZE_256B        = 0x00030000;
        internal const uint BUFFER_SIZE_512B        = 0x00020000;
        internal const uint BUFFER_SIZE_1KB         = 0x00010000;
        internal const uint BUFFER_SIZE_2KB         = 0x00000000;
        internal const uint BUFFER_SIZE_4KB         = 0x02030000;
        internal const uint BUFFER_SIZE_8KB         = 0x02020000;
        internal const uint BUFFER_SIZE_16KB        = 0x02010000;
    }

    internal struct TsmtCtrlBits
    {
        internal const uint TSMT_ENABLE             = 1u << 1;
        internal const uint PAD_SHORT_PACKETS       = 1u << 3;
        internal const uint SOFTWARE_XOFF_TRANS     = 1u << 22;
        internal const uint RE_TSMT_LATE_COLL       = 1u << 24;
        internal const uint NO_RE_TSMT_ON_UNDERRUN  = 1u << 25;

        internal const uint COLL_THRESHOLD_DEFAULT  = 0x0fu << 4;
        internal const uint COLL_DISTANCE_DEFAULT   = 0x40u << 12;
    }

    internal struct TsmtIpg
    {
        internal const uint DEFAULT_IPG_T           = 10u << 0;
        internal const uint DEFAULT_IPG_R1          = 10u << 10;
        internal const uint DEFAULT_IPG_R2          = 10u << 20;

        internal const uint DEFAULT_IPG = (DEFAULT_IPG_T |
                                           DEFAULT_IPG_R1 |
                                           DEFAULT_IPG_R2);
    }

    internal struct RecvChecksumBits
    {
        internal const uint IP_CHECKSUM_ENABLE      = 1u << 8;
        internal const uint TCP_CHECKSUM_ENABLE     = 1u << 9;
        internal const uint IP6_CHECKSUM_ENABLE     = 1u << 10;
    }

    //
    // The defaults for the rx interrupt delay timers
    //
    internal struct RxDelayTimers
    {
        internal const uint RECV_DELAY_TIMER    = 100u;   // ~100 us
        internal const uint RECV_ABSOLUTE_TIMER = 1000u;  // ~1000 us
    }

    //
    // Recieve address High bits
    //
    internal struct RahRegister
    {
        internal const uint ADDRESS_VALID       = 1u << 31;
    }

    //
    // MultiCast Table Array
    //
    internal struct MtaRegister
    {
        internal const uint MTA_LENGTH          = 128;
    }

    //
    // bits for EEPROM Read register
    //
    internal class EerdRegister
    {
        uint done;
        int shift;

        internal EerdRegister (ushort devIdArg)
        {
            if (devIdArg == 0x1019 || // 82547 EI/GI
                devIdArg == 0x1013 || // 82541 EI
                devIdArg == 0x1018 || // 82541 EI Mobile
                devIdArg == 0x1076 || // 82541 GI/PI
                devIdArg == 0x1077 || // 82541 GI Mobile
                devIdArg == 0x1078 || // 82541 ER Copper
                devIdArg == 0x4003 ||
                devIdArg == 0x107c) {  // 82541 PI

                done  = 0x02;
                shift = 2;
            }
            else {
                done  = 0x10;
                shift = 8;
            }
        }

        internal uint Done { get { return done; } }
        internal int AddressShift { get { return shift; } }

        internal const uint Start = 0x01;
        internal const int DataShift = 16;
    }

    internal struct Mdic
    {
        internal const uint DataMask        = 0x0000ffff;
        internal const uint MdiWrite        = 0x04000000;
        internal const uint MdiRead         = 0x08000000;
        internal const uint Ready           = 0x10000000;
        internal const uint InterruptEnable = 0x20000000;
        internal const uint Error           = 0x40000000;
        internal const uint PowerMask       = 0xfffff7ff;

        internal const uint RegMask = 0x1f;
        internal const int  RegRoll = 16;
        internal const uint PhyMask = 0x1f;
        internal const int  PhyRoll = 21;
    }

    //
    // Bit fields common to both rx and tx descriptors (relative to ulong
    // control words
    //
    internal struct Descriptor
    {
        internal const ulong DESCRIPTOR_DONE    = 0x100000000ul;
    }

    //
    // Bit fields common to both rx and tx descriptors (relative to uint
    // stat part of control words
    //
    internal struct DescriptorStat
    {
        internal const ulong DESCRIPTOR_DONE              = 0x1u;
        internal const ulong DESCRIPTOR_EXCESS_COLLISIONS = 0x2u;
        internal const ulong DESCRIPTOR_LATE_COLLISION    = 0x4u;
        internal const ulong DESCRIPTOR_TRANSMIT_OVERRUN  = 0x8u;
    }

    //
    // The parts within a recieve descriptor
    //
    internal struct RxDescriptor
    {
        internal const ulong LENGTH_MASK        = 0xfffful;
        internal const int   LENGTH_SHIFT       = 0;
        internal const ulong ERR_STAT_MASK      = 0xffff00000000ul;
        internal const int   ERR_STAT_SHIFT     = 32;
    }

    //
    // Fields within the Errors and Stats parts of a recieve descriptor
    //
    internal struct RxErrStatFields
    {
        // status
        internal const uint STATUS_MASK         = 0x00ff;

        internal const uint DESCRIPTOR_DONE     = 1u << 0;
        internal const uint END_OF_PACKET       = 1u << 1;
        internal const uint IGNORE_CHECKSUM     = 1u << 2;
        internal const uint VLAN_PACKET         = 1u << 3;
        internal const uint TCP_CHECKSUM_CALC   = 1u << 5;
        internal const uint IP_CHECKSUM_CALC    = 1u << 6;
        internal const uint PASSED_IN_EXACT     = 1u << 7;

        // errors
        internal const uint ERR_MASK            = 0xff00;

        internal const uint CRC_ERROR           = 1u << 8;
        internal const uint SYMBOL_ERROR        = 1u << 9;
        internal const uint SEQUENCE_ERROR      = 1u << 10;
        internal const uint CARRIER_EXT_ERROR   = 1u << 12;
        internal const uint TCP_CHECKSUM_ERROR  = 1u << 13;
        internal const uint IP_CHECKSUM_ERROR   = 1u << 14;
        internal const uint RX_DATA_ERROR       = 1u << 15;
    }

    //
    // The parts within a recieve descriptor
    //
    internal struct TxDescriptor
    {
        internal const ulong LENGTH_MASK        = 0xfffful;
        internal const int   LENGTH_SHIFT       = 0;
        internal const ulong ERR_STAT_MASK      = 0xf00000000ul;
        internal const int   ERR_STAT_SHIFT     = 32;
    }

    internal struct TxCmdFields
    {
        // status
        internal const uint END_OF_PACKET       = 1u << 24;
        internal const uint INSERT_FCS          = 1u << 25;
        internal const uint INSERT_CHECKSUM     = 1u << 26;
        internal const uint REPORT_STATUS       = 1u << 27;
        internal const uint REPORT_PACKET_SENT  = 1u << 28;
        internal const uint EXTENTION_MODE      = 1u << 29;
        internal const uint VLAN_PACKET_ENABLE  = 1u << 30;
        internal const uint INT_DELAY_ENABLE    = 1u << 31;
    }


    internal struct TxStatErrFields
    {
        // status
        internal const uint DESCRIPTOR_DONE     = 1u << 0;
        internal const uint LATE_COLLISION      = 1u << 1;
        internal const uint EXCESS_COLLISIONS   = 1u << 2;
        internal const uint TRANSMIT_UNDERRUN   = 1u << 3;
    }
}
