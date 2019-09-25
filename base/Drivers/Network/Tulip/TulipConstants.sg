///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TulipConstants.cs
//
//  Simple Driver for DEC 21140a PCI Ethernet card (as used in Virtual PC).
//
//  Useful reference URLs:
//      http://www.intel.com/design/network/manuals/21140ahm.pdf
//

namespace Microsoft.Singularity.Drivers.Network.Tulip
{
    internal struct RDES0
    {
        internal const uint OWN = 1u << 31;    // Own Bit
        internal const uint FF  = 1u << 30;    // Filtering Fail
        internal const int  FL_ROLL = 16;      // Frame length
        internal const uint FL_MASK = 0x3fff;
        internal const uint ES  = 1u << 15;    // Error Summary
        internal const uint DE  = 1u << 14;    // Descriptor Error
        internal const uint DT_S = 0u << 12;   // Data type (serial)
        internal const uint DT_I = 1u << 12;   // Data type (int/loopback)
        internal const uint DT_E = 2u << 12;   // Data type (ext/loopback)
        internal const uint RF  = 1u << 11;    // Runt Frame
        internal const uint MF  = 1u << 10;    // Multicast Frame
        internal const uint FS  = 1u << 9;     // First Descriptor
        internal const uint LS  = 1u << 8;     // Last Descriptor
        internal const uint TL  = 1u << 7;     // Frame Too Long
        internal const uint CS  = 1u << 6;     // Collision Seen
        internal const uint FT  = 1u << 5;     // Frame Type
        internal const uint RW  = 1u << 4;     // Receive Watchdog
        internal const uint RE  = 1u << 3;     // Report MII Error
        internal const uint DB  = 1u << 2;     // Dribbling Bit
        internal const uint CE  = 1u << 1;     // CRC Error
        internal const uint ZER = 1u << 0;     // Zero Length
    }

    internal struct RDES1
    {
        internal const uint RER = 1u << 25;    // Receive End of Ring
        internal const uint RCH = 1u << 24;    // Second address chained
        internal const uint RBS_MASK  = 0x000007ff;
        internal const int  RBS2_ROLL = 11;
    }

    internal struct TDES0
    {
        internal const uint OWN        = 1u << 31;   // Own Bit
        internal const uint ES         = 1u << 15;   // Error Summary
        internal const uint TO         = 1u << 14;   // Transmit Jabber Timeout
        internal const uint LO         = 1u << 11;   // Loss of Carrier
        internal const uint NC         = 1u << 10;   // No Carrier
        internal const uint LC         = 1u << 9;    // Late Collision
        internal const uint EC         = 1u << 8;    // Excessive Collisions
        internal const uint HF         = 1u << 7;    // Heartbeat fail
        internal const int  CC_ROLL    = 3;          // Collision Count
        internal const uint CC_MASK    = 0xf;
        internal const uint LF         = 1u << 2;    // Link Fail Report
        internal const uint UF         = 1u << 1;    // Underflow Error
        internal const uint DE         = 1u << 0;    // Deferred
        internal const uint SETUP_DONE = 0x7fffffff; // Filtering frame done
    }

    internal struct TDES1
    {
        internal const uint IC  = 1u << 31;    // Interrupt on Completion
        internal const uint LS  = 1u << 30;    // Last Segment
        internal const uint FS  = 1u << 29;    // First Segment
        internal const uint FT1 = 1u << 22;    // Filtering type:0
        internal const uint SET = 1u << 27;    // Setup Packet
        internal const uint TER = 1u << 25;    // Transmit end of ring
        internal const uint TCH = 1u << 24;    // Second Address chained
        internal const uint DPD = 1u << 23;    // Disabled Padding
        internal const uint FT0 = 1u << 22;    // Filtering type:1
        internal const uint FT_PERFECT = 0;    // Perfect filtering
        internal const uint FT_HASH    = FT0;  // Hash filtering
        internal const uint FT_INVERSE = FT1;  // Inverse filtering
        internal const uint FT_HASH_ONLY = FT1 | FT0;
        internal const uint TBS_MASK  = 0x000007ff;
        internal const int  TBS2_ROLL = 11;
    }

    internal struct CSR0
    {
        internal const uint WIE = 1u << 24;     // Write and Invalidate En.
        internal const uint RLE = 1u << 23;     // Read Line Enable
        internal const uint RME = 1u << 21;     // Read Multiple Enable
        internal const uint DBO = 1u << 20;     // Descriptor Byte Ordering
        internal const int  TAP_ROLL = 17;      // Transmit Auto. Polling
        internal const uint TAP_MASK = 0x7;
        internal const int  CAL_ROLL = 14;      // Cache Alignment
        internal const uint CAL_MASK = 0x3;
        internal const int  PBL_ROLL = 8;       // Programmable burst len
        internal const uint PBL_MASK = 0x1f;
        internal const int  DSL_ROLL = 2;       // Descriptor Skip len
        internal const uint BAR = 1u << 1;      // Bus Arbitration
        internal const uint SWR = 1u << 0;      // Software Reset
    }

    internal struct CSR5
    {
        internal const int  VALID   = 0x0fffffff;
        internal const int  EB_ROLL = 23;       // Error bits
        internal const uint EB_MASK = 0x7;
        internal const uint EB = EB_MASK << EB_ROLL;
        internal const int  TS_ROLL = 20;       // Transmit Process State
        internal const uint TS_MASK = 0x7;
        internal const int  RS_ROLL = 17;       // Receive Process State
        internal const uint RS_MASK = 0x7;
        internal const uint NIS = 1u << 16;     // Normal Interrupt Summary
        internal const uint AIS = 1u << 15;     // Abnormal Interrupt Summary
        internal const uint ERI = 1u << 14;     // Early Receive Interrupt
        internal const uint FBE = 1u << 13;     // Fatal Bus Error
        internal const uint GTE = 1u << 11;     // General Purpose Timer
        internal const uint ETI = 1u << 10;     // Early Transmit Interrupt
        internal const uint RWT = 1u << 9;      // Receive Watchdog Timeout
        internal const uint RPS = 1u << 8;      // Receive Process Stopped
        internal const uint RU  = 1u << 7;      // Receive Buffer Unavail.
        internal const uint RI  = 1u << 6;      // Receive Interrupt
        internal const uint UNF = 1u << 5;      // Transmit Underflow
        internal const uint TJT = 1u << 3;      // Transmit Jabber Timeout
        internal const uint TU  = 1u << 2;      // Transmit Buffer Unavail.
        internal const uint TPS = 1u << 1;      // Transmit Process Stopped
        internal const uint TI  = 1u << 0;      // Transmit Interrupt
        internal const uint INTERRUPTS = 0x6fef;
    }

    internal struct CSR6
    {
        internal const uint SC  = 1u << 31;     // Special capture
        internal const uint RA  = 1u << 30;     // Receive All
        internal const uint MBO = 1u << 25;     // Must Be One
        internal const uint SCR = 1u << 24;     // Scrambler Mode
        internal const uint PCS = 1u << 23;     // PCS Function
        internal const uint TTM = 1u << 22;     // Transmit Threshold Mode
        internal const uint SF  = 1u << 21;     // Store and Forward
        internal const uint HBD = 1u << 19;     // Heartbeat Disable
        internal const uint PS  = 1u << 18;     // Port Select
        internal const uint CA  = 1u << 17;     // Capture Effect Enable
        internal const int  TR_ROLL = 14;       // Threshold Control Bits
        internal const uint TR_MASK = 0x3;
        internal const uint ST  = 1u << 13;     // Start/Stop Transmit
        internal const uint FC  = 1u << 12;     // Force Collision Mode
        internal const uint OME = 1u << 11;     // Operating Mode (ex/loop)
        internal const uint OMI = 1u << 10;     // Operating Mode (in/loop)
        internal const uint FD  = 1u << 9;      // Full-Duplex Mode
        internal const uint PM  = 1u << 7;      // Pass All Multicast
        internal const uint PR  = 1u << 6;      // Promiscuous Mode
        internal const uint SB  = 1u << 5;      // Start/Stop Backoff
        internal const uint IF  = 1u << 4;      // Inverse Filtering (RO)
        internal const uint PB  = 1u << 3;      // Pass Bad Frames
        internal const uint HO  = 1u << 2;      // Hash-Only Filtering (RO)
        internal const uint SR  = 1u << 1;      // Start/Stop Receive
        internal const uint HP  = 1u << 0;      // Hash/Perfect Recv (RO)
    }

    internal struct CSR7
    {
        internal const uint NI  = 1u << 16;     // Normal Interrupts
        internal const uint AI  = 1u << 15;     // Abnormal Interrupts too
        internal const uint ALL = CSR5.INTERRUPTS;  // All Interrupt bits
        internal const uint ERE = 1 << 14;      // Early Receive Enable
        internal const uint FBE = 1 << 13;      // Fatal Bus Error Enable
        internal const uint GPT = 1 << 11;      // GP Timer Enable
        internal const uint ETE = 1 << 10;      // Early TX Interrupt
        internal const uint RW  = 1 << 9;       // RX Watchdog Timeout
        internal const uint RS  = 1 << 8;       // RX Stop Enable
        internal const uint RU  = 1 << 7;       // RX Buffer Unavailable En
        internal const uint RI  = 1 << 6;       // RX Interrupt Enable
        internal const uint UN  = 1 << 5;       // TX Underflow Interrupt
        internal const uint TJ  = 1 << 3;       // TX Jabber Timeout enable
        internal const uint TU  = 1 << 2;       // TX Buffer Unavailable
        internal const uint TS  = 1 << 1;       // TX Stop Enable
        internal const uint TI  = 1 << 0;       // TX Interrupt Enable
    }

    internal struct CSR9
    {
        internal const uint MDI = 1u << 19;     // MII Mgmt data in
        internal const uint MII = 1u << 18;     // MII Mgmt opt mode (set = rd)
        internal const uint MDO = 1u << 17;     // MII Mgmt write data
        internal const uint MDC = 1u << 16;     // MII Mgmt clock
    }

    /// <summary> Filtering types from table 4-8 in 21143ahm.pdf</summary>
    internal enum FilteringType : byte
    {
        Perfect  = 1,
        Hash     = 2,
        Inverse  = 3,
        HashOnly = 4,
        MinValue = Perfect,
        MaxValue = HashOnly
    }
}
