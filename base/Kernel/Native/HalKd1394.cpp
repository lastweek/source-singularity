//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkd1394.cpp: runtime support for debugging over 1394.
//
//  For more information see:
//      \nt\base\ntos\kd64
//      \nt\base\boot\kdcom
//      \nt\base\boot\kd1394
//      \nt\base\boot\kdusb2
//      \nt\sdktools\debuggers\ntsd64
//
//  Note:   Kernel Only
//

#include "hal.h"
#include "halkd.h"
#include "halkd1394.h"

//
// Debugger Debugging
//
#define KDDBG if (0) kdprintf
#define KDDBG2 if (0) kdprintf

///////////////////////////////////////////////////////// Debugger Structures.
//
//  These structures are accessed directly by the host using RDMA.
//
#define DEBUG_BUS1394_MAX_PACKET_SIZE       4000
#define DEBUG_1394_MAJOR_VERSION            0x1
#define DEBUG_1394_MINOR_VERSION            0x0
#define DEBUG_1394_CONFIG_TAG               0xBABABABA

struct DEBUG_1394_SEND_PACKET {
    UINT32              TransferStatus;
    UINT32              PacketHeader[4];
    UINT32              Length;
    UCHAR               Packet[DEBUG_BUS1394_MAX_PACKET_SIZE];
    UCHAR               Padding[72];
};
STATIC_ASSERT(sizeof(DEBUG_1394_SEND_PACKET) == 4096);

struct DEBUG_1394_RECEIVE_PACKET {
    UINT32              TransferStatus;
    UINT32              Length;
    UCHAR               Packet[DEBUG_BUS1394_MAX_PACKET_SIZE];
    UCHAR               Padding[88];
};
STATIC_ASSERT(sizeof(DEBUG_1394_RECEIVE_PACKET) == 4096);

// exists on target, host reads it to match for id.
struct DEBUG_1394_CONFIG {
    UINT32              Tag;
    UINT16              MajorVersion;
    UINT16              MinorVersion;
    UINT32              Id;
    UINT32              BusPresent;
    UINT64              SendPacket;
    UINT64              ReceivePacket;
};
STATIC_ASSERT(sizeof(DEBUG_1394_CONFIG) == 32);

struct DEBUG_1394_DATA {
    //    POHCI_REGISTER_MAP          BaseAddress;    // our OHCI register map
    UINT32                      CromBuffer[248];   // our config ROM - must be 1k aligned
    DEBUG_1394_CONFIG           Config;         // our config for this session
    DEBUG_1394_SEND_PACKET      SendPacket;     // our send packet (isoch packet)
    DEBUG_1394_RECEIVE_PACKET   ReceivePacket;  // our receive packet
};
STATIC_ASSERT(sizeof(DEBUG_1394_DATA) == 1024 + 4096 + 4096);
STATIC_ASSERT(sizeof(DEBUG_1394_DATA) <= 3 * 4096);   // we allocate 12KB in boot.

//////////////////////////////////////////////////////////////////////////////
//
#define TIMEOUT_COUNT                   1024*500
#define MAX_REGISTER_READS              400000

//
// Global Data Structures
//
static DEBUG_1394_DATA *            Kd1394Data;
static volatile OHCI_REGISTER_MAP * KdRegisters;

//
static ULONG_PTR MmGetPhysicalAddress(PVOID pv)
{
    return (ULONG_PTR)pv;
}

// ?? need to look into this
static UINT32 Dbg1394_StallExecution(UINT32 LoopCount)
{
    volatile UINT32 b = 1;

    for (volatile UINT32 k = 0; k < LoopCount; k++) {
        for (volatile UINT32 i = 1; i < 100000; i++) {
#ifdef ISA_IX86
            __asm pause;
#endif
            b = b * (i>>k);
        }
    }

    return b;
}

//  Exchange byte pairs 0:3 and 1:2 of Source and returns the resulting ULONG.
static inline UINT32 Dbg1394_ByteSwap(UINT32 Source)
{
    return (((Source)              << (8 * 3)) |
            ((Source & 0x0000FF00) << (8 * 1)) |
            ((Source & 0x00FF0000) >> (8 * 1)) |
            ((Source)              >> (8 * 3)));
}

//  Derive the 16 bit CRC as defined by IEEE 1212 clause 8.1.5.
//  (ISO/IEC 13213) First edition 1994-10-05.
//      data - UINT32 data to derive CRC from.
//      check - check value.
static UINT32 Dbg1394_Crc16(UINT32 data, UINT32 check)
{
    UINT32 next = check;

    for (INT32 shift = 28; shift >= 0; shift -= 4) {
        UINT32 sum = ((next >> 12) ^ (data >> shift)) & 0xf;
        next = (next << 4) ^ (sum << 12) ^ (sum << 5) ^ (sum);
    }
    return (next & 0xFFFF);
}

//  Calculate a CRC for the pointer to the Quadlet data.
//      Quadlet - Pointer to data to CRC
//      length - length of data to CRC
static UINT16 Dbg1394_CalculateCrc(UINT32 *Quadlet, UINT32 length)
{
    UINT32 temp = 0;

    for (UINT32 index = 0; index < length; index++) {
        temp = Dbg1394_Crc16(Quadlet[index], temp);
    }
    return (UINT16)temp;
}

//////////////////////////////////////////////////  Initialize the controller!
//
bool Kdp1394Init(UINT16 Channel, ULONG_PTR Base, ULONG_PTR BufferAddr32, UINT32 BufferSize32)
{
    if (Base == 0 ||
        BufferAddr32 == 0 ||
        BufferSize32 < sizeof(DEBUG_1394_DATA)) {

        return false;
    }

    // Note: Kd1394Data must be in the low 32-bits of address space due to
    //       limits on valid 1394 DMA addresses.  It must also be contiguous.

    Kd1394Data = (DEBUG_1394_DATA *)BufferAddr32;
    memset(Kd1394Data, 0, sizeof(*Kd1394Data));

    // get our base address
    KdRegisters = (volatile OHCI_REGISTER_MAP *)Base;

    // initialize our config info for host debugger to read.
    Kd1394Data->Config.Tag = DEBUG_1394_CONFIG_TAG;
    Kd1394Data->Config.MajorVersion = DEBUG_1394_MAJOR_VERSION;
    Kd1394Data->Config.MinorVersion = DEBUG_1394_MINOR_VERSION;
    Kd1394Data->Config.Id = (Channel < 0x100) ? Channel : 0;
    Kd1394Data->Config.BusPresent = false;
    Kd1394Data->Config.SendPacket = MmGetPhysicalAddress(&Kd1394Data->SendPacket);
    Kd1394Data->Config.ReceivePacket = MmGetPhysicalAddress(&Kd1394Data->ReceivePacket);

    // get our version
    UINT32 ulVersion = KdRegisters->Version.all;
    UCHAR MajorVersion = (UCHAR)(ulVersion >> 16);

    // make sure we have a valid version
    if (MajorVersion != 1) { // INVESTIGATE
        kdprintf("1394: MajorVersion != 1\n");
        return false;
    }

    // soft reset to initialize the controller
    HC_CONTROL_REGISTER HCControl;
    HCControl.all = 0;
    HCControl.SoftReset = true;
    KdRegisters->HCControlSet.all = HCControl.all;

    // wait until reset complete - ??
    UINT32 retry = 1000; // ??
    do {
        HCControl.all = KdRegisters->HCControlSet.all;
        Dbg1394_StallExecution(1);
    } while ((HCControl.SoftReset) && (--retry));
    if (retry == 0) {
        kdprintf("1394: Reset failed\n");
        return false;
    }

    // enable link to phy communication.
    HCControl.all = 0;
    HCControl.Lps = true;
    KdRegisters->HCControlSet.all = HCControl.all;

    Dbg1394_StallExecution(20);

    // initialize HCControl register
    // send data in little-endian order (i.e. do byte swap).
    HCControl.all = 0;
    HCControl.NoByteSwapData = true;
    KdRegisters->HCControlClear.all = HCControl.all;

    // enable posted writes.
    HCControl.all = 0;
    HCControl.PostedWriteEnable = true;
    KdRegisters->HCControlSet.all = HCControl.all;

    // setup the link control
    LINK_CONTROL_REGISTER LinkControl;
    LinkControl.all = 0;
    LinkControl.CycleTimerEnable = true;
    LinkControl.CycleMaster = true;
    LinkControl.RcvPhyPkt = true;
    LinkControl.RcvSelfId = true;
    KdRegisters->LinkControlClear.all = LinkControl.all;

    LinkControl.all = 0;
    LinkControl.CycleTimerEnable = true;
    LinkControl.CycleMaster = true;
    KdRegisters->LinkControlSet.all = LinkControl.all;

    // set the bus number (hardcoded to 0x3FF) - ??? what about node id??
    NODE_ID_REGISTER NodeId;
    NodeId.all = 0;
    NodeId.BusId = (UINT16)0x3FF;
    KdRegisters->NodeId.all = NodeId.all;

    // do something with the crom...

    // 0xf0000404 - bus id register
    Kd1394Data->CromBuffer[1] = 0x31333934;

    // 0xf0000408 - bus options register
    BUS_OPTIONS_REGISTER BusOptions;
    BusOptions.all = Dbg1394_ByteSwap(KdRegisters->BusOptions.all);
    BusOptions.Pmc = false;
    BusOptions.Bmc = false;
    BusOptions.Isc = false;
    BusOptions.Cmc = false;
    BusOptions.Irmc = false;
    BusOptions.g = 1;
    Kd1394Data->CromBuffer[2] = Dbg1394_ByteSwap(BusOptions.all);

    // 0xf000040c - global unique id hi
    Kd1394Data->CromBuffer[3] = KdRegisters->GuidHi;

    // 0xf0000410 - global unique id lo
    Kd1394Data->CromBuffer[4] = KdRegisters->GuidLo;

    // 0xf0000400 - config ROM header - set last to calculate CRC!
    CONFIG_ROM_INFO ConfigRomHeader;
    ConfigRomHeader.all = 0;
    ConfigRomHeader.CRI_Info_Length = 4;
    ConfigRomHeader.CRI_CRC_Length = 4;
    ConfigRomHeader.CRI_CRC_Value = Dbg1394_CalculateCrc(&Kd1394Data->CromBuffer[1],
                                                         ConfigRomHeader.CRI_CRC_Length);
    Kd1394Data->CromBuffer[0] = ConfigRomHeader.all;

    Kd1394Data->CromBuffer[6] = 0xC083000C; // 0xf0000418 - node capabilities
    Kd1394Data->CromBuffer[7] = 0xF2500003; // 0xf000041C - module vendor id

    // KD's state machine looks for 1c w/ 50f2, 1d w/ 02, then 1e w/ address.
    Kd1394Data->CromBuffer[8] = 0xF250001C; // 0xf0000420 - extended key (for KD)
    Kd1394Data->CromBuffer[9] = 0x0200001D; // 0xf0000424 - debug key (for KD)

    // 0xf0000428 - debug value (for KD)
    IMMEDIATE_ENTRY CromEntry;
    CromEntry.all = (UINT32)MmGetPhysicalAddress(&Kd1394Data->Config);
    CromEntry.IE_Key = 0x1E;
    Kd1394Data->CromBuffer[10] = Dbg1394_ByteSwap(CromEntry.all);

    // 0xf0000414 - root directory header - set last to calculate CRC!
    DIRECTORY_INFO DirectoryInfo;
    DirectoryInfo.all = 0;
    DirectoryInfo.DI_Length = 5;
    DirectoryInfo.DI_CRC = Dbg1394_CalculateCrc(&Kd1394Data->CromBuffer[6],
                                                DirectoryInfo.DI_Length);
    Kd1394Data->CromBuffer[5] = Dbg1394_ByteSwap(DirectoryInfo.all);

    // write the first few registers
    KdRegisters->ConfigRomHeader.all = Kd1394Data->CromBuffer[0];
    KdRegisters->BusId = Kd1394Data->CromBuffer[1];
    KdRegisters->BusOptions.all = Kd1394Data->CromBuffer[2];
    KdRegisters->GuidHi = Kd1394Data->CromBuffer[3];
    KdRegisters->GuidLo = Kd1394Data->CromBuffer[4];

    // set our crom
    KdRegisters->ConfigRomMap = (UINT32)MmGetPhysicalAddress(&Kd1394Data->CromBuffer);

    // disable all interrupts. wdm driver will enable them later - ??
    KdRegisters->IntMaskClear.all = 0xFFFFFFFF;

    // enable the link
    HCControl.all = 0;
    HCControl.LinkEnable = true;
    KdRegisters->HCControlSet.all = HCControl.all;

    Dbg1394_StallExecution(1000);

    // enable access filters to all nodes
    KdRegisters->AsynchReqFilterLoSet = 0xFFFFFFFF;
    KdRegisters->AsynchReqFilterHiSet = 0xFFFFFFFF;
    KdRegisters->PhyReqFilterHiSet = 0xFFFFFFFF;
    KdRegisters->PhyReqFilterLoSet = 0xFFFFFFFF;

    // hard reset on the bus (so KD will look for us)
    PHY_CONTROL_REGISTER PhyControl;
    PhyControl.all = 0;
    PhyControl.RdReg = true;
    PhyControl.RegAddr = 1;

    KdRegisters->PhyControl.all = PhyControl.all;
    retry = MAX_REGISTER_READS;
    do {
        PhyControl.all = KdRegisters->PhyControl.all;
    } while ((!PhyControl.RdDone) && --retry);
    if (retry == 0) {
        kdprintf("1394: Read on bus failed\n");
        return false;
    }

    UCHAR Data = ((UCHAR)PhyControl.RdData | PHY_INITIATE_BUS_RESET);

    PhyControl.all = 0;
    PhyControl.WrReg = true;
    PhyControl.RegAddr = 1;
    PhyControl.WrData = Data;

    KDDBG2("1394: Writing to        PhyControl=%08x\n", PhyControl.all);
    KdRegisters->PhyControl.all = PhyControl.all;

    retry = MAX_REGISTER_READS;
    do {
        PhyControl.all = KdRegisters->PhyControl.all;
    } while (PhyControl.WrReg && --retry);
    if (retry == 0) {
        kdprintf("1394: Hard reset on bus failed\n");
        return false;
    }

    kdprintf("1394: Init Succeeded\n");
    return true;
}

static void Dbg1394_EnablePhysicalAccess()
{
    // see if ohci1394 is being loaded...
    HC_CONTROL_REGISTER HCControl;
    HCControl.all = KdRegisters->HCControlSet.all;
    if (!HCControl.LinkEnable || !HCControl.Lps || HCControl.SoftReset) {
        KDDBG("1394: EnablePhysicalAccess HCControl=%08x!\n", HCControl.all);
        return;
    }

    // if the bus reset interrupt is not cleared, we have to clear it...
    INT_EVENT_MASK_REGISTER IntEvent;
    IntEvent.all = KdRegisters->IntEventSet.all;
    if (IntEvent.BusReset) {
        KDDBG("1394: EnablePhysicalAccess IntEvent =%08x!\n", IntEvent.all);
        IntEvent.all = 0;
        IntEvent.BusReset = 1;
        KdRegisters->IntEventClear.all = IntEvent.all;
    }

    // we might need to re-enable physical access. If so, do it.
    KdRegisters->AsynchReqFilterHiSet = 0xFFFFFFFF;
    KdRegisters->AsynchReqFilterLoSet = 0xFFFFFFFF;
    KdRegisters->PhyReqFilterHiSet = 0xFFFFFFFF;
    KdRegisters->PhyReqFilterLoSet = 0xFFFFFFFF;
}

static KDP_STATUS
Dbg1394_ReadPacket(
    OUT PKD_PACKET      PacketHeader,
    OUT PSTRING         MessageHeader,
    OUT PSTRING         MessageData,
    bool             Wait
    )
//    KDP_PACKET_RESEND - if resend is required.  = 2 = CP_GET_ERROR
//    KDP_PACKET_TIMEOUT - if timeout.            = 1 = CP_GET_NODATA
//    KDP_PACKET_RECEIVED - if packet received.   = 0 = CP_GET_SUCCESS
{
    UINT32  timeoutLimit = 0;

    do {
        // make sure our link is enabled..
        Dbg1394_EnablePhysicalAccess();
        KdpSpin();

        if (Kd1394Data->ReceivePacket.TransferStatus == STATUS_PENDING) {
            KdDebuggerNotPresent = false;

            memcpy(PacketHeader,
                   &Kd1394Data->ReceivePacket.Packet[0],
                   sizeof(KD_PACKET));

            // make sure we have a valid PacketHeader
            if (Kd1394Data->ReceivePacket.Length < sizeof(KD_PACKET)) {
                // short packet, we are done...
                Kd1394Data->ReceivePacket.TransferStatus = STATUS_SUCCESS;
                return(KDP_PACKET_RESEND);
            }

            if (MessageHeader) {
                memcpy(MessageHeader->Buffer,
                       &Kd1394Data->ReceivePacket.Packet[sizeof(KD_PACKET)],
                       MessageHeader->MaximumLength);

                if (Kd1394Data->ReceivePacket.Length <= (UINT16)(sizeof(KD_PACKET)+MessageHeader->MaximumLength)) {
                    Kd1394Data->ReceivePacket.TransferStatus = STATUS_SUCCESS;
                    return(KDP_PACKET_RECEIVED);
                }

                if (MessageData) {
                    memcpy(MessageData->Buffer,
                           &Kd1394Data->ReceivePacket.Packet[sizeof(KD_PACKET) + MessageHeader->MaximumLength],
                           Kd1394Data->ReceivePacket.Length - (sizeof(KD_PACKET) + MessageHeader->MaximumLength));
                }
            }

            Kd1394Data->ReceivePacket.TransferStatus = STATUS_SUCCESS;
            return(KDP_PACKET_RECEIVED);
        }

        timeoutLimit++;

        if (Wait == false) {
            return(KDP_PACKET_RESEND);
        }

    } while (timeoutLimit <= TIMEOUT_COUNT);

    return(KDP_PACKET_TIMEOUT);
}

//
//  Send a control packet to the host machine that is running the
//  kernel debugger and wait for an ACK.
//
//      PacketType - Supplies the type of packet to send.
//
static void KdpSendControlPacket(IN UINT16 PacketType)
{
    KD_PACKET   PacketHeader;

    //
    // Initialize and send the packet header.
    //
    PacketHeader.PacketLeader = CONTROL_PACKET_LEADER;
    PacketHeader.PacketId = 0;
    PacketHeader.ByteCount = 0;
    PacketHeader.Checksum = 0;
    PacketHeader.PacketType = PacketType;

    // setup our send packet
    memset(&Kd1394Data->SendPacket, 0, sizeof(DEBUG_1394_SEND_PACKET));
    Kd1394Data->SendPacket.Length = 0;

    memcpy(&Kd1394Data->SendPacket.PacketHeader[0],
           &PacketHeader, sizeof(KD_PACKET));

    Kd1394Data->SendPacket.TransferStatus = STATUS_PENDING;
}

KDP_STATUS
Kdp1394ReceivePacket(
    IN UINT32           PacketType,
    OUT PSTRING         MessageHeader,
    OUT PSTRING         MessageData,
    OUT UINT32 *        DataLength,
    IN OUT PKD_CONTEXT  KdContext
    )
    //  Routine Description:
    //      This routine receives a packet from the host machine that is running
    //      the kernel debugger UI.  This routine is ALWAYS called after packet being
    //      sent by caller.  It first waits for ACK packet for the packet sent and
    //      then waits for the packet desired.
    //
    //      N.B. If caller is KdPrintString, the parameter PacketType is
    //         PACKET_TYPE_KD_ACKNOWLEDGE.  In this case, this routine will return
    //         right after the ack packet is received.
    //
    //  Arguments:
    //      PacketType - Supplies the type of packet that is excepted.
    //      MessageHeader - Supplies a pointer to a string descriptor for the input
    //          message.
    //      MessageData - Supplies a pointer to a string descriptor for the input data.
    //      DataLength - Supplies pointer to UINT32 to receive length of recv. data.
    //      KdContext - Supplies a pointer to the kernel debugger context.
    //
    //  Return Value:
    //      KDP_PACKET_RESEND - if resend is required.  = 2 = CP_GET_ERROR
    //      KDP_PACKET_TIMEOUT - if timeout.            = 1 = CP_GET_NODATA
    //      KDP_PACKET_RECEIVED - if packet received.   = 0 = CP_GET_SUCCESS
{
    UINT32      MessageLength;
    KD_PACKET   PacketHeader;
    KDP_STATUS  ReturnCode;
    UINT32      Checksum;

    KDDBG2("Kdp1394ReceivePacket\n");

    // this dispatch gets called with PacketType != PACKET_TYPE_KD_POLL_BREAKIN for
    // the number of times specified in KdCompNumberRetries (??).

WaitForPacketLeader:

    // read in our packet, if available...
    ReturnCode = Dbg1394_ReadPacket(&PacketHeader,
                                    MessageHeader,
                                    MessageData,
                                    true);
    //
    // If we can successfully read packet leader, it has high possibility that
    // kernel debugger is alive.  So reset count.
    //
    if (ReturnCode != KDP_PACKET_TIMEOUT) {
        KdCompNumberRetries = KdCompRetryCount;
    }

    if (ReturnCode != KDP_PACKET_RECEIVED) {
        // see if it's a breakin packet...
        if ((PacketHeader.PacketLeader & 0xFF) == BREAKIN_PACKET_BYTE) {
            KdContext->KdpControlCPending = true;
            return(KDP_PACKET_RESEND);
        }
        return(ReturnCode);
    }

    //
    // if the packet we received is a resend request, we return true and
    // let caller resend the packet.
    //
    if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER &&
        PacketHeader.PacketType == PACKET_TYPE_KD_RESEND) {
        return(KDP_PACKET_RESEND);
    }

    //
    // Check ByteCount received is valid
    //
    MessageLength = MessageHeader->MaximumLength;

    if ((PacketHeader.ByteCount > (UINT16)PACKET_MAX_SIZE) ||
        (PacketHeader.ByteCount < (UINT16)MessageLength)) {
        goto SendResendPacket;
    }
    *DataLength = PacketHeader.ByteCount - MessageLength;

    MessageData->Length = (UINT16)*DataLength;
    MessageHeader->Length = (UINT16)MessageLength;

    //
    // Check PacketType is what we are waiting for.
    //
    if (PacketType != PacketHeader.PacketType) {
        goto SendResendPacket;
    }

    //
    // Check checksum is valid.
    //
    Checksum = KdpComputeChecksum(MessageHeader->Buffer, MessageHeader->Length);
    Checksum += KdpComputeChecksum(MessageData->Buffer, MessageData->Length);

    if (Checksum != PacketHeader.Checksum) {
        goto SendResendPacket;
    }

    return(KDP_PACKET_RECEIVED);

SendResendPacket:

    KdpSendControlPacket(PACKET_TYPE_KD_RESEND);
    goto WaitForPacketLeader;
}

void
Kdp1394SendPacket(
    IN UINT32           PacketType,
    IN PSTRING          MessageHeader,
    IN PSTRING          MessageData OPTIONAL,
    IN OUT PKD_CONTEXT  KdContext
    )
    //  Routine Description:
    //      This routine sends a packet to the host machine that is running the
    //      kernel debugger and waits for an ACK.
    //
    //  Arguments:
    //      PacketType - Supplies the type of packet to send.
    //      MessageHeader - Supplies a pointer to a string descriptor that describes
    //          the message information.
    //      MessageData - Supplies a pointer to a string descriptor that describes
    //          the optional message data.
    //      KdContext - Supplies a pointer to the kernel debugger context.
    //
    //  Return Value:
    //      None.
{
    KD_PACKET                   PacketHeader;
    UINT32                      MessageDataLength;
    UINT32                      ReturnCode;
    bool                        bException = false;

    KDDBG2("Kdp1394SendPacket\n");
    PacketHeader.Checksum = 0;

    if (MessageData != NULL) {
        MessageDataLength = MessageData->Length;
        PacketHeader.Checksum = KdpComputeChecksum(MessageData->Buffer, MessageData->Length);
    }
    else {
        MessageDataLength = 0;
        PacketHeader.Checksum = 0;
    }

    PacketHeader.Checksum += KdpComputeChecksum(MessageHeader->Buffer, MessageHeader->Length);

    //
    // Initialize and send the packet header.
    //
    PacketHeader.PacketLeader = PACKET_LEADER;
    PacketHeader.ByteCount = (UINT16)(MessageHeader->Length + MessageDataLength);
    PacketHeader.PacketType = (UINT16)PacketType;
    PacketHeader.PacketId = KdPacketId;

    KdPacketId++;

    KdCompNumberRetries = KdCompRetryCount;

    // setup our send packet
    memset(&Kd1394Data->SendPacket, 0, sizeof(DEBUG_1394_SEND_PACKET));
    Kd1394Data->SendPacket.Length = 0;

    // copy our packet header...
    memcpy(&Kd1394Data->SendPacket.PacketHeader[0],
           &PacketHeader, sizeof(KD_PACKET));

    // setup our message header
    if (MessageHeader) {
        memcpy(&Kd1394Data->SendPacket.Packet[0],
               MessageHeader->Buffer, MessageHeader->Length);
        Kd1394Data->SendPacket.Length += MessageHeader->Length;
    }

    // setup our message data
    if (MessageData != NULL) {
        memcpy(&Kd1394Data->SendPacket.Packet[Kd1394Data->SendPacket.Length],
               MessageData->Buffer, MessageData->Length);
        Kd1394Data->SendPacket.Length += MessageData->Length;
    }

    Kd1394Data->SendPacket.TransferStatus = STATUS_PENDING;

    //
    // We sync on first STATE_CHANGE64 message like NT.  If this
    // is the first such message, drain receive pipe as nothing
    // said before this instant is interesting (and any buffered
    // packets may interact badly with SendWaitContinue).
    //
    if (PacketType == PACKET_TYPE_KD_STATE_CHANGE64 /* && !KdStateChange64Sent*/) {
        // need to do this to fix pre-logging (eventually).
#if 0
        UCHAR uDummy;
        uint32 dwDrained = 0;
        KdCompNextPacketIdToSend |= SYNC_PACKET_ID;
        KdStateChange64Sent = true;

        while (KdCompGetByte(&uDummy) == CP_GET_SUCCESS) {
            dwDrained++;
        }
#endif // 0
    }

    do {
        KDDBG2("LOOP %d/%d [SendPacket=%p %08x %08x %08x %02x %02x %02x %02x]\n",
               KdCompNumberRetries, KdCompRetryCount,
               &Kd1394Data->SendPacket,
               Kd1394Data->SendPacket.TransferStatus,
               *(UINT32*)&Kd1394Data->SendPacket.PacketHeader,
               Kd1394Data->SendPacket.Length,
               Kd1394Data->SendPacket.Packet[0],
               Kd1394Data->SendPacket.Packet[1],
               Kd1394Data->SendPacket.Packet[2],
               Kd1394Data->SendPacket.Packet[3]);

        // make sure our link is enabled..
        Dbg1394_EnablePhysicalAccess();

        if (KdCompNumberRetries == 0) {
            //
            // If the packet is not for reporting exception, we give up
            // and declare debugger not present.
            //
            if (PacketType == PACKET_TYPE_KD_DEBUG_IO) {
                PDBGKD_DEBUG_IO DebugIo
                    = (PDBGKD_DEBUG_IO)MessageHeader->Buffer;

                if (DebugIo->ApiNumber == DbgKdPrintStringApi) {
                    KdDebuggerNotPresent = true;
                    Kd1394Data->SendPacket.TransferStatus = STATUS_SUCCESS;
                    return;
                }
            }
            else if (PacketType == PACKET_TYPE_KD_STATE_CHANGE64) {
                PDBGKD_ANY_WAIT_STATE_CHANGE StateChange
                    = (PDBGKD_ANY_WAIT_STATE_CHANGE)MessageHeader->Buffer;
                if (StateChange->NewState == DbgKdLoadSymbolsStateChange) {
                    KdDebuggerNotPresent = true;
                    Kd1394Data->SendPacket.TransferStatus = STATUS_SUCCESS;
                    return;
                }
            }
            else if (PacketType == PACKET_TYPE_KD_FILE_IO) {
                PDBGKD_FILE_IO FileIo
                    = (PDBGKD_FILE_IO)MessageHeader->Buffer;
                if (FileIo->ApiNumber == DbgKdCreateFileApi) {
                    KdDebuggerNotPresent = true;
                    Kd1394Data->SendPacket.TransferStatus = STATUS_SUCCESS;
                    return;
                }
            }
            else {
                bException = true;
            }
        }

        ReturnCode = KDP_PACKET_TIMEOUT;

        {
            UINT32                  count = 0;
            volatile NTSTATUS       *pStatus;

            pStatus = &Kd1394Data->ReceivePacket.TransferStatus;

            //
            // now sit here and poll for a response from the host machine
            //
            do {
                // make sure our link is enabled..
                Dbg1394_EnablePhysicalAccess();
                KdpSpin();

                //
                // while in this loop check if the host has submitted a new request.
                // If they did, abort processing of the current request.
                //
                count++;
                if (Kd1394Data->SendPacket.TransferStatus != STATUS_PENDING) {
                    ReturnCode = KDP_PACKET_RECEIVED;
                    break;
                }

                if ((*pStatus == STATUS_PENDING) && (!bException)) {
                    ReturnCode = KDP_PACKET_RECEIVED;
                    break;
                }
            } while (count < TIMEOUT_COUNT);
        }

        if (ReturnCode == KDP_PACKET_TIMEOUT) {
            KdCompNumberRetries--;
        }
    } while (ReturnCode != KDP_PACKET_RECEIVED);

    //
    // Since we are able to talk to debugger, the retrycount is set to
    // maximum value.
    //
    KdCompRetryCount = KdContext->KdpDefaultRetries;
}

// Returns true if a breakin packet is pending.
// A packet is present if: There is a valid character which matches BREAK_CHAR.
bool Kdp1394PollBreakIn(void)
{
    KDDBG2("Kdp1394PollBreakIn\n");

    // make sure our link is enabled..
    Dbg1394_EnablePhysicalAccess();

    // let's peak into our receive packet and see if it's a breakin
    if ((Kd1394Data->ReceivePacket.TransferStatus == STATUS_PENDING) &&
        (Kd1394Data->ReceivePacket.Packet[0] == BREAKIN_PACKET_BYTE)) {

        KdDebuggerNotPresent = false;

        // we have a breakin packet
        Kd1394Data->ReceivePacket.TransferStatus = STATUS_SUCCESS;
        return true;
    }
    return false;
}

//
///////////////////////////////////////////////////////////////// End of File.
