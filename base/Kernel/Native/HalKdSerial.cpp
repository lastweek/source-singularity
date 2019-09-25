//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkdserial.cpp: Serial-port transport routines.
//
//  Note:   Kernel Only
//

#include "hal.h"
#include "halkd.h"

//
// Debugger Debugging
//
#define KDDBG if (0) kdprintf
#define KDDBG2 if (0) kdprintf

//
// Globals
//
static UINT32 KdCompPacketIdExpected = INITIAL_PACKET_ID;
static UINT32 KdCompNextPacketIdToSend = INITIAL_PACKET_ID | SYNC_PACKET_ID;
static BOOL  KdStateChange64Sent = false;

/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
//
// PLATFORM LAYER - this is the cut point for abstracting the serial port
//
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////


KDP_STATUS KdpSerialGetByte(OUT PUCHAR Input, BOOL WaitForByte);
void KdpSerialPutByte(IN UCHAR Output);

//++
//
//Routine Description:
//
//  This routine reads a string from the kernel debugger port.
//
//Arguments:
//
//  Destination - Supplies a pointer to the input string.
//
//  Length - Supplies the length of the string to be read.
//--

static KDP_STATUS KdpSerialReceiveString(OUT PUCHAR Destination, IN UINT32 Length, IN BOOL WaitForInput = true)
{
    KDDBG2("KdpSerialReceiveString len %d\n", Length);

    UCHAR Input;
    UINT32 ReqLength = Length;
    UINT32 ReturnCode;

    //
    // Read bytes until either a error is encountered or the entire string
    // has been read.
    //
    while (Length > 0) {
        KdpSpin();

        ReturnCode = KdpSerialGetByte(&Input, WaitForInput);
        if (ReturnCode != KDP_PACKET_RECEIVED) {
            break;
        }
        else {
            *Destination++ = Input;
            Length -= 1;
        }
    }

    KDDBG2("KdpSerialReceiveString left %d\n", Length);

    return (Length == 0) ? KDP_PACKET_RECEIVED : KDP_PACKET_TIMEOUT;
}

//++
//
//Routine Description:
//
//  This routine writes a string to the kernel debugger port.
//
//Arguments:
//
//  Source - Supplies a pointer to the output string.
//
//  Length - Supplies the length of the string to be written.
//
//Return Value:
//
//  None.
//
//--

static void KdpSerialSendString(IN PUCHAR Source, IN UINT32 Length)
{

    KDDBG2("KdpSerialSendString len %d\n", Length);

    UINT32 ReqLength = (UINT32)Length;

    //
    // Write bytes to the kernel debugger port.
    //

    UCHAR Output;

    while (Length > 0) {
        Output = *Source++;
        KdpSerialPutByte(Output);
        Length -= 1;
    }

    KDDBG2("KdpSerialSendString done\n");
}

/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////
//
// CHANNEL LAYER - all this code should be neutral to the actual channel
// (i.e. nothing specific to serial port, only reading and writing bytes)
//
/////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////

//  Wait for a packet header leader (receive it into PacketLeader ULONG).
//
static
KDP_STATUS
KdCompReceivePacketLeader(
    OUT UINT32 *PacketLeader,
    IN OUT PKD_CONTEXT KdContext
    )
{

    UCHAR Input;
    UCHAR PreviousByte = 0;
    UINT32 PacketId = 0;
    UINT32 Index;
    KDP_STATUS ReturnCode;
    BOOLEAN BreakinDetected = false;

    KDDBG2("KdCompReceivePacketLeader\n");
    //
    // NOTE - With all the interrupts being off, it is very hard
    // to implement the actual timeout code. (Maybe, by reading the CMOS.)
    // Here we use a loop count to wait about 3 seconds.  The CpGetByte
    // will return with error code = KDP_PACKET_TIMEOUT if it cannot find data
    // byte within 1 second. Kernel debugger's timeout period is 5 seconds.
    //

    Index = 0;
    do {
        ReturnCode = KdpSerialReceiveString(&Input, 1);
        if (ReturnCode == KDP_PACKET_TIMEOUT) {
            if (BreakinDetected) {
                KdContext->KdpControlCPending = true;
                return KDP_PACKET_RESEND;
            }
            else {
                KDDBG2("KdCompReceivePackerLeader returning KDP_PACKET_TIMEOUT\n");
                return KDP_PACKET_TIMEOUT;
            }
        }
        else if (ReturnCode == KDP_PACKET_RESEND) {
            Index = 0;
            continue;
        }
        else {                    // if (ReturnCode == KDP_PACKET_RECEIVED)
            if ( Input == PACKET_LEADER_BYTE ||
                 Input == CONTROL_PACKET_LEADER_BYTE ) {
                if ( Index == 0 ) {
                    PreviousByte = Input;
                    Index++;
                }
                else if (Input == PreviousByte) {
                    Index++;
                }
                else {
                    PreviousByte = Input;
                    Index = 1;
                }
            }
            else {

                //
                // If we detect breakin character, we need to verify it
                // validity.  (It is possible that we missed a packet leader
                // and the breakin character is simply a data byte in the
                // packet.)
                // Since kernel debugger send out breakin character ONLY
                // when it is waiting for State Change packet.  The breakin
                // character should not be followed by any other character
                // except packet leader byte.
                //

                if ( Input == BREAKIN_PACKET_BYTE ) {
                    BreakinDetected = true;
                }
                else {

                    //
                    // The following statement is ABSOLUTELY necessary.
                    //

                    BreakinDetected = false;
                }
                Index = 0;
            }
        }
    } while ( Index < 4 );

    if (BreakinDetected) {
        KdContext->KdpControlCPending = true;
    }

    //
    // return the packet leader and false to indicate no resend is needed.
    //

    if ( Input == PACKET_LEADER_BYTE ) {
        *PacketLeader = PACKET_LEADER;
    }
    else {
        *PacketLeader = CONTROL_PACKET_LEADER;
    }
    KdDebuggerNotPresent = false;
#if 0
    SharedUserData->KdDebuggerEnabled |= 0x00000002;
#endif

    return KDP_PACKET_RECEIVED;
}


static
void
KdpSendControlPacket(
    IN UINT16 PacketType,
    IN UINT32 PacketId OPTIONAL
    )
    //  Routine Description:
    //      This routine sends a control packet to the host machine that is running the
    //      kernel debugger and waits for an ACK.
    //
    //  Arguments:
    //      PacketType - Supplies the type of packet to send.
    //      PacketId - Supplies packet id, optionally.
    //
    //  Return Value:
    //      None.
{

    KD_PACKET PacketHeader;

    //
    // Initialize and send the packet header.
    //

    PacketHeader.PacketLeader = CONTROL_PACKET_LEADER;
    if (PacketId != 0) {
        PacketHeader.PacketId = PacketId;
    }
    PacketHeader.ByteCount = 0;
    PacketHeader.Checksum = 0;
    PacketHeader.PacketType = PacketType;
    KdpSerialSendString((PUCHAR)&PacketHeader, sizeof(KD_PACKET));

    return;
}

//////////////////////////////////////////////////////////////////////////////
//
void
KdpSerialSendPacket(
                    IN UINT32 PacketType,
                    IN PSTRING MessageHeader,
                    IN PSTRING MessageData OPTIONAL,
                    IN OUT PKD_CONTEXT KdContext
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

    KD_PACKET PacketHeader;
    UINT32 MessageDataLength;
    KDP_STATUS ReturnCode;
    KDDBG2("KdpSerialSendPacket %d\n", PacketType);

    if (MessageData != NULL) {
        MessageDataLength = MessageData->Length;
        PacketHeader.Checksum = KdpComputeChecksum(MessageData->Buffer,
                                                   MessageData->Length);
    }
    else {
        MessageDataLength = 0;
        PacketHeader.Checksum = 0;
    }
    PacketHeader.Checksum += KdpComputeChecksum(MessageHeader->Buffer,
                                                MessageHeader->Length);

    //
    // Initialize and send the packet header.
    //

    PacketHeader.PacketLeader = PACKET_LEADER;
    PacketHeader.ByteCount = (UINT16)(MessageHeader->Length + MessageDataLength);
    PacketHeader.PacketType = (UINT16)PacketType;

    KdCompNumberRetries = KdCompRetryCount;

    //
    // We sync on first STATE_CHANGE64 message like NT.  If this
    // is the first such message, drain receive pipe as nothing
    // said before this instant is interesting (and any buffered
    // packets may interact badly with SendWaitContinue).
    //
    if (PacketType == PACKET_TYPE_KD_STATE_CHANGE64 && !KdStateChange64Sent) {
        //
        UCHAR uDummy;
        uint32 dwDrained = 0;
        KdCompNextPacketIdToSend |= SYNC_PACKET_ID;
        KdStateChange64Sent = true;

        while (KdpSerialReceiveString(&uDummy, 1, false) == KDP_PACKET_RECEIVED) {
            dwDrained++;
        }
    }

    do {
        KDDBG2("LOOP %d/%d\n", KdCompNumberRetries, KdCompRetryCount);
        if (KdCompNumberRetries == 0) {
            KDDBG("KdCompNumberRetries == 0\n");
            //
            // If the packet is not for reporting exception, we give up
            // and declare debugger not present.
            //
            if (PacketType == PACKET_TYPE_KD_STATE_CHANGE64) {
                PDBGKD_ANY_WAIT_STATE_CHANGE StateChange
                    = (PDBGKD_ANY_WAIT_STATE_CHANGE)MessageHeader->Buffer;
                if (StateChange->NewState == DbgKdLoadSymbolsStateChange) {
                    KdDebuggerNotPresent = true;
                    //SharedUserData->KdDebuggerEnabled &= ~0x00000002;
                    KdCompNextPacketIdToSend = INITIAL_PACKET_ID | SYNC_PACKET_ID;
                    KdCompPacketIdExpected = INITIAL_PACKET_ID;
                    return;
                }
            }
            else if (PacketType == PACKET_TYPE_KD_DEBUG_IO) {
                PDBGKD_DEBUG_IO DebugIo
                    = (PDBGKD_DEBUG_IO)MessageHeader->Buffer;
                if (DebugIo->ApiNumber == DbgKdPrintStringApi) {
                    KdDebuggerNotPresent = true;
                    //SharedUserData->KdDebuggerEnabled &= ~0x00000002;
                    KdCompNextPacketIdToSend = INITIAL_PACKET_ID | SYNC_PACKET_ID;
                    KdCompPacketIdExpected = INITIAL_PACKET_ID;
                    return;
                }
            }
            else if (PacketType == PACKET_TYPE_KD_FILE_IO) {
                PDBGKD_FILE_IO FileIo;

                FileIo = (PDBGKD_FILE_IO)MessageHeader->Buffer;
                if (FileIo->ApiNumber == DbgKdCreateFileApi) {
                    KdDebuggerNotPresent = true;
                    //SharedUserData->KdDebuggerEnabled &= ~0x00000002;
                    KdCompNextPacketIdToSend = INITIAL_PACKET_ID | SYNC_PACKET_ID;
                    KdCompPacketIdExpected = INITIAL_PACKET_ID;
                    return;
                }
            }
        }
        //
        // Setting PacketId has to be in the do loop in case Packet Id was
        // reset.
        //

        PacketHeader.PacketId = KdCompNextPacketIdToSend;
        KdpSerialSendString((PUCHAR)&PacketHeader, sizeof(KD_PACKET));

        //
        // Output message header.
        //

        KdpSerialSendString((PUCHAR)MessageHeader->Buffer, MessageHeader->Length);

        //
        // Output message data.
        //

        if ( MessageDataLength ) {
            KdpSerialSendString((PUCHAR)MessageData->Buffer, MessageData->Length);
        }

        //
        // Output a packet trailing byte
        //

        {
            UCHAR b = PACKET_TRAILING_BYTE;
            KdpSerialSendString(&b, 1);
        }

        //
        // Wait for the Ack Packet
        //

        ReturnCode = KdpSerialReceivePacket(
                                            PACKET_TYPE_KD_ACKNOWLEDGE,
                                            NULL,
                                            NULL,
                                            NULL,
                                            KdContext
                                            );
        if (ReturnCode == KDP_PACKET_TIMEOUT) {
            KDDBG2("TIMEOUT\n");
            KdCompNumberRetries--;
        }
    } while (ReturnCode != KDP_PACKET_RECEIVED);

    KDDBG2("KD: PACKET_RECEIVED\n");
    //
    // Reset Sync bit in packet id.  The packet we sent may have Sync bit set
    //

    KdCompNextPacketIdToSend &= ~SYNC_PACKET_ID;

    //
    // Since we are able to talk to debugger, the retrycount is set to
    // maximum value.
    //

    KdCompRetryCount = KdContext->KdpDefaultRetries;

    KDDBG2("KdpSerialSendPacket %d done\n", PacketType);
}

//////////////////////////////////////////////////////////////////////////////
//
KDP_STATUS
KdpSerialReceivePacket(
                       IN UINT32 PacketType,
                       OUT PSTRING MessageHeader,
                       OUT PSTRING MessageData,
                       OUT UINT32 *DataLength,
                       IN OUT PKD_CONTEXT KdContext
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
    //      KDP_PACKET_RESEND - if resend is required.
    //      KDP_PAKCET_TIMEOUT - if timeout.
    //      KDP_PACKET_RECEIVED - if packet received.
{

    UCHAR Input;
    UINT32 MessageLength;
    KD_PACKET PacketHeader;
    KDP_STATUS ReturnCode;
    UINT32 Checksum;

    KDDBG2("KdpSerialReceivePacket %d\n", PacketType);

  WaitForPacketLeader:

    //
    // Read Packet Leader
    //
    ReturnCode = KdCompReceivePacketLeader(&PacketHeader.PacketLeader, KdContext);
    KDDBG2("KdCompReceivePacketLeader returned %d\n", ReturnCode);

    //
    // If we can successfully read packet leader, it has high possibility that
    // kernel debugger is alive.  So reset count.
    //
    if (ReturnCode != KDP_PACKET_TIMEOUT) {
        KdCompNumberRetries = KdCompRetryCount;
    }
    if (ReturnCode != KDP_PACKET_RECEIVED) {
        return ReturnCode;
    }

    //
    // Read packet type.
    //

    ReturnCode = KdpSerialReceiveString((PUCHAR)&PacketHeader.PacketType,
                                        sizeof(PacketHeader.PacketType));

    if (ReturnCode == KDP_PACKET_TIMEOUT) {
        return KDP_PACKET_TIMEOUT;
    }
    else if (ReturnCode == KDP_PACKET_RESEND) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {
            //
            // If read error and it is for a control packet, simply
            // pretend that we have not seen this packet.  Hopefully
            // we will receive the packet we desire which automatically acks
            // the packet we just sent.
            //
            goto WaitForPacketLeader;
        }
        else {
            //
            // if read error while reading data packet, we have to ask
            // kernel debugger to resend us the packet.
            //
            goto SendResendPacket;
        }
    }

    //
    // if the packet we received is a resend request, we return true and
    // let caller resend the packet.
    //
    if ( PacketHeader.PacketLeader == CONTROL_PACKET_LEADER &&
         PacketHeader.PacketType == PACKET_TYPE_KD_RESEND ) {
        return KDP_PACKET_RESEND;
    }

    //
    // Read data length.
    //
    ReturnCode = KdpSerialReceiveString((PUCHAR)&PacketHeader.ByteCount,
                                        sizeof(PacketHeader.ByteCount));
    if (ReturnCode == KDP_PACKET_TIMEOUT) {
        return KDP_PACKET_TIMEOUT;
    }
    else if (ReturnCode == KDP_PACKET_RESEND) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {
            goto WaitForPacketLeader;
        }
        else {
            goto SendResendPacket;
        }
    }

    //
    // Read Packet Id.
    //
    ReturnCode = KdpSerialReceiveString((PUCHAR)&PacketHeader.PacketId,
                                        sizeof(PacketHeader.PacketId));

    if (ReturnCode == KDP_PACKET_TIMEOUT) {
        return KDP_PACKET_TIMEOUT;
    }
    else if (ReturnCode == KDP_PACKET_RESEND) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {
            goto WaitForPacketLeader;
        }
        else {
            goto SendResendPacket;
        }
    }

    //
    // Read packet checksum.
    //
    ReturnCode = KdpSerialReceiveString((PUCHAR)&PacketHeader.Checksum,
                                        sizeof(PacketHeader.Checksum));
    if (ReturnCode == KDP_PACKET_TIMEOUT) {
        return KDP_PACKET_TIMEOUT;
    }
    else if (ReturnCode == KDP_PACKET_RESEND) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {
            goto WaitForPacketLeader;
        }
        else {
            goto SendResendPacket;
        }
    }

    //
    // A complete packet header is received.  Check its validity and
    // perform appropriate action depending on packet type.
    //
    if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER ) {
        if (PacketHeader.PacketType == PACKET_TYPE_KD_ACKNOWLEDGE ) {
            //
            // If we received an expected ACK packet and we are not
            // waiting for any new packet, update outgoing packet id
            // and return.  If we are NOT waiting for ACK packet
            // we will keep on waiting.  If the ACK packet
            // is not for the packet we send, ignore it and keep on waiting.
            //
            if (PacketHeader.PacketId !=
                (KdCompNextPacketIdToSend & ~SYNC_PACKET_ID))  {
                goto WaitForPacketLeader;
            }
            else if (PacketType == PACKET_TYPE_KD_ACKNOWLEDGE) {
                KdCompNextPacketIdToSend ^= 1;
                return KDP_PACKET_RECEIVED;
            } else {
                goto WaitForPacketLeader;
            }
        }
        else if (PacketHeader.PacketType == PACKET_TYPE_KD_RESET) {
            //
            // if we received Reset packet, reset the packet control variables
            // and resend earlier packet.
            //
            KdCompNextPacketIdToSend = INITIAL_PACKET_ID;
            KdCompPacketIdExpected = INITIAL_PACKET_ID;
            KdpSendControlPacket(PACKET_TYPE_KD_RESET, 0L);
            return KDP_PACKET_RESEND;
        }
        else if (PacketHeader.PacketType == PACKET_TYPE_KD_RESEND) {
            return KDP_PACKET_RESEND;
        }
        else {
            //
            // Invalid packet header, ignore it.
            //
            goto WaitForPacketLeader;
        }

        //
        // The packet header is for data packet (not control packet).
        //

    }
    else if (PacketType == PACKET_TYPE_KD_ACKNOWLEDGE) {
        //
        // if we are waiting for ACK packet ONLY
        // and we receive a data packet header, check if the packet id
        // is what we expected.  If yes, assume the acknowledge is lost (but
        // sent), ask sender to resend and return with PACKET_RECEIVED.
        //
        if (PacketHeader.PacketId == KdCompPacketIdExpected) {
            KdpSendControlPacket(PACKET_TYPE_KD_RESEND, 0L);
            KdCompNextPacketIdToSend ^= 1;
            return KDP_PACKET_RECEIVED;
        }
        else {
            KdpSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                                 PacketHeader.PacketId);
            goto WaitForPacketLeader;
        }
    }

    //
    // we are waiting for data packet and we received the packet header
    // for data packet. Perform the following checks to make sure
    // it is the packet we are waiting for.
    //

    //
    // Check ByteCount received is valid
    //
    MessageLength = MessageHeader->MaximumLength;
    if ((PacketHeader.ByteCount > (UINT16)PACKET_MAX_SIZE) ||
        (PacketHeader.ByteCount < (UINT16)MessageLength)) {
        goto SendResendPacket;
    }
    *DataLength = PacketHeader.ByteCount - MessageLength;

    //
    // Read the message header.
    //

    ReturnCode = KdpSerialReceiveString((PUCHAR)MessageHeader->Buffer, MessageLength);
    if (ReturnCode != KDP_PACKET_RECEIVED) {
        goto SendResendPacket;
    }
    MessageHeader->Length = (UINT16)MessageLength;

    //
    // Read the message data.
    //

    ReturnCode = KdpSerialReceiveString((PUCHAR)MessageData->Buffer, *DataLength);
    if (ReturnCode != KDP_PACKET_RECEIVED) {
        goto SendResendPacket;
    }
    MessageData->Length = (UINT16)*DataLength;

    //
    // Read packet trailing byte
    //

    ReturnCode = KdpSerialReceiveString(&Input, 1);
    if (ReturnCode != KDP_PACKET_RECEIVED || Input != PACKET_TRAILING_BYTE) {
        goto SendResendPacket;
    }

    //
    // Check PacketType is what we are waiting for.
    //
    if (PacketType != PacketHeader.PacketType) {
        KdpSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                             PacketHeader.PacketId);
        goto WaitForPacketLeader;
    }

    //
    // Check PacketId is valid.
    //
    if (PacketHeader.PacketId == INITIAL_PACKET_ID ||
        PacketHeader.PacketId == (INITIAL_PACKET_ID ^ 1)) {
        if (PacketHeader.PacketId != KdCompPacketIdExpected) {
            KdpSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                                 PacketHeader.PacketId);
            goto WaitForPacketLeader;
        }
    }
    else {
        goto SendResendPacket;
    }

    //
    // Check checksum is valid.
    //
    Checksum = KdpComputeChecksum(MessageHeader->Buffer,
                                  MessageHeader->Length);
    Checksum += KdpComputeChecksum(MessageData->Buffer,
                                   MessageData->Length);
    if (Checksum != PacketHeader.Checksum) {
        goto SendResendPacket;
    }

    //
    // Send Acknowledge byte and the Id of the packet received.
    // Then, update the ExpectId for next incoming packet.
    //
    KdpSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                         PacketHeader.PacketId);

    //
    // We have successfully received the packet so update the
    // packet control variables and return success.
    //
    KdCompPacketIdExpected ^= 1;
    KDDBG2("KdpSerialReceivePacket - got one!\n");
    return KDP_PACKET_RECEIVED;

  SendResendPacket:
    KdpSendControlPacket(PACKET_TYPE_KD_RESEND, 0L);
    goto WaitForPacketLeader;
}

// Returns true if a breakin packet is pending.
// A packet is present if: There is a valid character which matches BREAK_CHAR.
bool KdpSerialPollBreakIn()
{
    KDDBG2("KdpSerialPollBreakIn\n");
    UCHAR Input;
    UINT32 Status = KdpSerialReceiveString(&Input, 1, false);
    KDDBG2("KdpSerialPollByte STATUS %d Input %02x\n", Status, Input);
    if ((Status == KDP_PACKET_RECEIVED) && (Input == BREAKIN_PACKET_BYTE)) {
        KDDBG("KDP_PACKET_RECEIVED\n");
        KdDebuggerNotPresent = false;
        return true;
    }
    return false;
}
//
///////////////////////////////////////////////////////////////// End of File.
