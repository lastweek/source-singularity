///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  debug.cpp: runtime support for debugging
//

#ifndef IN
#define IN
#endif
#ifndef OUT
#define OUT
#endif

// Define the maximum number of retries for packet sends.
//
#define BD_MAXIMUM_RETRIES 20

// Define packet waiting status codes.
//
#define BD_PACKET_RECEIVED 0
#define BD_PACKET_TIMEOUT 1
#define BD_PACKET_RESEND 2

typedef struct _STRING {
    UINT16  Length;
    UINT16  MaximumLength;
    PUINT8  Buffer;
} STRING, *PSTRING;

//======================================================================
// Selected structs and defines used by the KD protocol
//

//
// If the packet type is PACKET_TYPE_KD_DEBUG_IO, then
// the format of the packet data is as follows:
//

#define DbgKdPrintStringApi     0x00003230L

//
// For get string, the Null terminated prompt string
// immediately follows the message. The LengthOfStringRead
// field initially contains the maximum number of characters
// to read. Upon reply, this contains the number of bytes actually
// read. The data read immediately follows the message.
//
//
typedef struct _DBGKD_DEBUG_IO {
    UINT32 ApiNumber;
    UINT16 ProcessorLevel;
    UINT16 Processor;
    UINT32 LengthOfString;
    UINT32 LengthOfStringRead;
} DBGKD_DEBUG_IO, *PDBGKD_DEBUG_IO;

//
// DbgKd APIs are for the portable kernel debugger
//

//
// KD_PACKETS are the low level data format used in KD. All packets
// begin with a packet leader, byte count, packet type. The sequence
// for accepting a packet is:
//
//  - read 4 bytes to get packet leader.  If read times out (10 seconds)
//    with a short read, or if packet leader is incorrect, then retry
//    the read.
//
//  - next read 2 byte packet type.  If read times out (10 seconds) with
//    a short read, or if packet type is bad, then start again looking
//    for a packet leader.
//
//  - next read 4 byte packet Id.  If read times out (10 seconds)
//    with a short read, or if packet Id is not what we expect, then
//    ask for resend and restart again looking for a packet leader.
//
//  - next read 2 byte count.  If read times out (10 seconds) with
//    a short read, or if byte count is greater than PACKET_MAX_SIZE,
//    then start again looking for a packet leader.
//
//  - next read 4 byte packet data checksum.
//
//  - The packet data immediately follows the packet.  There should be
//    ByteCount bytes following the packet header.  Read the packet
//    data, if read times out (10 seconds) then start again looking for
//    a packet leader.
//

typedef struct _KD_PACKET {
    UINT32 PacketLeader;
    UINT16 PacketType;
    UINT16 ByteCount;
    UINT32 PacketId;
    UINT32 Checksum;
} KD_PACKET, *PKD_PACKET;

#define PACKET_MAX_SIZE     4000
#define INITIAL_PACKET_ID   0x80800000  // Don't use 0
#define SYNC_PACKET_ID      0x00000800  // Or in with INITIAL_PACKET_ID
                                        // to force a packet ID reset.

//
// Packet lead in sequence
//

#define PACKET_LEADER                   0x30303030 //0x77000077
#define PACKET_LEADER_BYTE              0x30

#define CONTROL_PACKET_LEADER           0x69696969
#define CONTROL_PACKET_LEADER_BYTE      0x69

//
// Packet Trailing Byte
//

#define PACKET_TRAILING_BYTE            0xAA

//
// Packet Types
//

#define PACKET_TYPE_KD_DEBUG_IO         3
#define PACKET_TYPE_KD_ACKNOWLEDGE      4       // Packet-control type
#define PACKET_TYPE_KD_RESEND           5       // Packet-control type
#define PACKET_TYPE_KD_RESET            6       // Packet-control type
#define PACKET_TYPE_MAX                 12

//
// Status Constants for reading data from comport
//

#define DBGKD_64BIT_PROTOCOL_VERSION2 6

//
// Communication functions (comio.c)
//

static
UINT32
BdComputeChecksum(
    IN PUINT8 Buffer,
    IN UINT32 Length
    );

static
UINT16
BdReceivePacketLeader(
    IN UINT32 PacketType,
    OUT PUINT32 PacketLeader
    );

static
void
BdSendControlPacket(
    IN UINT16 PacketType,
    IN UINT32 PacketId
    );

static
UINT32
BdReceivePacket(
    IN UINT32 ExpectedPacketType,
    OUT PSTRING MessageHeader,
    OUT PSTRING MessageData,
    OUT PUINT32 DataLength
    );

static
void
BdSendPacket(
    IN UINT32 PacketType,
    IN PSTRING MessageHeader,
    IN PSTRING MessageData
    );

static
UINT32
BdReceiveString(
    OUT PUINT8 Destination,
    IN UINT32 Length
    );

static
void
BdSendString(
    IN PUINT8 Source,
    IN UINT32 Length
    );

static
void
BdSendControlPacket(
    IN UINT16 PacketType,
    IN UINT32 PacketId
    );

// Debugger enabled and present.
//
static BOOL BdDebuggerNotPresent = 0;

// Next packet id to send and next packet id to expect.
//
static UINT32 BdPacketIdExpected;
static UINT32 BdNextPacketIdToSend;

// Number of retries and the retry count.
//
static UINT32 BdNumberRetries = BD_MAXIMUM_RETRIES;
static UINT32 BdRetryCount = BD_MAXIMUM_RETRIES;

//////////////////////////////////////////////////////////////////////////////

static
UINT32
BdComputeChecksum(
    IN PUINT8 Buffer,
    IN UINT32 Length
    )

//++
//
//Routine Description:
//
//  This routine computes the checksum of the specified buffer.
//
//Arguments:
//
//  Buffer - Supplies a pointer to the buffer.
//
//  Length - Supplies the length of the buffer.
//
//Return Value:
//
//  A UINT32 is return as the checksum for the input string.
//
//--  

{

    UINT32 Checksum = 0;

    while (Length > 0) {
        Checksum = Checksum + (UINT32)*Buffer++;
        Length--;
    }

    return Checksum;
}

static
UINT16
BdReceivePacketLeader(
                      IN UINT32 /* PacketType */,
                      OUT PUINT32 PacketLeader
                     )

//++
//
//Routine Description:
//
//  This routine waits for a packet header leader.
//
//Arguments:
//
//  PacketType - supplies the type of packet we are expecting.
//
//  PacketLeader - supplies a pointer to a ulong variable to receive
//                 packet leader bytes.
//
//Return Value:
//
//  BD_PACKET_RESEND - if resend is required.
//  BD_PAKCET_TIMEOUT - if timeout.
//  BD_PACKET_RECEIVED - if packet received.
//
//--  

{

    UINT8 Input, PreviousByte = 0;
    UINT32 PacketId = 0;
    UINT32 Index;
    UINT32 ReturnCode;

    // NOTE - With all the interrupts being off, it is very hard
    // to implement the actual timeout code. (Maybe, by reading the CMOS.)
    // Here we use a loop count to wait about 3 seconds.  The CpGetByte
    // will return with error code = CP_GET_NODATA if it cannot find data
    // byte within 1 second. Kernel debugger's timeout period is 5 seconds.
    //
    Index = 0;
    do {
        ReturnCode = BdPortGetByte(&Input);
        if (ReturnCode == CP_GET_NODATA) {
            return BD_PACKET_TIMEOUT;
        } else if (ReturnCode == CP_GET_ERROR) {
            Index = 0;
            continue;

        } else {                    // if (ReturnCode == CP_GET_SUCCESS)
            if ( Input == PACKET_LEADER_BYTE ||
                 Input == CONTROL_PACKET_LEADER_BYTE ) {
                if ( Index == 0 ) {
                    PreviousByte = Input;
                    Index++;
                } else if (Input == PreviousByte ) {
                    Index++;
                } else {
                    PreviousByte = Input;
                    Index = 1;
                }
            } else {

                Index = 0;
            }
        }
    } while ( Index < 4 );

    // return the packet leader and FALSE to indicate no resend is needed.
    //
    if ( Input == PACKET_LEADER_BYTE ) {
        *PacketLeader = PACKET_LEADER;

    } else {
        *PacketLeader = CONTROL_PACKET_LEADER;
    }

    BdDebuggerNotPresent = 0;
    return BD_PACKET_RECEIVED;
}

static
void
BdSendControlPacket(
    IN UINT16 PacketType,
    IN UINT32 PacketId
    )

//++
//
//Routine Description:
//
//  This routine sends a control packet to the host machine that is running the
//  kernel debugger and waits for an ACK.
//
//Arguments:
//
//  PacketType - Supplies the type of packet to send.
//
//  PacketId - Supplies packet id, optionally.
//
//Return Value:
//
//  None.
//
//--  

{

    KD_PACKET PacketHeader;

    // Initialize and send the packet header.
    //
    PacketHeader.PacketLeader = CONTROL_PACKET_LEADER;
    if (PacketId != 0) {
        PacketHeader.PacketId = PacketId;
    }

    PacketHeader.ByteCount = 0;
    PacketHeader.Checksum = 0;
    PacketHeader.PacketType = PacketType;
    BdSendString((PUINT8)&PacketHeader, sizeof(KD_PACKET));
    return;
}

static
UINT32
BdReceivePacket(
    IN UINT32 PacketType,
    OUT PSTRING MessageHeader,
    OUT PSTRING MessageData,
    OUT PUINT32 DataLength
    )

//++
//
//Routine Description:
//
//  This routine receives a packet from the host machine that is running
//  the kernel debugger UI.  This routine is ALWAYS called after packet being
//  sent by caller.  It first waits for ACK packet for the packet sent and
//  then waits for the packet desired.
//
//  N.B. If caller is BdrintString, the parameter PacketType is
//     PACKET_TYPE_KD_ACKNOWLEDGE.  In this case, this routine will return
//     right after the ack packet is received.
//
//Arguments:
//
//  PacketType - Supplies the type of packet that is excepted.
//
//  MessageHeader - Supplies a pointer to a string descriptor for the input
//      message.
//
//  MessageData - Supplies a pointer to a string descriptor for the input data.
//
//  DataLength - Supplies pointer to UINT32 to receive length of recv. data.
//
//Return Value:
//
//  BD_PACKET_RESEND - if resend is required.
//  BD_PAKCET_TIMEOUT - if timeout.
//  BD_PACKET_RECEIVED - if packet received.
//
//--  

{

    UINT8 Input;
    UINT32 MessageLength;
    KD_PACKET PacketHeader;
    UINT32 ReturnCode;
    UINT32 Checksum;

WaitForPacketLeader:

    //
    // Read Packet Leader
    //

    ReturnCode = BdReceivePacketLeader(PacketType, &PacketHeader.PacketLeader);

    //
    // If we can successfully read packet leader, it has high possibility that
    // kernel debugger is alive.  So reset count.
    //

    if (ReturnCode != BD_PACKET_TIMEOUT) {
        BdNumberRetries = BdRetryCount;
    }
    if (ReturnCode != BD_PACKET_RECEIVED) {
        return ReturnCode;
    }

    //
    // Read packet type.
    //

    ReturnCode = BdReceiveString((PUINT8)&PacketHeader.PacketType,
                                 sizeof(PacketHeader.PacketType));

    if (ReturnCode == CP_GET_NODATA) {
        return BD_PACKET_TIMEOUT;

    } else if (ReturnCode == CP_GET_ERROR) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {

            //
            // If read error and it is for a control packet, simply
            // pretend that we have not seen this packet.  Hopefully
            // we will receive the packet we desire which automatically acks
            // the packet we just sent.
            //

            goto WaitForPacketLeader;

        } else {

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
        return BD_PACKET_RESEND;
    }

    //
    // Read data length.
    //

    ReturnCode = BdReceiveString((PUINT8)&PacketHeader.ByteCount,
                                 sizeof(PacketHeader.ByteCount));

    if (ReturnCode == CP_GET_NODATA) {
        return BD_PACKET_TIMEOUT;
    } else if (ReturnCode == CP_GET_ERROR) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {
            goto WaitForPacketLeader;
        } else {
            goto SendResendPacket;
        }
    }

    //
    // Read Packet Id.
    //

    ReturnCode = BdReceiveString((PUINT8)&PacketHeader.PacketId,
                                 sizeof(PacketHeader.PacketId));

    if (ReturnCode == CP_GET_NODATA) {
        return BD_PACKET_TIMEOUT;
    } else if (ReturnCode == CP_GET_ERROR) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {
            goto WaitForPacketLeader;
        } else {
            goto SendResendPacket;
        }
    }

    //
    // Read packet checksum.
    //

    ReturnCode = BdReceiveString((PUINT8)&PacketHeader.Checksum,
                                 sizeof(PacketHeader.Checksum));

    if (ReturnCode == CP_GET_NODATA) {
        return BD_PACKET_TIMEOUT;

    } else if (ReturnCode == CP_GET_ERROR) {
        if (PacketHeader.PacketLeader == CONTROL_PACKET_LEADER) {
            goto WaitForPacketLeader;
        } else {
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
                (BdNextPacketIdToSend & ~SYNC_PACKET_ID))  {
                goto WaitForPacketLeader;

            } else if (PacketType == PACKET_TYPE_KD_ACKNOWLEDGE) {
                BdNextPacketIdToSend ^= 1;
                return BD_PACKET_RECEIVED;

            } else {
                goto WaitForPacketLeader;
            }

        } else if (PacketHeader.PacketType == PACKET_TYPE_KD_RESET) {

            //
            // if we received Reset packet, reset the packet control variables
            // and resend earlier packet.
            //

            BdNextPacketIdToSend = INITIAL_PACKET_ID;
            BdPacketIdExpected = INITIAL_PACKET_ID;
            BdSendControlPacket(PACKET_TYPE_KD_RESET, 0L);
            return BD_PACKET_RESEND;

        } else if (PacketHeader.PacketType == PACKET_TYPE_KD_RESEND) {
            return BD_PACKET_RESEND;

        } else {

            //
            // Invalid packet header, ignore it.
            //

            goto WaitForPacketLeader;
        }

    //
    // The packet header is for data packet (not control packet).
    //

    } else if (PacketType == PACKET_TYPE_KD_ACKNOWLEDGE) {

        //
        // if we are waiting for ACK packet ONLY
        // and we receive a data packet header, check if the packet id
        // is what we expected.  If yes, assume the acknowledge is lost (but
        // sent), ask sender to resend and return with PACKET_RECEIVED.
        //

        if (PacketHeader.PacketId == BdPacketIdExpected) {
            BdSendControlPacket(PACKET_TYPE_KD_RESEND, 0L);
            BdNextPacketIdToSend ^= 1;
            return BD_PACKET_RECEIVED;

        } else {
            BdSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                                PacketHeader.PacketId);

            goto WaitForPacketLeader;
        }
    }

    //
    // we are waiting for data packet and we received the packet header
    // for data packet. Perform the following checks to make sure
    // it is the packet we are waiting for.
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

    ReturnCode = BdReceiveString(MessageHeader->Buffer, MessageLength);
    if (ReturnCode != CP_GET_SUCCESS) {
        goto SendResendPacket;
    }

    MessageHeader->Length = (UINT16)MessageLength;

    //
    // Read the message data.
    //

    ReturnCode = BdReceiveString(MessageData->Buffer, *DataLength);
    if (ReturnCode != CP_GET_SUCCESS) {
        goto SendResendPacket;
    }

    MessageData->Length = (UINT16)*DataLength;

    //
    // Read packet trailing byte
    //

    ReturnCode = BdPortGetByte(&Input);
    if (ReturnCode != CP_GET_SUCCESS || Input != PACKET_TRAILING_BYTE) {
        goto SendResendPacket;
    }

    //
    // Check PacketType is what we are waiting for.
    //

    if (PacketType != PacketHeader.PacketType) {
        BdSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                             PacketHeader.PacketId
                             );
        goto WaitForPacketLeader;
    }

    //
    // Check PacketId is valid.
    //

    if (PacketHeader.PacketId == INITIAL_PACKET_ID ||
        PacketHeader.PacketId == (INITIAL_PACKET_ID ^ 1)) {
        if (PacketHeader.PacketId != BdPacketIdExpected) {
            BdSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                                 PacketHeader.PacketId
                                 );
            goto WaitForPacketLeader;
        }

    } else {
        goto SendResendPacket;
    }

    //
    // Check checksum is valid.
    //

    Checksum = BdComputeChecksum(MessageHeader->Buffer,
                                 MessageHeader->Length);


    Checksum += BdComputeChecksum(MessageData->Buffer,
                                  MessageData->Length);

    if (Checksum != PacketHeader.Checksum) {
        goto SendResendPacket;
    }

    //
    // Send Acknowledge byte and the Id of the packet received.
    // Then, update the ExpectId for next incoming packet.
    //

    BdSendControlPacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                        PacketHeader.PacketId);

    //
    // We have successfully received the packet so update the
    // packet control variables and return success.
    //

    BdPacketIdExpected ^= 1;
    return BD_PACKET_RECEIVED;

SendResendPacket:
    BdSendControlPacket(PACKET_TYPE_KD_RESEND, 0L);
    goto WaitForPacketLeader;
}

static
void
BdSendPacket(
    IN UINT32 PacketType,
    IN PSTRING MessageHeader,
    IN PSTRING MessageData
    )

//++
//
//Routine Description:
//
//  This routine sends a packet to the host machine that is running the
//  kernel debugger and waits for an ACK.
//
//Arguments:
//
//  PacketType - Supplies the type of packet to send.
//
//  MessageHeader - Supplies a pointer to a string descriptor that describes
//      the message information.
//
//  MessageData - Supplies a pointer to a string descriptor that describes
//      the optional message data.
//
//Return Value:
//
//  None.
//
//--  

{

    KD_PACKET PacketHeader;
    UINT32 MessageDataLength;
    UINT32 ReturnCode;
    PDBGKD_DEBUG_IO DebugIo;

    if (MessageData != NULL) {
        MessageDataLength = MessageData->Length;
        PacketHeader.Checksum = BdComputeChecksum(MessageData->Buffer,
                                                  MessageData->Length);

    } else {
        MessageDataLength = 0;
        PacketHeader.Checksum = 0;
    }

    PacketHeader.Checksum += BdComputeChecksum(MessageHeader->Buffer,
                                               MessageHeader->Length);

    //
    // Initialize and send the packet header.
    //

    PacketHeader.PacketLeader = PACKET_LEADER;
    PacketHeader.ByteCount = (UINT16)(MessageHeader->Length + MessageDataLength);
    PacketHeader.PacketType = (UINT16)PacketType;
    BdNumberRetries = BdRetryCount;
    do {
        if (BdNumberRetries == 0) {

            //
            // If the packet is not for reporting exception, we give up
            // and declare debugger not present.
            //

            if (PacketType == PACKET_TYPE_KD_DEBUG_IO) {
                DebugIo = (PDBGKD_DEBUG_IO)MessageHeader->Buffer;
                if (DebugIo->ApiNumber == DbgKdPrintStringApi) {
                    BdDebuggerNotPresent = 1;
                    BdNextPacketIdToSend = INITIAL_PACKET_ID | SYNC_PACKET_ID;
                    BdPacketIdExpected = INITIAL_PACKET_ID;
                    return;
                }
            }
        }

        //
        // Setting PacketId has to be in the do loop in case Packet Id was
        // reset.
        //

        PacketHeader.PacketId = BdNextPacketIdToSend;
        BdSendString((PUINT8)&PacketHeader, sizeof(KD_PACKET));

        //
        // Output message header.
        //

        BdSendString(MessageHeader->Buffer, MessageHeader->Length);

        //
        // Output message data.
        //

        if ( MessageDataLength ) {
            BdSendString(MessageData->Buffer, MessageData->Length);
        }

        //
        // Output a packet trailing byte
        //

        BdPortPutByte(PACKET_TRAILING_BYTE);

        //
        // Wait for the Ack Packet
        //

        ReturnCode = BdReceivePacket(PACKET_TYPE_KD_ACKNOWLEDGE,
                                     NULL,
                                     NULL,
                                     NULL);

        if (ReturnCode == BD_PACKET_TIMEOUT) {
            BdNumberRetries--;
        }

    } while (ReturnCode != BD_PACKET_RECEIVED);

    //
    // Reset Sync bit in packet id.  The packet we sent may have Sync bit set
    //

    BdNextPacketIdToSend &= ~SYNC_PACKET_ID;

    //
    // Since we are able to talk to debugger, the retrycount is set to
    // maximum value.
    //

    BdRetryCount = BD_MAXIMUM_RETRIES;
}

static
UINT32
BdReceiveString(
    OUT PUINT8 Destination,
    IN UINT32 Length
    )

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
//
//Return Value:
//
//  CP_GET_SUCCESS is returned if string is successfully read from the
//      kernel debugger line.
//  CP_GET_ERROR is returned if error encountered during reading.
//  CP_GET_NODATA is returned if timeout.
//
//--  

{

    UINT8 Input;
    UINT32 ReturnCode;

    //
    // Read bytes until either an error is encountered or the entire string
    // has been read.
    //
    while (Length > 0) {
        ReturnCode = BdPortGetByte(&Input);
        if (ReturnCode != CP_GET_SUCCESS) {
            return ReturnCode;
        } else {
            *Destination++ = Input;
            Length -= 1;
        }
    }

    return CP_GET_SUCCESS;
}

static
void
BdSendString(
    IN PUINT8 Source,
    IN UINT32 Length
    )

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

{

    UINT8 Output;

    //
    // Write bytes to the kernel debugger port.
    //

    while (Length > 0) {
        Output = *Source++;
        BdPortPutByte(Output);
        Length -= 1;
    }

    return;
}

void BdPrintString(char *Output, UINT Length)

//++
//
//Routine Description:
//
//  This routine prints a string.
//
//Arguments:
//
//  Output - Supplies a pointer to a string descriptor for the output string.
//
//--  

{

    STRING MessageData;
    STRING MessageHeader;
    DBGKD_DEBUG_IO DebugIo;

    if (BdDebuggerNotPresent) {
        return;
    }

    // If the total message length is greater than the maximum packet size,
    // then truncate the output string.
    //
    if ((sizeof(DBGKD_DEBUG_IO) + Length) > PACKET_MAX_SIZE) {
        Length = PACKET_MAX_SIZE - sizeof(DBGKD_DEBUG_IO);
    }

    // Construct the print string message and message descriptor.
    //
    DebugIo.ApiNumber = DbgKdPrintStringApi;
    DebugIo.ProcessorLevel = 0;
    DebugIo.Processor = 0;
    DebugIo.LengthOfString = Length;
    MessageHeader.Length = sizeof(DBGKD_DEBUG_IO);
    MessageHeader.Buffer = (PUINT8)&DebugIo;

    // Construct the print string data and data descriptor.
    //
    MessageData.Length = (UINT16)Length;
    MessageData.Buffer = (PUINT8)Output;

    // Send packet to the kernel debugger on the host machine.
    //
    BdSendPacket(PACKET_TYPE_KD_DEBUG_IO, &MessageHeader, &MessageData);
}

bool BdInitDebugger(bool present)
{
    // Configure debugger state based on presence of transport layer.
    //
    if (present) {
        BdDebuggerNotPresent = 0;

        // Initialize the ID for the NEXT packet to send and the Expect
        // ID of next incoming packet.
        //
        BdNextPacketIdToSend = INITIAL_PACKET_ID | SYNC_PACKET_ID;
        BdPacketIdExpected = INITIAL_PACKET_ID;

        // Number of retries and the retry count.
        //
        BdNumberRetries = 5;
        BdRetryCount = 5;

        return 1;
    }

    BdDebuggerNotPresent = 1;
    return 0;
}
