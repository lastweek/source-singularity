
//

//

//

//

//

//
//--

#include "bl.h"

UINT32 BlKdNextPacketId;

VOID
BlKdSpin(
    VOID
    )


//

//

//
//--

{
    static UINT8 state = 0;

    //
    
    //

    *((UINT16 *)(ULONG_PTR)0xb809e) = 0x2f00 + ("+-|*" [state++ & 0x3]);
}

UINT32
BlKdComputeChecksum(
    PCVOID Buffer,
    UINT32 Length
    )


//

//

//

//

//

//

//

//
//--

{
    UINT32 Checksum;
    UINT32 Index;

    Checksum = 0;

    for (Index = 0; Index < Length; Index += 1) {

        Checksum += ((PCHAR)Buffer)[Index];
    }

    return Checksum;
}

BOOLEAN
BlKdPrintString(
    PCSTR String
    )


//

//

//

//

//

//


//
//--

{
    KD_DEBUG_IO Packet;
    UINT32 StringLength;

    StringLength = BlRtlStringLength(String);

    if (StringLength >= 0xFFFF) {

        return FALSE;
    }

    BlRtlZeroMemory(&Packet, sizeof(Packet));

    Packet.ApiNumber = KD_API_PRINT_STRING;
    Packet.u1.PrintString.LengthOfString = StringLength;

    if (BlKdComPort != 0) {

        return BlKdComSendPacket(KD_PACKET_TYPE_KD_DEBUG_IO,
                                 &Packet,
                                 sizeof(Packet),
                                 String,
                                 (UINT16) StringLength + 1);

    }
    else if (BlPciOhci1394BaseAddress != 0) {

        return BlKd1394SendPacket(KD_PACKET_TYPE_KD_DEBUG_IO,
                                  &Packet,
                                  sizeof(Packet),
                                  String,
                                  (UINT16) StringLength + 1);

    }

    return FALSE;
}

BOOLEAN
BlKdPrintf(
    PCSTR Format,
    ...
    )


//

//

//

//

//

//

//


//
//--

{
    va_list ArgumentList;
    CHAR Buffer[4096];

    va_start(ArgumentList, Format);

    if (BlRtlFormatString(Buffer,
                          sizeof(Buffer),
                          Format,
                          ArgumentList) == FALSE) {

        return FALSE;
    }

    BlKdPrintString(Buffer);

    return TRUE;
}

VOID
BlKdInitialize(
    VOID
    )


//

//

//
//--

{
    //
    
    //

    if (BlKdComConnect() != FALSE) {

#if KD_VERBOSE

        BlVideoPrintf("KD: Connected to COM%u\n", BlKdComPort);

#endif

        return;
    }

    //
    
    //

    if (BlKd1394Connect() != FALSE) {

#if KD_VERBOSE

        BlVideoPrintf("KD: Connected to 1394:%u\n", 0);

#endif

        return;
    }

    return;
}
