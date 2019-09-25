//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkdcom.cpp: pc-compatible com port serial transport.
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

////////////////////////////////////////////////////////// COM PORT Constants.
//
#define COM1_PORT           0x03f8
#define COM2_PORT           0x02f8
#define COM3_PORT           0x03e8
#define COM4_PORT           0x02e8

#define COM_DAT             0x00
#define COM_IEN             0x01    // interrupt enable register
#define COM_FCR             0x02    // FIFO Control Register
#define COM_LCR             0x03    // line control registers
#define COM_MCR             0x04    // modem control reg
#define COM_LSR             0x05    // line status register
#define COM_MSR             0x06    // modem status register
#define COM_SCR             0x07    // scratch register
#define COM_DLL             0x00    // divisor latch least sig
#define COM_DLM             0x01    // divisor latch most sig

const UINT16 BaudRate = 1;          // 115200 bps

#define COM_DATRDY          0x01
#define COM_OUTRDY          0x20

#define LC_DLAB             0x80

#define CLOCK_RATE          0x1C200 // USART clock rate

#define MC_DTRRTS           0x03    // Control bits to assert DTR and RTS
#define MS_DSRCTSCD         0xB0    // Status bits for DSR, CTS and CD
#define MS_CD               0x80

#define SERIAL_MCR_LOOP     0x10    // enables loopback testing mode
#define SERIAL_MCR_OUT1     0x04    // general purpose output.
#define SERIAL_MSR_CTS      0x10    // (complemented) state of clear to send (CTS).
#define SERIAL_MSR_DSR      0x20    // (complemented) state of data set ready (DSR).
#define SERIAL_MSR_RI       0x40    // (complemented) state of ring indicator (RI).
#define SERIAL_MSR_DCD      0x80    // (complemented) state of data carrier detect (DCD).

//
// Globals
//
static UINT16 KdBasePort = COM2_PORT;

////////////////////////////////////////////////// Serial Port Input & Output.
//

static UINT8 KdReadInt8(UINT16 port)
{
    return __inbyte(port);
}

static void KdWriteInt8(UINT16 port, UINT8 value)
{
    __outbyte(port, value);
}

bool KdpSerialInit(Class_Microsoft_Singularity_Hal_Platform *nbi)
// Initializes the communication port (baud rate, parity etc.)
{
    KdBasePort = (UINT16)nbi->DebugBasePort;
    if (KdBasePort < 0x100) {
        KdBasePort = 0;
        return false;
    }

    // turn off interrupts
    KdWriteInt8(KdBasePort + COM_LCR, 0x00);
    KdWriteInt8(KdBasePort + COM_IEN, 0x00);

    // Turn on DTS/RTS
    KdWriteInt8(KdBasePort + COM_MCR, MC_DTRRTS); // Needed for VirtualPC PIPE/Serial

    // Turn on FIFO
    //KdWriteInt8(KdBasePort + COM_FCR, 1);

    // Set the baud rate
    KdWriteInt8(KdBasePort + COM_LCR, LC_DLAB);  // Divisor latch access bit
    KdWriteInt8(KdBasePort + COM_DLM, (UINT8)(BaudRate >> 8));
    KdWriteInt8(KdBasePort + COM_DLL, (UINT8)(BaudRate & 0xFF));

    // initialize the LCR
    KdWriteInt8(KdBasePort + COM_LCR, 0x03);
    // 8 data bits, 1 stop bit, no parity, no break

    // See if the 16450/16550 scratch register is available.
    // If not, we'll assume the serial port doesn't really exist.
    KdWriteInt8(KdBasePort + COM_SCR, 0xff);
    UINT8 a1 = KdReadInt8(KdBasePort + COM_SCR);
    KdWriteInt8(KdBasePort + COM_SCR, 0x00);
    UINT8 a2 = KdReadInt8(KdBasePort + COM_SCR);

    return (bool) ((a1 == (UINT8)0xff) && (a2 == (UINT8)0x00));
}

//
// Define wait timeout value.
//
#define TIMEOUT_COUNT 1024 * 1000
// #define TIMEOUT_COUNT 1024 * 200
//#define TIMEOUT_COUNT 15

KDP_STATUS KdpSerialGetByte(OUT PUCHAR Input, BOOL WaitForByte)
{
    UCHAR lsr;
    UCHAR value;
    UINT32 limitcount = WaitForByte ? TIMEOUT_COUNT : 1;

    UCHAR msr;
    msr = KdReadInt8(KdBasePort + COM_MSR);
    KDDBG2("MSR %02x\n", msr);

    while (limitcount != 0) {
        limitcount--;

        lsr = KdReadInt8(KdBasePort + COM_LSR);
        KDDBG2("LSR %02x\n", lsr);
        if (lsr & COM_DATRDY) {
            value = KdReadInt8(KdBasePort + COM_DAT);
            *Input = value & 0xff;
            return KDP_PACKET_RECEIVED;
        }
    }
    return KDP_PACKET_TIMEOUT;
}


void KdpSerialPutByte(IN UCHAR Output)
{
    // wait for the com port to be ready
    while ((KdReadInt8( KdBasePort + COM_LSR ) & COM_OUTRDY) == 0) {
        // nop;
    }

    // write a single char
    KdWriteInt8(KdBasePort + COM_DAT, Output);
}
//
///////////////////////////////////////////////////////////////// End of File.
