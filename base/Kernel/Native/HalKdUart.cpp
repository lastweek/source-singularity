//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.   All rights reserved.
//
//  File:   halkduart.cpp: UART serial transport.
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

///////////////////////////////////////////////////////////////// Serial Port.
//
#define OMAP_CLOCK_RATE 2995200

// Define COM Port registers.
#define COM_DAT 0x00
#define COM_DLL 0x00            // Divisor Latch (LSB).
#define COM_IEN 0x01            // Interrupt enable register
#define COM_DLM 0x01            // Divisor Latch (MSB).
#define COM_FCR 0x02            // FIFO Control Register.
#define COM_LCR 0x03            // Line Control Register.
#define COM_MCR 0x04            // Modem Control Register.
#define COM_LSR 0x05            // Line Status Register.
#define COM_MSR 0x06            // Modem Status Register.
#define COM_SCR 0x07            // Scratch Register.

#define OMAP_UART_MDR1    0x8
#define OMAP_UART_IER     0x1
#define OMAP_UART_EFR     0x2

// Define bits in the FIFO Control Register (FCR).
#define FCR_ENABLE                0x01
#define FCR_CLEAR_RECEIVE         0x02
#define FCR_CLEAR_TRANSMIT        0x04

// Define bits in the Line Control Register (LCR).
#define LCR_DATA_SIZE             0x03
#define LCR_DLAB                  0x80

// Define bits in the Modem Control Register (MCR).
#define MCR_DATA_TERMINAL_READY   0x01
#define MCR_REQUEST_TO_SEND       0x02
#define MCR_OUT1                  0x04
#define MCR_OUT2                  0x08
#define MCR_LOOPBACK              0x10
#define MCR_INITIALIZE            (MCR_DATA_TERMINAL_READY | MCR_REQUEST_TO_SEND)

// Define bits in the Line Status Register (LSR).
#define LSR_DATA_AVAILABLE        0x01
#define LSR_OVERRUN_ERROR         0x02
#define LSR_PARITY_ERROR          0x04
#define LSR_FRAMING_ERROR         0x08
#define LSR_BREAK_SIGNAL          0x10
#define LSR_THR_EMPTY             0x20
#define LSR_THR_LINE_IDLE         0x40


// Defined bits in the Modem Status Register (MSR).
#define MSR_DELTA_CLEAR_TO_SEND   0x01
#define MSR_DELTA_DATA_SET_READY  0x02
#define MSR_DELTA_RING_INDICATOR  0x04
#define MSR_DELTA_CARRIER_DETECT  0x08
#define MSR_CLEAR_TO_SEND         0x10
#define MSR_DATA_SET_READY        0x20
#define MSR_RING_INDICATOR        0x40
#define MSR_CARRIER_DETECT        0x80

//
// Globals
//
static const uint32 BaudRate = 115200;
static uint32 * uartBase = 0;

////////////////////////////////////////////////// Serial Port Input & Output.
//
static inline void WriteReg8(volatile void * addr, uint8 value)
{
    ((volatile uint8 *)addr)[0] = value;
}

static inline uint8 ReadReg8(volatile void * addr)
{
    return ((volatile uint8 *)addr)[0];
}

static void UartSetBaudRate(uint32 * BaseAddress, uint32 BaudRate)
{
    uint32 Divisor = OMAP_CLOCK_RATE / BaudRate;
    uint8 Enhanced;

    // Disable UART
    WriteReg8(BaseAddress + OMAP_UART_MDR1, 0x7);

    // Set register configuration mode B
    WriteReg8(BaseAddress + COM_LCR, 0xBF);

    // Save enhanced mode
    Enhanced = ReadReg8(BaseAddress + OMAP_UART_EFR);
    WriteReg8(BaseAddress + OMAP_UART_EFR, Enhanced | (1 << 4));

    // switch to operational mode
    WriteReg8(BaseAddress + COM_LCR, 0);

    // clear sleep mode
    WriteReg8(BaseAddress + OMAP_UART_IER, 0);

    // Set register configuration mode B
    WriteReg8(BaseAddress + COM_LCR, 0xBF);

    // Write the divisor value to DLL and DLM.
    WriteReg8(BaseAddress + COM_DLM, (uint8)((Divisor >> 8) & 0xff));
    WriteReg8(BaseAddress + COM_DLL, (uint8)(Divisor & 0xff));

    // Restore enhanced mode
    WriteReg8(BaseAddress + OMAP_UART_EFR, Enhanced);

    // Reset the Line Control Register.
    WriteReg8(BaseAddress + COM_LCR, LCR_DATA_SIZE);

    // Enable UART
    WriteReg8(BaseAddress + OMAP_UART_MDR1, 0);
}

bool KdpSerialInit(Class_Microsoft_Singularity_Hal_Platform *nbi)
// Initializes the communication port (baud rate, parity etc.)
{
    if (nbi->DebugBasePort < 0x100) {
        return false;

    }
    uartBase = (uint32 *)nbi->DebugBasePort;

    // Set the default baudrate.
    UartSetBaudRate(uartBase, BaudRate);

    // Set DLAB to zero.  DLAB controls the meaning of the first two
    // registers.  When zero, the first register is used for all byte transfer
    // and the second register controls device interrupts.
    //
    WriteReg8(uartBase + COM_LCR,
              ReadReg8(uartBase + COM_LCR) & ~LCR_DLAB);

    // Disable device interrupts.  This implementation will handle state
    // transitions by request only.
    //
    WriteReg8(uartBase + COM_IEN, 0);

    // Reset and disable the FIFO queue.
    // N.B. FIFO will be reenabled before returning from this routine.
    //
    WriteReg8(uartBase + COM_FCR, FCR_CLEAR_TRANSMIT | FCR_CLEAR_RECEIVE);

    // Configure the Modem Control Register.  Disabled device interrupts,
    // turn off loopback.
    //
    WriteReg8(uartBase + COM_MCR,
              ReadReg8(uartBase + COM_MCR) & MCR_INITIALIZE);

    // Initialize the Modem Control Register.  Indicate to the device that
    // we are able to send and receive data.
    //
    WriteReg8(uartBase + COM_MCR, MCR_INITIALIZE);

    // Enable the FIFO queues.
    WriteReg8(uartBase + COM_FCR, FCR_ENABLE);

    return true;
}

//
// Define wait timeout value.
//
#define TIMEOUT_COUNT 1024 * 30
// #define TIMEOUT_COUNT 1024 * 200
//#define TIMEOUT_COUNT 15

KDP_STATUS KdpSerialGetByte(OUT PUCHAR Input, BOOL WaitForByte)
{
    UINT8 lsr;
    UINT8 value;
    UINT32 limitcount = (WaitForByte) ? TIMEOUT_COUNT : 1;

    UINT8 msr;
    msr = ReadReg8(uartBase + COM_MSR);
    KDDBG2("MSR %02x\n", msr);

    while (limitcount != 0) {
        limitcount--;

        lsr = ReadReg8(uartBase + COM_LSR);
        KDDBG2("LSR %02x\n", lsr);
        if (lsr & LSR_DATA_AVAILABLE) {
            value = ReadReg8(uartBase + COM_DAT);
            *Input = (UINT8)(value & 0xff);
            return KDP_PACKET_RECEIVED;
        }
    }
    return KDP_PACKET_TIMEOUT;
}


void KdpSerialPutByte(IN UCHAR Output)
{
    // Loop until the device is ready for output
    while ((ReadReg8(uartBase + COM_LSR) & LSR_THR_EMPTY) == 0) {
    }

    // The transmitter regiser is clear and can be written to.
    WriteReg8(uartBase + COM_DAT, Output);
}
//
///////////////////////////////////////////////////////////////// End of File.
