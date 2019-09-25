///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  UART transport support for debugging
//

//
// Status Constants for reading data from comport
//

#define CP_GET_SUCCESS  0
#define CP_GET_NODATA   1
#define CP_GET_ERROR    2


#define OMAP_UART1_BASE 0x4806A000
#define OMAP_UART2_BASE 0x4806C000

///////////////////////////////////////////////////////////////// Serial Port.
//
#define OMAP_CLOCK_RATE 2995200

#define OMAP_CONTROL_PADCONF_UART1_TX   (0x17c)
#define OMAP_CONTROL_PADCONF_UART1_CTS  (0x180)
#define OMAP_CONTROL_PADCONF_UART2_TX   (0x178)
#define OMAP_CONTROL_PADCONF_UART2_CTS  (0x174)

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
// Communication functions.
//

static uint32 *uartBase = 0;

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

bool BdPortInit(uint32 * BaseAddress, uint32 BaudRate)
{
#define PADCONF_CTS    ((1 << 4) | (1 << 3) | (1 << 8))
#define PADCONF_RTS    (0)
#define PADCONF_TX     (0)
#define PADCONF_RX     ((1 << 3) | (1 << 8))

    uartBase = BaseAddress;
    uint8 * HalpSCM = (uint8 *)OMAP_SCM_BASE;
    uint8 * HalpCORE_CM = (uint8 *)OMAP_CORE_CM_BASE;
    uint32 Value;

    if (BaseAddress == (uint32 *)OMAP_UART1_BASE) {
        // Power on the required function and interface units.
        Value = ReadReg32(HalpCORE_CM + CM_FCLKEN1_CORE);
        Value |= CM_CORE_EN_UART1;
        WriteReg32(HalpCORE_CM + CM_FCLKEN1_CORE, Value);

        Value = ReadReg32(HalpCORE_CM + CM_ICLKEN1_CORE);
        Value |= CM_CORE_EN_UART1;
        WriteReg32(HalpCORE_CM + CM_ICLKEN1_CORE, Value);

        // Configure uart1 pads per documentation example
        WriteReg32(HalpSCM + OMAP_CONTROL_PADCONF_UART1_TX,
                   PADCONF_TX | (PADCONF_RTS << 16));
        WriteReg32(HalpSCM + OMAP_CONTROL_PADCONF_UART1_CTS,
                   PADCONF_CTS | (PADCONF_RX << 16));
    }
    else if (BaseAddress == (uint32 *)OMAP_UART2_BASE) {
        // Power on the required function and interface units.
        Value = ReadReg32(HalpCORE_CM + CM_FCLKEN1_CORE);
        Value |= CM_CORE_EN_UART2;
        WriteReg32(HalpCORE_CM + CM_FCLKEN1_CORE, Value);

        Value = ReadReg32(HalpCORE_CM + CM_ICLKEN1_CORE);
        Value |= CM_CORE_EN_UART2;
        WriteReg32(HalpCORE_CM + CM_ICLKEN1_CORE, Value);

        WriteReg32(HalpSCM + OMAP_CONTROL_PADCONF_UART2_CTS,
                   PADCONF_CTS | (PADCONF_RTS << 16));
        WriteReg32(HalpSCM + OMAP_CONTROL_PADCONF_UART2_TX,
                   PADCONF_TX | (PADCONF_RX << 16));
    }

    // Set the default baudrate.
    UartSetBaudRate(BaseAddress, BaudRate);

    // Set DLAB to zero.  DLAB controls the meaning of the first two
    // registers.  When zero, the first register is used for all byte transfer
    // and the second register controls device interrupts.
    //
    WriteReg8(BaseAddress + COM_LCR,
              ReadReg8(BaseAddress + COM_LCR) & ~LCR_DLAB);

    // Disable device interrupts.  This implementation will handle state
    // transitions by request only.
    //
    WriteReg8(BaseAddress + COM_IEN, 0);

    // Reset and disable the FIFO queue.
    // N.B. FIFO will be reenabled before returning from this routine.
    //
    WriteReg8(BaseAddress + COM_FCR, FCR_CLEAR_TRANSMIT | FCR_CLEAR_RECEIVE);

    // Configure the Modem Control Register.  Disabled device interrupts,
    // turn off loopback.
    //
    WriteReg8(BaseAddress + COM_MCR,
              ReadReg8(BaseAddress + COM_MCR) & MCR_INITIALIZE);

    // Initialize the Modem Control Register.  Indicate to the device that
    // we are able to send and receive data.
    //
    WriteReg8(BaseAddress + COM_MCR, MCR_INITIALIZE);

    // Enable the FIFO queues.
    WriteReg8(BaseAddress + COM_FCR, FCR_ENABLE);

    return true;
}

UINT32 BdPortGetByte(PUINT8 Input)
//++
//
//Routine Description:
//
//  Fetch a byte from the debug port and return it.
//
//Arguments:
//
//  Input - Returns the data byte.
//
//Return Value:
//
//  CP_GET_SUCCESS is returned if a byte is successfully read from the
//      kernel debugger line.
//  CP_GET_NODATA is returned if timeout.
//
//--  
{
    //
    // Define wait timeout value.
    //
    #define TIMEOUT_COUNT 1024 * 30 // * 200   
    //#define TIMEOUT_COUNT 15

    UINT8 lsr;
    UINT8 value;
    UINT32 limitcount = TIMEOUT_COUNT;

    UINT8 msr;
    msr = ReadReg8(uartBase + COM_MSR);

    while (limitcount != 0) {
        limitcount--;

        lsr = ReadReg8(uartBase + COM_LSR);
        if (lsr & LSR_DATA_AVAILABLE) {
            value = ReadReg8(uartBase + COM_DAT);
            *Input = (UINT8)(value & 0xff);
            return CP_GET_SUCCESS;
        }
    }
    return CP_GET_NODATA;
}

void BdPortPutByte(UINT8 Output)
{
    // Loop until the device is ready for output
    while ((ReadReg8(uartBase + COM_LSR) & LSR_THR_EMPTY) == 0) {
    }

    // The transmitter regiser is clear and can be written to.
    WriteReg8(uartBase + COM_DAT, Output);
}

// End of File.
