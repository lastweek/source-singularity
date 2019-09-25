///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Timer8254.cs
//
//  Useful reference URLs:
//    http://developer.intel.com/design/archives/periphrl/index.htm
//    http://developer.intel.com/design/archives/periphrl/docs/7203.htm
//    http://developer.intel.com/design/archives/periphrl/docs/23124406.htm
//

using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;

using System;
using System.Threading;
using System.Diagnostics;

namespace Microsoft.Singularity.Hal
{
    [DriverCategory]
    [Signature("/pnp/PNP0100")]
    public sealed class Timer8254Resources : DriverCategoryDeclaration
    {
        [IoPortRange(0, Default = 0x0040, Length = 0x04)]
        public IoPortRange port1;

        [IoIrqRange(1, Default = 0x00, Length = 0x01)]
        public IoIrqRange irq1;

        [IoFixedPortRange(Base = 0x0061, Length = 0x01)]
        public IoPortRange port2;
    }

    //
    // Note on the i8254 timer:
    //
    // The clock is driven by a 14.318 MHz clock through a divide-by-12
    // counter.
    // This gives a clock frequency of 1.193 MHz.
    // Each tick is therefore 0.838 microseconds long.
    // Thus a 16 bit timer gives us a maximum delay of 0.05 seconds.
    // 
    [CLSCompliant(false)]
    public sealed class Timer8254Apic
    {
        // Registers   
        const byte  i8254_C2     = 0x02;    // counter 2       
        const byte  i8254_CW     = 0x03;    // control word      

        //
        //The control word to the 8254 is composed of four fields:
        //bits 6-7: select the counter
        //bits 4-5: select read/write
        //bits 1-3: mode to use
        //bit  0  : BCD mode
        //

        // bits 6-7 select the counter   
        const byte i8254_CW_SEL0      = 0x00;  // select counter 0         
        const byte i8254_CW_SEL1      = 0x40;  // select counter 1         
        const byte i8254_CW_SEL2      = 0x80;  // select counter 2         
        const byte i8254_CW_RBC       = 0xc0;  // read-back command        

        // bits 4-5 select transaction type   
        const byte i8254_CW_CLC       = 0x00;  // counter latch comm.      
        const byte i8254_CW_LSB       = 0x10;  // r/w lsb only             
        const byte i8254_CW_MSB       = 0x20;  // r/w msb only             
        const byte i8254_CW_BOTH      = 0x30;  // r/w lsb, then msb        

        // bits 1-3 select the mode. bit 3 is sometimes a don't care   
        const byte i8254_CW_MODE0     = 0x00;  // int. on term. count      
        const byte i8254_CW_MODE1     = 0x02;  // h/w retrig. one-shot     
        const byte i8254_CW_MODE2     = 0x04;  // rate generator           
        const byte i8254_CW_MODE3     = 0x06;  // square wave mode         
        const byte i8254_CW_MODE4     = 0x08;  // s/w trig. strobe         
        const byte i8254_CW_MODE5     = 0x0a;  // h/w trig. strobe         

        // bit 0 sets BCD mode, if you really must   
        const byte i8254_CW_BCD       = 0x01;  // set BCD operation        

        // read-back commands use bits 4 and 5 to return status these
        // are the wrong way round since the bits are inverted (RTFDS).
        // 
        const byte i8254_RB_NOSTATUS  = 0xd0;  // Don't get latched count   
        const byte i8254_RB_NOCOUNT   = 0xe0;  // Don't get status         
        const byte i8254_RB_ALL       = 0xc0;  // Get status and count     

        // read-back commands use bits 3-1 to select counter   
        const byte i8254_RB_SEL2      = 0x08;  // counter 2                

        // status from read-back is returned in bits 6-7   
        const byte i8254_RB_OUT       = 0x80;  // out pin value            
        const byte i8254_RB_NULL      = 0x40;  // 1 = count null           

        private static readonly int DefaultTicksPerSecond = 1193182;
        private static readonly int SystemTicksPerSecond  = 10000000;

        private PnpConfig config;
        private byte      irq;
        private int       frequency = DefaultTicksPerSecond;

        // IOPorts   
        private IoPort  C2Port;
        private IoPort  CWPort;

        // Constructor
        internal Timer8254Apic(PnpConfig config)
        {
            // /pnp/08/02/01/PNP0100 0003 cfg dis : ISA 8254 Timer : AT Timer
            // IRQ mask=0001 type=47
            // I/O Port inf=01 min=0040 max=0040 aln=01 len=04 0040..0043
            this.config = config;
            this.irq    = ((IoIrqRange)config.DynamicRanges[1]).Irq;

            IoPortRange ioPorts = (IoPortRange) config.DynamicRanges[0];

            C2Port = ioPorts.PortAtOffset(i8254_C2, 1, Access.ReadWrite);
            CWPort = ioPorts.PortAtOffset(i8254_CW, 1, Access.ReadWrite);

            // Use Timer2 as it's not connected as interrupt source.
            //
            // Lower 2 bits of port 61 are described in:
            // The Indispensable PC Hardware Book (3rd Edition) p.724
            ioPorts = (IoPortRange) config.FixedRanges[0];
            IoPort p = ioPorts.PortAtOffset(0, 1, Access.ReadWrite);

            //
            // Also clear the NMI RAM parity error to enable the PCI card
            // to generate NMI if the button is depressed
            //

            p.Write8((byte) ((p.Read8() & 0xf8) | 0x01));
        }

        internal void Start(ushort pitTicks)
        {
            CWPort.Write8(i8254_CW_MODE2 | i8254_CW_BOTH | i8254_CW_SEL2);
            C2Port.Write8((byte)(pitTicks & 0xff));
            C2Port.Write8((byte)(pitTicks >> 8));
            do {
                CWPort.Write8(i8254_RB_NOCOUNT | i8254_RB_SEL2);
            } while ((C2Port.Read8() & i8254_RB_NULL) == i8254_RB_NULL);
        }

        internal ushort Read()
        {
            CWPort.Write8(i8254_RB_NOSTATUS | i8254_RB_SEL2);
            return (ushort)(C2Port.Read8() | (C2Port.Read8() << 8));
        }

        internal void Stop()
        {
            CWPort.Write8(i8254_CW_MODE2 | i8254_CW_BOTH | i8254_CW_SEL2);
            C2Port.Write8((byte)(0));    // LSB   
            // C2Port.Write8((byte)(0));  MSB DON'T!   
        }

        internal void SetFrequency(uint newFrequency)
        {
            frequency = (int)newFrequency;
            DebugStub.Print("i8254 frequency {0} Hz\n", __arglist(frequency));
        }

        internal uint TimeSpanToTimerTicks(uint ts)
        {
            return (uint) ((ulong)ts * (uint)(frequency / SystemTicksPerSecond));
        }

        internal uint TimerToTimeSpanTicks(uint ts)
        {
            return (uint) ((ulong)ts * (uint)(SystemTicksPerSecond / frequency));
        }

#if FIXED_FREQUENCY
        internal static int TimeSpanTicksToPitTicks(int ts)
        {
            // t = 1193182 * T / (10^7) = 0.1193182 * T
            //   = T * (1/0x10 + 0xe8ba/0x100000)
            int tmp = (ts * 0xe8ba) >> 20;
            return tmp + (ts >> 4);
        }

        internal static int PitTicksToTimeSpanTicks(int delta)
        {
            // T = 10^7 * t / 1193182 = 8.3809511 * t
            //   = t * (8 + 0x6186/0x10000)
            return (delta << 3) + ((delta * 0x6186) >> 16);
        }
#endif
    }
}
