///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PmTimer.cs
//
//  Note:
//    Power management timer

namespace Microsoft.Singularity.Hal.Acpi
{
    using System;
    using System.Runtime.CompilerServices;
    using Microsoft.Singularity.Io;

    [ CLSCompliant(false) ]
    public sealed class PMTimer
    {
        public const uint FrequencyHz = 3579545;

        IoPort   io;
        IoMemory mem;
        int      width;

        private PMTimer(uint offset, int width)
        {
            if (offset < 0xffffu) {
                this.io = new IoPort((ushort) offset, 4, Access.Read);
            }
            else {
                this.mem = IoMemory.MapPhysicalMemory(new UIntPtr(offset),
                                                      4, true, false);
            }
            this.width = width;
        }

        /// <summary> Get the width of the timer in bits (24 or 32). </summary>
        public int Width { get { return width; } }

        /// <summary> Get the current timer value. </summary>
        public uint Value
        {
            [NoHeapAllocation]
            get {
                uint value;
                if (io != null) {
                    IoResult result = io.Read32NoThrow(0, out value);
                    DebugStub.Assert(IoResult.Success == result);
                }
                else {
                    IoResult result = mem.Read32NoThrow(0, out value);
                    DebugStub.Assert(IoResult.Success == result);
                }
                return value;
            }
        }

        public static PMTimer Create(Fadt fadt)
        {
            if ((fadt.Flags & (uint) FadtFlags.TMR_VAL_EXT) == 0) {
                return new PMTimer(fadt.PM_TMR_BLK, 24);
            }
            return new PMTimer(fadt.PM_TMR_BLK, 32);
        }
    }
}
