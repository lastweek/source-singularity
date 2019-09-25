////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PhysicalAddress.cs - Abstraction for a processor's physical address
//
//  Note:
//

using System.Runtime.CompilerServices;
using System;

namespace Microsoft.Singularity.Memory
{
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halkd.cpp")]
    public struct PhysicalAddress
    {
        // This is a processor detail. 52 is for x86-derived
        // architectures with Physical Address Extensions enabled.
        private const uint HARDWARE_ADDR_BITS = 52;

        // "640KB is enough for anybody"
        private ulong addr;

        public PhysicalAddress(ulong pAddr)
        {
            addr = pAddr;
        }

        [AccessedByRuntime("referenced from halkd.cpp")]
        public PhysicalAddress(UIntPtr pAddr)
        {
            addr = (ulong)pAddr;
        }

        public static PhysicalAddress Null {
            get {
                return new PhysicalAddress(0);
            }
        }

        public ulong Value {
            get {
                return addr;
            }
        }

        public static bool operator== (PhysicalAddress adr1, PhysicalAddress adr2)
        {
            return adr1.Value == adr2.Value;
        }

        public static bool operator!= (PhysicalAddress adr1, PhysicalAddress adr2)
        {
            return !(adr1 == adr2);
        }

        public override bool Equals(Object o)
        {
            if (o is PhysicalAddress) {
                return this == (PhysicalAddress)o;
            }
            else {
                return false;
            }
        }

        public override int GetHashCode()
        {
            unchecked{ return (int)addr; }
        }
    }
}
