////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   AddressSpace.cs
//
//  Note:
//

using System.Runtime.CompilerServices;
using System;

namespace Microsoft.Singularity.Memory
{
    [NoCCtor]
    [CLSCompliant(false)]

    // This class just wraps the PhysicalAddress of the root PDPE that
    // describes this space.
    public struct AddressSpace
    {
        private PhysicalAddress spaceAddr;

        public AddressSpace(PhysicalAddress addr)
        {
            spaceAddr = addr;
        }

        public unsafe PhysicalAddress PdptPage {
            get {
                return spaceAddr;
            }
        }

        public static AddressSpace Null {
            get {
                return new AddressSpace(PhysicalAddress.Null);
            }
        }

        public static bool operator== (AddressSpace adr1, AddressSpace adr2)
        {
            return adr1.spaceAddr == adr2.spaceAddr;
        }

        public static bool operator!= (AddressSpace adr1, AddressSpace adr2)
        {
            return !(adr1 == adr2);
        }

        public override bool Equals(Object o)
        {
            if (o is AddressSpace) {
                return this == (AddressSpace)o;
            }
            else {
                return false;
            }
        }

        public static AddressSpace CurrentAddressSpace {
            get {
                return Processor.GetCurrentAddressSpace();
            }
        }

        public override int GetHashCode()
        {
            return spaceAddr.GetHashCode();
        }
    }
}
