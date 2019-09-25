///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;

using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity.Io
{
    [CLSCompliant(false)]
    public sealed class PciPort
    {
        private PciPortHandle handle;

        internal PciPort(PciPortHandle pciPortHandle)
        {
            this.handle = pciPortHandle;
        }

        ~PciPort()
        {
        }

        public void Write8(int offset, byte value)
        {
            if (!PciPortHandle.Write8(handle, offset, value)) {
                DebugStub.Break();
            }
        }

        public void Write16(int offset, ushort value)
        {
            if (!PciPortHandle.Write16(handle, offset, value)) {
                DebugStub.Break();
            }
        }

        public void Write32(int offset, uint value)
        {
            if (!PciPortHandle.Write32(handle, offset, value)) {
                DebugStub.Break();
            }
        }

        public byte Read8(int offset)
        {
            return Read8Impl(offset);
        }

        public ushort Read16(int offset)
        {
            return Read16Impl(offset);
        }

        public uint Read32(int offset)
        {
            return Read32Impl(offset);
        }

        private unsafe byte Read8Impl(int offset)
        {
            byte v;

            if (PciPortHandle.Read8Impl(handle, offset, &v)) {
                return v;
            }
            else {
                DebugStub.Break();
                return 0;
            }
        }

        private unsafe ushort Read16Impl(int offset)
        {
            ushort v;

            if (PciPortHandle.Read16Impl(handle, offset, &v)) {
                return v;
            }
            else {
                DebugStub.Break();
                return 0;
            }
        }

        private unsafe uint Read32Impl(int offset)
        {
            uint v;

            if (PciPortHandle.Read32Impl(handle, offset, &v)) {
                return v;
            }
            else {
                DebugStub.Break();
                return 0;
            }
        }
    }
}
