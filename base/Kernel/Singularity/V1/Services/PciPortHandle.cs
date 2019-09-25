///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PciPortHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Memory;
using System.Threading;

namespace Microsoft.Singularity.V1.Services
{
    [CLSCompliant(false)]
    public struct PciPortHandle
    {
        // Internal methods
        UIntPtr id;

        internal PciPortHandle(UIntPtr id)
        {
            this.id = id;
        }

        ///////////////////////////////////////////////////////////////////////
        //
        // ABI Exposed
        //

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(PciPortHandle* handle)
        {
            return Create(out *handle);
        }

        public static bool Create(out PciPortHandle handle)
        {
            IoConfig config = Thread.CurrentProcess.IoConfig;
            PciConfig pciConfig = config as PciConfig;

            if (pciConfig != null) {
                handle = new PciPortHandle(
                    Thread.CurrentProcess.AllocateHandle(pciConfig.PciPort)
                    );
                return true;
            }
            else {
                handle = new PciPortHandle();
                return false;
            }
        }

        [ExternalEntryPoint]
        public static bool Dispose(PciPortHandle handle)
        {
            if (handle.id != UIntPtr.Zero) {
                Thread.CurrentProcess.ReleaseHandle(handle.id);
            }
            return false;
        }

        [ExternalEntryPoint]
        public static unsafe
        bool Read8Impl(PciPortHandle handle, int offset, byte* value)
        {
            if (handle.id != UIntPtr.Zero) {
                PciPort p = HandleTable.GetHandle(handle.id) as PciPort;
                *value = p.Read8(offset);
                return true;
            }
            else {
                *value = 0;
                return false;
            }
        }

        [ExternalEntryPoint]
        public static unsafe
        bool Read16Impl(PciPortHandle handle, int offset, ushort* value)
        {
            if (handle.id != UIntPtr.Zero) {
                PciPort p = HandleTable.GetHandle(handle.id) as PciPort;
                *value = p.Read16(offset);
                return true;
            }
            else {
                *value = 0;
                return false;
            }
        }

        [ExternalEntryPoint]
        public static unsafe
        bool Read32Impl(PciPortHandle handle, int offset, uint* value)
        {
            if (handle.id != UIntPtr.Zero) {
                PciPort p = HandleTable.GetHandle(handle.id) as PciPort;
                *value = p.Read32(offset);
                return true;
            }
            else {
                *value = 0;
                return false;
            }
        }

        [ExternalEntryPoint]
        public static
        bool Write8(PciPortHandle handle, int offset, byte value)
        {
            if (handle.id != UIntPtr.Zero) {
                PciPort p = HandleTable.GetHandle(handle.id) as PciPort;
                p.Write8(offset, value);
                return true;
            }
            else {
                return false;
            }
        }

        [ExternalEntryPoint]
        public static
        bool Write16(PciPortHandle handle, int offset, ushort value)
        {
            if (handle.id != UIntPtr.Zero) {
                PciPort p = HandleTable.GetHandle(handle.id) as PciPort;
                p.Write16(offset, value);
                return true;
            }
            else {
                return false;
            }
        }

        [ExternalEntryPoint]
        public static
        bool Write32(PciPortHandle handle, int offset, uint value)
        {
            if (handle.id != UIntPtr.Zero) {
                PciPort p = HandleTable.GetHandle(handle.id) as PciPort;
                p.Write32(offset, value);
                return true;
            }
            else {
                return false;
            }
        }
    }
}
