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
using System.Runtime.InteropServices;

namespace Microsoft.Singularity.V1.Services
{
    public struct PciPortHandle
    {
        public readonly UIntPtr id;

        public static unsafe bool Read8(PciPortHandle handle,
                                        int           offset,
                                        out byte      value)
        {
            unsafe {
                fixed (byte *valuePtr = &value) {
                    return Read8Impl(handle, offset, valuePtr);
                }
            }
        }

        public static unsafe bool Read16(PciPortHandle handle,
                                         int           offset,
                                         out ushort    value)
        {
            unsafe {
                fixed (ushort *valuePtr = &value) {
                    return Read16Impl(handle, offset, valuePtr);
                }
            }
        }

        public static unsafe bool Read32(PciPortHandle handle,
                                         int           offset,
                                         out uint      value)
        {
            unsafe {
                fixed (uint *valuePtr = &value) {
                    return Read32Impl(handle, offset, valuePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool Read8Impl(PciPortHandle h,
                                                   int           offset,
                                                   byte*         value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool Read16Impl(PciPortHandle h,
                                                    int           offset,
                                                    ushort*       value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool Read32Impl(PciPortHandle h,
                                                    int           offset,
                                                    uint*         value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Write8(PciPortHandle h,
                                            int           offset,
                                            byte          value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Write16(PciPortHandle h,
                                          int           offset,
                                          ushort        value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Write32(PciPortHandle h,
                                          int           offset,
                                          uint          value);
    }
}
