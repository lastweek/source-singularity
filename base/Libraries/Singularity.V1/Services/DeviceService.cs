////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DeviceService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;

namespace Microsoft.Singularity.V1.Services
{
    public struct DeviceService
    {
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe uint GetPnpSignature(int index, /*[out]*/ char * output,
                                                         uint maxout);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool GetPciPort(out PciPortHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetIrqCount(byte irq);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint GetDynamicIoRangeCount();

        [NoHeapAllocation]
        public static bool GetDynamicIoPortRange(uint range,
                                                 out ushort port,
                                                 out ushort size,
                                                 out bool readable,
                                                 out bool writable)
        {
            unsafe {
                fixed (ushort * portPrt = &port, sizePtr = &size) {
                    fixed (bool * readablePtr = &readable,
                                  writablePtr = &writable) {
                        return GetDynamicIoPortRangeImpl(range, portPrt,
                            sizePtr, readablePtr, writablePtr);
                    }
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1186)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetDynamicIoPortRangeImpl(
            uint range,
            ushort * port,
            ushort * size,
            bool * readable,
            bool * writable);

        [NoHeapAllocation]
        public static unsafe bool GetDynamicIoMemoryRange(uint range,
                                                          out byte * data,
                                                          out uint size,
                                                          out bool readable,
                                                          out bool writable)
        {
            fixed (byte * * dataPtr = &data) {
                fixed (uint * sizePtr = &size) {
                    fixed (bool * readablePtr = &readable,
                                  writablePtr = &writable) {
                        return GetDynamicIoMemoryRangeImpl(range, dataPtr,
                            sizePtr, readablePtr, writablePtr);
                    }
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1186)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetDynamicIoMemoryRangeImpl(
            uint range,
            byte * * data,
            uint * size,
            bool * readable,
            bool * writable);

        [NoHeapAllocation]
        public static bool GetDynamicIoIrqRange(uint range,
                                                out byte line,
                                                out byte size)
        {
            unsafe {
                fixed (byte * linePtr = &line, sizePtr = &size) {
                    return GetDynamicIoIrqRangeImpl(range, linePtr, sizePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetDynamicIoIrqRangeImpl(
            uint range,
            byte * line,
            byte * size);

        [NoHeapAllocation]
        public static bool GetDynamicIoDmaRange(uint range,
                                                out byte channel,
                                                out byte size)
        {
            unsafe {
                fixed (byte * channelPtr = &channel, sizePtr = &size) {
                    return GetDynamicIoDmaRangeImpl(range, channelPtr, sizePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetDynamicIoDmaRangeImpl(
            uint range,
            byte * channel,
            byte * size);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern uint GetFixedIoRangeCount();

        public static bool GetFixedIoPortRange(uint range,
                                               out ushort port,
                                               out ushort size,
                                               out bool readable,
                                               out bool writable)
        {
            unsafe {
                fixed (ushort * portPrt = &port, sizePtr = &size) {
                    fixed (bool * readablePtr = &readable,
                                  writablePtr = &writable) {
                        return GetFixedIoPortRangeImpl(range, portPrt, sizePtr,
                            readablePtr, writablePtr);
                    }
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1186)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetFixedIoPortRangeImpl(
            uint range,
            ushort * port,
            ushort * size,
            bool * readable,
            bool * writable);

        [NoHeapAllocation]
        public static unsafe bool GetFixedIoMemoryRange(uint range,
                                                        out byte * data,
                                                        out uint size,
                                                        out bool readable,
                                                        out bool writable)
        {
            fixed (byte * * dataPtr = &data) {
                fixed (uint * sizePtr = &size) {
                    fixed (bool * readablePtr = &readable,
                                  writablePtr = &writable) {
                        return GetFixedIoMemoryRangeImpl(range, dataPtr,
                            sizePtr, readablePtr, writablePtr);
                    }
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1186)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetFixedIoMemoryRangeImpl(
            uint range,
            byte * * data,
            uint * size,
            bool * readable,
            bool * writable);

        [NoHeapAllocation]
        public static bool GetFixedIoIrqRange(uint range,
                                              out byte line,
                                              out byte size)
        {
            unsafe {
                fixed (byte * linePtr = &line, sizePtr = &size) {
                    return GetFixedIoIrqRangeImpl(range, linePtr, sizePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetFixedIoIrqRangeImpl(
            uint range,
            byte * line,
            byte * size);

        [NoHeapAllocation]
        public static bool GetFixedIoDmaRange(uint range,
                                              out byte channel,
                                              out byte size)
        {
            unsafe {
                fixed (byte * channelPtr = &channel, sizePtr = &size) {
                    return GetFixedIoDmaRangeImpl(range, channelPtr, sizePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetFixedIoDmaRangeImpl(
            uint range,
            byte * channel,
            byte * size);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern UIntPtr MapPhysicalRange(UIntPtr physStart,
                                                      UIntPtr numBytes,
                                                      bool readable,
                                                      bool writable);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void UnmapPhysicalRange(UIntPtr startAddr,
                                                     UIntPtr limitAddr);

        [NoHeapAllocation]
        public static bool GetDmaPhysicalAddress(UIntPtr virtualAddr,
                                                 out UIntPtr physicalAddr,
                                                 out UIntPtr physicalRemaining)
        {
            unsafe {
                fixed (UIntPtr * physicalAddrPtr = &physicalAddr,
                       physicalRemainingPtr = &physicalRemaining) {
                    return GetDmaPhysicalAddressImpl(virtualAddr,
                                                     physicalAddrPtr,
                                                     physicalRemainingPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetDmaPhysicalAddressImpl(
            UIntPtr virtualAddr,
            UIntPtr * physicalAddr,
            UIntPtr * physicalRemaining);
    }
}
