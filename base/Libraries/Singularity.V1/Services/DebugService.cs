////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DebugService.cs
//
//  Note:
//

using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.V1.Services
{
    [AccessedByRuntime("referenced from hal.cpp")]
    public struct DebugService
    {
        //private readonly int id;

        [NoHeapAllocation]
        public static unsafe void PrintBegin(out char * buffer, out int length)
        {
            fixed (char * * bufferPtr = &buffer) {
                fixed (int * lengthPtr = &length) {
                    PrintBeginImpl(bufferPtr, lengthPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1170)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe void PrintBeginImpl(
            char * * buffer,
            int * length);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(768)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe void PrintComplete(char * buffer, int used);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(768)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe void Print(char * buffer);

        [AccessedByRuntime("Required by hal.cpp")]
        [OutsideGCDomain]
        [StackBound(768)]
        [NoHeapAllocation]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe void Print(char * buffer, int length);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(832)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Print(bool value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(832)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Print(char value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(832)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Print(byte value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(832)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Print(int value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(832)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Print(uint value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(832)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Print(long value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(832)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Print(ulong value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(768)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Break();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1088)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void WalkStack();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool IsDebuggerPresent();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ulong ReadPerfCounter(uint which);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool WritePerfCounter(uint which, ulong value);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool AddToPerfCounter(uint which, ulong value);
    }
}
