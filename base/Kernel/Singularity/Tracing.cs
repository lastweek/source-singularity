////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:  Tracing.cs
//
//  Note:  Provides a simple tracing facility to allow for post-facto performance debugging.
//

using System;
using System.Diagnostics;
using System.Text;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Eventing;

namespace Microsoft.Singularity
{
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from Tracing.cpp")]
    public class Tracing
    {

        public const byte Fatal   = 0xe; // system crashed.
        public const byte Error   = 0xc; // system will crash.
        public const byte Warning = 0xa; // cause for immediate concern.
        public const byte Notice  = 0x8; // might be cause for concern.
        public const byte Trace   = 0x6; // may be of use in crash.
        public const byte Audit   = 0x4; // impact on performance.
        public const byte Debug   = 0x2; // used only for debugging.

        public static void InitializeSystem()
        {
        }

        [NoHeapAllocation]
        public static void SetTscOffset(long tscOffset){}

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(64)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static extern void Initialize();

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(64)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static extern UIntPtr GetSystemTracingStorageHandle();

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             UIntPtr arg0);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             UIntPtr arg0, UIntPtr arg1);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             UIntPtr arg0, UIntPtr arg1, UIntPtr arg2);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             UIntPtr arg0, UIntPtr arg1, UIntPtr arg2,
                                             UIntPtr arg3);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             UIntPtr arg0, UIntPtr arg1, UIntPtr arg2,
                                             UIntPtr arg3, UIntPtr arg4);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             UIntPtr arg0, UIntPtr arg1, UIntPtr arg2,
                                             UIntPtr arg3, UIntPtr arg4, UIntPtr arg5);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             string arg0);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             string arg0, UIntPtr arg1);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             string arg0, UIntPtr arg1, UIntPtr arg2);

        [AccessedByRuntime("output to header : defined in Tracing.cpp")]
        [StackBound(256)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        public static unsafe extern void Log(byte severity, string msg,
                                             string arg0, string arg1);

    }

}
