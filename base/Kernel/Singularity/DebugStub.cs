////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Debug.cs
//
//  Note:
//

using System;
using System.Collections;
using System.Diagnostics;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;

using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Loader;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity
{
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in halkd.cpp")]
    public class DebugStub
    {
        public static ulong perfCounter0;
        public static ulong perfCounter1;
        public static ulong perfCounter2;
        public static ulong perfCounter3;
        public static ulong perfCounter4;
        public static ulong perfCounter5;
        public static ulong perfCounter6;
        public static ulong perfCounter7;
        public static ulong perfCounter8;
        public static ulong perfCounter9;
        public static ulong perfCounter10;
        public static ulong perfCounter11;
        public static ulong perfCounter12;
        public static ulong perfCounter13;
        public static ulong perfCounter14;
        public static ulong perfCounter15;

        /////////////////////////////////////////////////////// Print Methods.
        //
        [NoHeapAllocation]
        public static void Print(byte value)
        {
            Print("{0:x2}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(ushort value)
        {
            Print("{0:x4}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(uint value)
        {
            Print("{0:x8}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(ulong value)
        {
            Print("{0:x}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(UIntPtr value)
        {
            Print("{0:x8}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(sbyte value)
        {
            Print("{0}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(short value)
        {
            Print("{0}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(int value)
        {
            Print("{0}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(long value)
        {
            Print("{0}", __arglist(value));
        }

        [NoHeapAllocation]
        public static void Print(String value)
        {
            if (value != null) {
                Print(value, new ArgIterator());
            }
        }

        [NoHeapAllocation]
        public static void Print(String format, __arglist)
        {
            Print(format, new ArgIterator(__arglist));
        }

        [NoHeapAllocation]
        public static unsafe void Print(String format, ArgIterator args)
        {
            char *buffer;
            int length;
            int used = 0;

            PrintBegin(out buffer, out length);
            try {
                if (buffer != null) {
                    used = String.LimitedFormatTo(format, args, buffer, length);
                }
            }
            finally {
                PrintComplete(buffer, used);
            }
        }

        [NoHeapAllocation]
        public static void Write(String value)
        {
            if (value != null) {
                Write(value, new ArgIterator());
            }
        }

        [NoHeapAllocation]
        public static void Write(String format, __arglist)
        {
            Print(format, new ArgIterator(__arglist));
        }

        [NoHeapAllocation]
        public static unsafe void Write(String format, ArgIterator args)
        {
            char *buffer;
            int length;
            int used = 0;

            PrintBegin(out buffer, out length);
            try {
                if (buffer != null) {
                    used = String.LimitedFormatTo(format, args, buffer, length);
                }
            }
            finally {
                PrintComplete(buffer, used);
            }
        }

        [NoHeapAllocation]
        public static void WriteLine()
        {
            WriteLine("", new ArgIterator());
        }

        [NoHeapAllocation]
        public static void WriteLine(String value)
        {
            if (value != null) {
                WriteLine(value, new ArgIterator());
            }
        }

        [NoHeapAllocation]
        public static void WriteLine(String format, __arglist)
        {
            WriteLine(format, new ArgIterator(__arglist));
        }

        [NoHeapAllocation]
        public static unsafe void WriteLine(String format, ArgIterator args)
        {
            char *buffer;
            int length;
            int used = 0;

            PrintBegin(out buffer, out length);
            try {
                if (buffer != null) {
                    used = String.LimitedFormatTo(format, args, buffer, length);
                    if (used < length) {
                        buffer[used++] = '\n';
                    }
                }
            }
            finally {
                PrintComplete(buffer, used);
            }
        }

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1200)]
        [NoHeapAllocation]
        public static extern unsafe void PrintBegin(out char * buffer, out int length);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1200)]
        [NoHeapAllocation]
        public static extern unsafe void PrintComplete(char * buffer, int used);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1200)]
        [NoHeapAllocation]
        public static extern unsafe void Print(char *buffer);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1200)]
        [NoHeapAllocation]
        public static extern unsafe void Print(char *buffer, int length);

        ////////////////////////////////////////////////////// Assert Methods.
        //
        [NoHeapAllocation]
        public static void NotImplemented()
        {
            failAssert("Not implemented.");
        }

        [NoHeapAllocation]
        public static void NotImplemented(String msg)
        {
            failAssert("Not implemented: {0}", __arglist(msg));
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        public static void NotReached()
        {
            failAssert("Unreachable code reached.");
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        public static void NotReached(String msg)
        {
            failAssert("Unreachable code reached: ", __arglist(msg));
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        [ManualRefCounts]
        public static void Assert(bool expr)
        {
            if (!expr) {
                failAssert(null);
            }
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        [ManualRefCounts]
        public static void Deny(bool expr)
        {
            if (expr) {
                failAssert(null);
            }
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        [ManualRefCounts]
        public static void Assert(bool expr, String s)
        {
            if (!expr) {
                failAssert(s);
            }
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        public static void Deny(bool expr, String s)
        {
            if (expr) {
                failAssert(s);
            }
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        [ManualRefCounts]
        public static void Assert(bool expr, String format, __arglist)
        {
            if (!expr) {
                failAssert(format, new ArgIterator(__arglist));
            }
        }

        [Conditional("DEBUG")]
        [NoInline]
        [NoHeapAllocation]
        public static void Deny(bool expr, String format, __arglist)
        {
            if (expr) {
                failAssert(format, new ArgIterator(__arglist));
            }
        }

        // Rationale for cutting the fact that no stack probes are permitted in this
        // tree of calls:
        //
        // * Asserts are debug only.
        // * When an assert fails, a future stack overflow is not our biggest problem.
        // * We want the ability to freely assert in trees that forbid stack probes.
        [NoStackLinkCheckTransCut]
        [ManualRefCounts]
        [NoHeapAllocation]
        private static void failAssert(String s)
        {
            if (s != null) {
                WriteLine("DS1.Assertion failed: {0}", __arglist(s));
            }
            else {
                WriteLine("DS1.Assertion failed.");
            }
            Break();
        }

        // Rationale for cutting the fact that no stack probes are permitted in this
        // tree of calls:
        //
        // * Asserts are debug only.
        // * When an assert fails, a future stack overflow is not our biggest problem.
        // * We want the ability to freely assert in trees that forbid stack probes.
        [NoStackLinkCheckTransCut]
        [ManualRefCounts]
        [NoHeapAllocation]
        private static void failAssert(String format, __arglist)
        {
            failAssert(format, new ArgIterator(__arglist));
        }

        // Rationale for cutting the fact that no stack probes are permitted in this
        // tree of calls:
        //
        // * Asserts are debug only.
        // * When an assert fails, a future stack overflow is not our biggest problem.
        // * We want the ability to freely assert in trees that forbid stack probes.
        [NoStackLinkCheckTransCut]
        [ManualRefCounts]
        [NoHeapAllocation]
        private static void failAssert(String format, ArgIterator args)
        {
            if (format != null) {
                Write("DS2.Assertion failed: ");
                WriteLine(format, args);
            }
            else {
                WriteLine("DS2.Assertion failed.");
            }
            Break();
        }

        /////////////////////////////////////////////////////// State Methods.
        //
        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(638)]
        [NoHeapAllocation]
        public static extern void Break();

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        internal static extern bool Trap(ref SpillContext context, int it);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        internal static extern bool TrapForProcessorSwitch(ref SpillContext context);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        internal static extern void AddProcessor(int cpuId);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        internal static extern void RevertToUniprocessor();

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static extern bool PollForBreak();

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static extern bool LoadedBinary(UIntPtr baseAddress,
                                               UIntPtr bytes,
                                               UIntPtr name,
                                               uint checksum,
                                               uint timestamp,
                                               bool silent);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static extern bool LoadedBinary(UIntPtr baseAddress,
                                               UIntPtr bytes,
                                               String name,
                                               uint checksum,
                                               uint timestamp,
                                               bool silent);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static extern bool UnloadedBinary(UIntPtr baseAddress,
                                                 bool silent);

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(1024)]
        [NoHeapAllocation]
        public static extern bool IsDebuggerPresent();

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [NoHeapAllocation]
        public static ulong ReadPerfCounter(uint which)
        {
            switch (which) {
                case 0: return perfCounter0;
                case 1: return perfCounter1;
                case 2: return perfCounter2;
                case 3: return perfCounter3;
                case 4: return perfCounter4;
                case 5: return perfCounter5;
                case 6: return perfCounter6;
                case 7: return perfCounter7;
                case 8: return perfCounter8;
                case 9: return perfCounter9;
                case 10: return perfCounter10;
                case 11: return perfCounter11;
                case 12: return perfCounter12;
                case 13: return perfCounter13;
                case 14: return perfCounter14;
                case 15: return perfCounter15;
                default: return 0;
            }
        }

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [NoHeapAllocation]
        public static bool WritePerfCounter(uint which, ulong value)
        {
            switch (which) {
                case 0: perfCounter0 = value; return true;
                case 1: perfCounter1 = value; return true;
                case 2: perfCounter2 = value; return true;
                case 3: perfCounter3 = value; return true;
                case 4: perfCounter4 = value; return true;
                case 5: perfCounter5 = value; return true;
                case 6: perfCounter6 = value; return true;
                case 7: perfCounter7 = value; return true;
                case 8: perfCounter8 = value; return true;
                case 9: perfCounter9 = value; return true;
                case 10: perfCounter10 = value; return true;
                case 11: perfCounter11 = value; return true;
                case 12: perfCounter12 = value; return true;
                case 13: perfCounter13 = value; return true;
                case 14: perfCounter14 = value; return true;
                case 15: perfCounter15 = value; return true;
                default: return false;
            }
        }

        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [NoHeapAllocation]
        public static bool AddToPerfCounter(uint which, ulong value)
        {
            switch (which) {
                case 0: Interlocked.Add(ref perfCounter0, value); return true;
                case 1: Interlocked.Add(ref perfCounter1, value); return true;
                case 2: Interlocked.Add(ref perfCounter2, value); return true;
                case 3: Interlocked.Add(ref perfCounter3, value); return true;
                case 4: Interlocked.Add(ref perfCounter4, value); return true;
                case 5: Interlocked.Add(ref perfCounter5, value); return true;
                case 6: Interlocked.Add(ref perfCounter6, value); return true;
                case 7: Interlocked.Add(ref perfCounter7, value); return true;
                case 8: Interlocked.Add(ref perfCounter8, value); return true;
                case 9: Interlocked.Add(ref perfCounter9, value); return true;
                case 10: Interlocked.Add(ref perfCounter10, value); return true;
                case 11: Interlocked.Add(ref perfCounter11, value); return true;
                case 12: Interlocked.Add(ref perfCounter12, value); return true;
                case 13: Interlocked.Add(ref perfCounter13, value); return true;
                case 14: Interlocked.Add(ref perfCounter14, value); return true;
                case 15: Interlocked.Add(ref perfCounter15, value); return true;
                default: return false;
            }
        }

    }
}
