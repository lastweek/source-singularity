////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
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

using Microsoft.Singularity.V1.Services;

namespace Microsoft.Singularity
{
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in halkd.cpp")]
    public class DebugStub
    {
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

        //////////////////////////////////////////////////////////////////////
        //

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
            WriteLine(format, args);
        }

        //////////////////////////////////////////////////////////////////////
        //

        [NoHeapAllocation]
        public static void Write(String value)
        {
            if (value != null) {
                WriteLine(value, new ArgIterator());
            }
        }

        [NoHeapAllocation]
        public static void Write(String format, __arglist)
        {
            Write(format, new ArgIterator(__arglist));
        }

        [NoHeapAllocation]
        public static unsafe void Write(String format, ArgIterator args)
        {
            WriteLine(format, args);
        }

        //////////////////////////////////////////////////////////////////////
        //
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

            DebugService.PrintBegin(out buffer, out length);
            try {
                if (buffer != null) {
                    AddLineHeader(buffer, ref used, length);
                    int format_used = String.LimitedFormatTo(format, args, buffer+used, length-used);
                    used += format_used;

                    // If the line had \r or \n at the start, replace with spaces.
                    for (int i = 0; i < used; i++) {
                        char c = buffer[i];
                        if (c == '\r' || c == '\n') {
                            buffer[i] = ' ';
                        }
                        else {
                            break;
                        }
                    }

                    // Remove whitespace (including \r\n) from the end.
                    while (used > 0) {
                        char c = buffer[used - 1];
                        if (c == ' ' || c == '\r' || c == '\n' || c == '\t') {
                            used--;
                        }
                        else {
                            break;
                        }
                    }

                    // Add our own \r\n
                    if (used < length) {
                        buffer[used++] = '\n';
                    }
                }
            }
            finally {
                DebugService.PrintComplete(buffer, used);
            }
        }

        /// <summary>
        /// This method adds prefix to each line sent to the debugger, containing the app name,
        /// process id, thread id, and thread name.  The thread name can be changed by setting
        /// the DebugName property of a thread.
        /// </summary>
        [NoHeapAllocation]
        private static unsafe void AddLineHeader(char* buffer, ref int length, int maxLength)
        {
            uint processId = ProcessService.GetCurrentProcessId();
            uint threadId = unchecked((uint)Thread.GetCurrentThreadIndex());

            string appName;
            string threadName;
#if DEBUG
            appName = AppRuntime.AppName;
            if (appName == null)
                appName = "?";

            Thread currentThread = Thread.CurrentThread;
            if (currentThread != null) {
                threadName = currentThread.DebugName;
                if (threadName == null) {
                    threadName = "";
                }
            }
            else {
                threadName = "";
            }
#else
            appName = "?";
            threadName = "";
#endif

            InsertFormat(buffer, ref length, maxLength, "[{0,10} p{1,2} t{2,2} {3,6}] ", __arglist(appName, processId, threadId, threadName));
        }

        [NoHeapAllocation]
        private static unsafe void InsertFormat(char* buffer, ref int length, int maxLength, String format, __arglist)
        {
            int count = String.LimitedFormatTo(format, new ArgIterator(__arglist), &buffer[length], maxLength - length);
            length += count;
        }

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
            failAssert(/*"Not implemented: "+*/msg);
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
            failAssert(/*"Unreachable code reached: "+*/msg);
        }

        [Conditional("DEBUG")]
        [NoInline]
        [ManualRefCounts]
        [NoHeapAllocation]
        public static void Assert(bool expr)
        {
            if (!expr) {
                failAssert(null);
            }
        }

        [Conditional("DEBUG")]
        [NoInline]
        [ManualRefCounts]
        [NoHeapAllocation]
        public static void Deny(bool expr)
        {
            if (expr) {
                failAssert(null);
            }
        }

        [Conditional("DEBUG")]
        [NoInline]
        [ManualRefCounts]
        [NoHeapAllocation]
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

        [ManualRefCounts]
        [NoHeapAllocation]
        private static void failAssert(String s)
        {
            if (s != null) {
                Print("Assertion failed: {0}", __arglist(s));
            }
            else {
                Print("Assertion failed.");
            }
            Break();
        }

        //////////////////////////////////////////////////////////////////////
        //
        [NoHeapAllocation]
        public static ulong ReadPerfCounter(uint which)
        {
            return DebugService.ReadPerfCounter(which);
        }


        [NoHeapAllocation]
        public static bool WritePerfCounter(uint which, ulong value)
        {
            return DebugService.WritePerfCounter(which, value);
        }

        [NoHeapAllocation]
        public static bool AddToPerfCounter(uint which, ulong value)
        {
            return DebugService.AddToPerfCounter(which, value);
        }

        /////////////////////////////////////////////////////// State Methods.
        //
#if true
        [AccessedByRuntime("output to header : defined in halkd.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(638)]
        [NoHeapAllocation]
        public static extern void Break();
#else
        [NoHeapAllocation]
        public static void Break()
        {
            DebugService.Break();
        }
#endif
    }
}
