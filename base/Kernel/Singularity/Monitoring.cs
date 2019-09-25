////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:  Monitoring.cs
//
//  Note:  Provides a little bit more sophisticated runtime monitoring (i.e.,
//         writing and reading events will be possible concurrently at runtime)
//         facility for performance and other debugging
//
//

using System;
using System.Diagnostics;
using System.Text;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity
{
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from Monitoring.cpp")]
    public class Monitoring
    {
        [AccessedByRuntime("referenced from Monitoring.cpp")]
        public struct LogEntry
        {
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public ulong    cycleCount;     // bytes 0..7
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public UIntPtr  eip;            // bytes 8..11
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public ushort   threadId;       // bytes 12..13
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public ushort   processId;      // bytes 14..15
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public ushort   provider;       // bytes 16..17
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public ushort   type;           // bytes 18..19
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public unsafe byte * text;      // bytes 20..23
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public ushort   cpu;           // bytes 24..25
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public ushort   version;       // bytes 26..27
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public UIntPtr  arg0;           // bytes 28..31
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public UIntPtr  arg1;           // bytes 32..35
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public UIntPtr  arg2;           // bytes 36..38
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public UIntPtr  arg3;           // bytes 40..43
            [AccessedByRuntime("referenced from Monitoring.cpp")]
            public UIntPtr  arg4;           // bytes 44..47
        }

        // This does not work, probably a Bartok problem
//        [AccessedByRuntime("referenced from Monitoring.cpp")]
//        public struct IndexEntry
//        {
//            [AccessedByRuntime("referenced from Monitoring.cpp")]
//            public /*volatile*/ ulong data;     // bytes 0..7
//        }

        // Note: These fields are initialized by the code in Monitoring.cpp.
        //
        [AccessedByRuntime("referenced from Monitoring.cpp")]
        private static unsafe byte * buffer;
        //
        // End Note.

        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(64)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Initialize();

#if SINGULARITY_KERNEL
        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        private static unsafe void InitPages(UIntPtr bytes)
        {
            UIntPtr pages = MemoryManager.PagesFromBytes(
                MemoryManager.PagePad(bytes));

            buffer = (byte *)MemoryManager.KernelAllocate(
                pages, null, 0, System.GCs.PageType.NonGC).ToPointer();
        }

        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        private static unsafe UIntPtr InitText(UIntPtr bytes)
        {
            UIntPtr pages = MemoryManager.PagesFromBytes(
                MemoryManager.PagePad(bytes));

            return MemoryManager.KernelAllocate(
                pages, null, 0, System.GCs.PageType.NonGC);
        }
#endif

        // Well-known provider IDs   
        public struct Provider
        {
            public const ushort SysInfo          = 1;
            public const ushort Cassini          = 3;
            public const ushort Shell            = 5;
            public const ushort Endpoint         = 8;
            public const ushort ChannelService   = 9;
            public const ushort WaitHandle       = 10;
            public const ushort AutoResetEvent   = 11;
            public const ushort Mutex            = 12;
            public const ushort ManualResetEvent = 13;
            public const ushort EndpointCore     = 14;
            public const ushort Process          = 19;
            public const ushort Thread           = 20;
            public const ushort DiskIo           = 21;
            public const ushort WebServer        = 22;  // Not Cassini
            public const ushort Directory        = 23;  // see Windows\ETS\Directory.tmf
            public const ushort GC               = 25;
            public const ushort Iso9660          = 26;
            public const ushort Processor        = 30;
        }

        [Conditional("Monitoring")]
        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern void Log(ushort provider, ushort type,
            ushort version, uint a0, uint a1,
            uint a2, uint a3, uint a4);

        [Conditional("Monitoring")]
        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern void Log(ushort provider, ushort type);

        [Conditional("Monitoring")]
        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern void Log(ushort provider, ushort type,
            string s);

        // \brief Return one LogEntry to caller
        // \param min_counter minimum event counter to read event for, will be
        //                    modified and contains the actually read event in
        //                    it after return
        // \param log         log entry to be filled
        // 
        public static unsafe int GetEntry(ref ulong min_counter,
                                          out LogEntry log)
        {
            int ret;

            fixed (LogEntry * pl = &log)
            {
                fixed (ulong * pm = &min_counter)
                {
                    ret = FillLogEntry(pl, pm);
                }
            }
            return ret;
        }

        // \brief Return text part for log entry
        // \param src      where to get the data from
        // \param counter  counter to expect at start of src
        // \param dst      where to copy the byte array to
        // \param max_size copy max_size bytes at max
        // 
        public static unsafe int GetText(byte * src, ulong counter, byte * dst,
                                         int max_size)
        {
            int ret;

            ret = FillTextEntry(src, counter, dst, max_size);
            return ret;
        }

        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern int FillLogEntry(LogEntry * log,
                                                     ulong * min_counter);

        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern int
        FillTextEntry(byte * src, ulong counter, byte * dst, int max_size);

        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(32)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern bool isActive();

        [AccessedByRuntime("output to header : defined in Monitoring.cpp")]
        [StackBound(32)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern void setActive(bool active);
    }
}
