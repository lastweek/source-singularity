////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Windows.cs
//
//  Note:   P/Invoke definitions for manipulating threads, processes, and jobs.
//

using System;
using System.Diagnostics;
using System.ComponentModel;
using System.Runtime.InteropServices;


// This only works on kernels later than Vista, XP64, and W2003S.
// Notably, it does not work on XP 32-bit.  So, we can't learn which
// processors are virtual processors (HyperThreading), so we can't
// make sure that we schedule jobs only on the main virtual processor
// of each physical core yet.  The reason to do this is because
// HyperThreading really doesn't work for CPU-bound tasks; in nearly
// all tests, running CPU-bound tasks on both virtual processors of
// a single hyper-threaded core results in *worse* performance, largely
// due to the increased cache pressure.
//
// #define ENABLE_LOGICAL_PROCESSOR_INFORMATION


namespace Windows
{
    public class Kernel32
    {
        const string DllName = "KERNEL32.DLL";

        [DllImport(DllName, CharSet = CharSet.Unicode)]
        static extern IntPtr CreateJobObject(
            IntPtr SecurityAttributes,
            string Name);

        public static IntPtr CreateJobObject()
        {
            IntPtr handle = CreateJobObject(IntPtr.Zero, null);
            if (handle == IntPtr.Zero || handle == ((IntPtr)~0)) {
                int error = Marshal.GetLastWin32Error();
                throw new Exception("The job object could not be created.",
                    new Win32Exception(error));
            }

            return handle;
        }

        [DllImport(DllName, SetLastError = true)]
        public static extern bool CloseHandle(IntPtr ObjectHandle);

        [DllImport(DllName, SetLastError = true)]
        public static extern bool AssignProcessToJobObject(
            IntPtr JobHandle,
            IntPtr ProcessHandle);

        [DllImport(DllName, SetLastError=true)]
        static unsafe extern bool QueryInformationJobObject(
            IntPtr JobHandle,
            JobObjectInformationClass InformationClass,
            void* Buffer,
            int BufferLength,
            out int ReturnLength);

        public static JOBOBJECT_BASIC_ACCOUNTING_INFORMATION
            QueryJobObjectBasicAccountingInformation(IntPtr JobHandle)
        {
            unsafe
            {
                JOBOBJECT_BASIC_ACCOUNTING_INFORMATION buffer;
                int length;

                if (!QueryInformationJobObject(
                    JobHandle,
                    JobObjectInformationClass.Accounting,
                    &buffer,
                    sizeof(JOBOBJECT_BASIC_ACCOUNTING_INFORMATION),
                    out length))
                {
                    int error = Marshal.GetLastWin32Error();
                    throw new Exception("Failed to query information from job object.",
                        new Win32Exception(error));
                }
                return buffer;
            }
        }

        public static bool IsCurrentProcessInJob()
        {
            unsafe
            {
                JOBOBJECT_BASIC_ACCOUNTING_INFORMATION information = new JOBOBJECT_BASIC_ACCOUNTING_INFORMATION();
                int returnLength = 0;

                if (QueryInformationJobObject(IntPtr.Zero, JobObjectInformationClass.Accounting,
                    &information, sizeof(JOBOBJECT_BASIC_ACCOUNTING_INFORMATION), out returnLength))
                {
                    return true;
                }
                else {
                    return false;
                }
            }
        }


        [DllImport(DllName, SetLastError = true, CharSet=CharSet.Unicode)]
        static unsafe extern int FormatMessage(
            FormatMessageFlag flags,
            void* Source,
            int MessageId,
            int LanguageId,
            void* Buffer,
            int BufferLength,
            void* Arguments);

        public static unsafe string FormatMessageFromSystem(int messageId, int languageId)
        {
            char* buffer = null;

            int length = FormatMessage(
                FormatMessageFlag.AllocateBuffer | FormatMessageFlag.FromSystem,
                null,
                messageId,
                languageId,
                (void*)&buffer,
                0,
                null);
            if (length == 0)
                return null;

            string result = new String(buffer, 0, length);
            Marshal.FreeHGlobal((IntPtr)(void*)buffer);
            return result;
        }

        public unsafe static string FormatMessageFromSystem(int messageId)
        {
            return FormatMessageFromSystem(messageId, 0);
        }

        public static string GetErrorText(int error)
        {
            string text = FormatMessageFromSystem(error);
            if (text == null) {
                if (error < 0x10000 && error >= 0)
                    return String.Format("Unknown error: {0]", error);
                else
                    return String.Format("Unknown error: 0x{0:x}", error);
            }
            else {
                return text;
            }
        }

        [DllImport(DllName, SetLastError = true)]
        public static extern uint SetThreadIdealProcessor(
            IntPtr ThreadHandle,
            int IdealProcessor);

        [DllImport(DllName, SetLastError = true)]
        public static extern bool GetProcessAffinityMask(
            IntPtr ProcessHandle,
            out UIntPtr ProcessAffinityMask,
            out UIntPtr SystemAffinityMask);

        [DllImport(DllName)]
        public static extern IntPtr GetCurrentThread();

        [DllImport(DllName)]
        public static extern IntPtr GetCurrentProcess();

        [DllImport(DllName, SetLastError = true)]
        public static extern bool GetThreadTimes(
          IntPtr hThread,
          out /* FILETIME */ long lpCreationTime,
          out /* FILETIME */ long lpExitTime,
          out /* FILETIME */ long lpKernelTime,
          out /* FILETIME */ long lpUserTime
        );

        public void GetThreadTimes(
            IntPtr ThreadHandle,
            out DateTime creationTime,
            out DateTime exitTime,
            out TimeSpan kernelTime,
            out TimeSpan userTime)
        {
            long ticks_creationTime;
            long ticks_exitTime;
            long ticks_kernelTime;
            long ticks_userTime;

            if (GetThreadTimes(ThreadHandle,
                out ticks_creationTime,
                out ticks_exitTime,
                out ticks_kernelTime,
                out ticks_userTime))
            {
                creationTime = new DateTime(ticks_creationTime);
                exitTime = new DateTime(ticks_exitTime);
                kernelTime = new TimeSpan(ticks_kernelTime);
                userTime = new TimeSpan(ticks_userTime);
            }
            else {
                throw new Exception("The thread times could not be retrieved.",
                    new Win32Exception(Marshal.GetLastWin32Error()));
            }
        }
        

        public static int GetProcessorCount()
        {
            UIntPtr processAffinityMask;
            UIntPtr systemAffinityMask;

            if (!GetProcessAffinityMask(GetCurrentProcess(), out processAffinityMask, out systemAffinityMask)) {
                Console.WriteLine("nib: Failed to get process affinity mask!  Assuming 1 processor.");
                return 1;
            }

            ulong mask = (ulong)processAffinityMask;
            int count = 0;
            while (mask != 0) {
                if ((mask & 1) != 0)
                    count++;
                mask >>= 1;
            }

            if (count == 0)
                return 1;

            Console.WriteLine("nib: Found {0} processors.", count);
            return count;
        }

        public static string GetLastErrorText()
        {
            int error = Marshal.GetLastWin32Error();
            return GetErrorText(error);
        }

#if ENABLE_LOGICAL_PROCESSOR_INFORMATION
        [DllImport(DllName, SetLastError=true)]
        static unsafe extern bool GetLogicalProcessorInformation(
            SYSTEM_LOGICAL_PROCESSOR_INFORMATION* buffer,
            ref int length);

        public static SYSTEM_LOGICAL_PROCESSOR_INFORMATION[] GetLogicalProcessorInformation()
        {
            unsafe
            {
                int length = 0;

                GetLogicalProcessorInformation(null, ref length);
                if (length == 0)
                    return new SYSTEM_LOGICAL_PROCESSOR_INFORMATION[0];

                int count = length / sizeof(SYSTEM_LOGICAL_PROCESSOR_INFORMATION);
                SYSTEM_LOGICAL_PROCESSOR_INFORMATION[] array = new SYSTEM_LOGICAL_PROCESSOR_INFORMATION[count];

                bool result;
                fixed (SYSTEM_LOGICAL_PROCESSOR_INFORMATION* array_pinned = &array[0])
                {
                    int length2 = sizeof(SYSTEM_LOGICAL_PROCESSOR_INFORMATION) * count;
                    result = GetLogicalProcessorInformation(array_pinned, ref length2);
                }
                if (result)
                    return array;
                else
                    throw new Exception("Failed to query logical processor information.",
                        new Win32Exception(Marshal.GetLastWin32Error()));
            }
        }


        public static int[] GetPhysicalProcessorList()
        {
            SYSTEM_LOGICAL_PROCESSOR_INFORMATION[] logical_info = GetLogicalProcessorInformation();

            for (int i = 0; i < logical_info.Length; i++) {
                Debug.WriteLine(logical_info.ToString());
            }

            return null;
        }
#endif


    }

    [Flags]
    enum FormatMessageFlag
    {
        AllocateBuffer = 0x100,
        FromSystem = 0x1000,
        FromModule = 0x800,
    }

    public enum JobObjectInformationClass
    {
        Accounting = 1, // JOBOBJECT_BASIC_ACCOUNTING_INFORMATION
    }

    [StructLayout(LayoutKind.Sequential)]
    public struct JOBOBJECT_BASIC_ACCOUNTING_INFORMATION
    {
        public TimeSpan TotalUserTime;
        public TimeSpan TotalKernelTime;
        public TimeSpan ThisPeriodTotalUserTime;
        public TimeSpan ThisPeriodTotalKernelTime;
        public uint TotalPageFaultCount;
        public uint TotalProcesses;
        public uint ActiveProcesses;
        public uint TotalTerminatedProcesses;
    }


#if ENABLE_LOGICAL_PROCESSOR_INFORMATION
    [StructLayout(LayoutKind.Sequential)]
    struct SYSTEM_LOGICAL_PROCESSOR_INFORMATION
    {
        public UIntPtr ProcessorMask;
        public LOGICAL_PROCESSOR_RELATIONSHIP Relationship;

        //
        //union {
        //  struct
        //  {
        //      BYTE Flags;
        //  } ProcessorCore;
        //  struct
        //  {
        //      DWORD NodeNumber;
        //  } NumaNode;
        //  CACHE_DESCRIPTOR Cache;
        //  ULONGLONG Reserved[2];
        //}
        //

        public ProcessorRelationUnion RelationUnion;
    }

    [StructLayout(LayoutKind.Explicit)]
    struct ProcessorRelationUnion
    {
        [FieldOffset(0)] public CACHE_DESCRIPTOR Cache;
        [FieldOffset(0)] public uint NumaNodeNumber;
        [FieldOffset(0)] public byte ProcessorCoreFlags;
    }

    [StructLayout(LayoutKind.Sequential)]
    struct CACHE_DESCRIPTOR
    {
        public byte Level;
        public byte Associativity;
        public ushort LineSize;
        public uint Size;
        public PROCESSOR_CACHE_TYPE Type;
    }

    enum PROCESSOR_CACHE_TYPE
    {
        Unified = 0,
        Instruction = 1,
        Data = 2,
        Trace = 3,
    }

    enum LOGICAL_PROCESSOR_RELATIONSHIP : uint
    {
        ProcessorCore = 0,
        NumaNode = 1,
        RelationCache = 2,
    }
#endif
}
