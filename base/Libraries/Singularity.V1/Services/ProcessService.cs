////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ProcessService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Reflection;
using Microsoft.Singularity.V1.Security;

[assembly: AssemblyTitle("Microsoft.Singularity.V1 ABI")]
[assembly: AssemblyProduct("Microsoft Research Singularity Operating System")]
[assembly: AssemblyCompany("Microsoft Corporation")]
[assembly: AssemblyKeyFile("public.snk")]
[assembly: AssemblyDelaySign(true)]
[assembly: AssemblyVersion("1.0.0.0")]

namespace Microsoft.Singularity.V1.Services
{

    public enum  ParameterCode {
        Success,
        OutOfRange,
        NotSet,
        Retrieved,
        Undefined,
    }

    [AccessedByRuntime("referenced from c++")]
    public struct ProcessService
    {
        //private readonly int id;

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Stop(int exitCode);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetCpuCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetRunningProcessorCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern TimeSpan GetUpTime();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(960)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern DateTime GetUtcTime();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern long GetCycleCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern long GetContextSwitchCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void SetGcPerformanceCounters(TimeSpan time, long bytes);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern long GetKernelGcCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern long GetKernelBootCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern long GetKernelInterruptCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern long GetCyclesPerSecond();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ushort GetCurrentProcessId();

        //
        //[OutsideGCDomain]
        //[NoHeapAllocation]
        //[StackBound(128)]
        //[MethodImpl(MethodImplOptions.InternalCall)]
        //public static extern PrincipalHandle GetCurrentPrincipal();
        //

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupArgCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe int GetStartupArg(int arg, char * output, int maxout);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupEndpointCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        // Return parameter is really: ExtensionContract.Exp opt(ExHeap) *
        public static extern unsafe SharedHeapService.Allocation * GetStartupEndpoint(int arg);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        // Parameter is really: ExtensionContract.Exp opt(ExHeap) *
        public static extern unsafe void SetStartupEndpoint(int arg, SharedHeapService.Allocation * ep);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1472)]
        [MethodImpl(MethodImplOptions.InternalCall)]
            // Return parameter is really: DirectoryService.Imp opt(ExHeap) *
        public static extern unsafe SharedHeapService.Allocation * GetNamespaceEndpoint();


        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern TimeSpan GetThreadTime();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern long GetThreadsCreatedCount();


        [NoHeapAllocation]
        [AccessedByRuntime("referenced from Monitoring.cpp")]
        public static unsafe bool GetSharedSourceHandles(uint infoId,
                                                         out UIntPtr storageHandle,
                                                         out UIntPtr sourceHandle,
                                                         out UIntPtr eventTypeHandle)
        {
            unsafe {
                fixed (UIntPtr * storageHandlePtr = &storageHandle) {
                    fixed (UIntPtr * sourceHandlePtr = &sourceHandle) {
                        fixed (UIntPtr * eventTypeHandlePtr = &eventTypeHandle) {

                            return GetSharedSourceHandlesImpl(infoId,
                                                              storageHandlePtr,
                                                              sourceHandlePtr,
                                                              eventTypeHandlePtr);
                        }
                    }
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1166)]
        [AccessedByRuntime("referenced from c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool GetSharedSourceHandlesImpl(uint infoId,
                                                                    UIntPtr * storageHandle,
                                                                    UIntPtr * sourceHandle,
                                                                    UIntPtr * eventTypeHandle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Waypoint0();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Waypoint(int num);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void WaypointDone();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void WaypointDump();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupStringArgCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupStringArrayArgCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupLongArgCount();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupBoolArgCount();

        [NoHeapAllocation]
        public static unsafe ParameterCode GetStartupStringArg(
            int arg,
            char * output,
            ref int inOutLength)
        {
            fixed (int * inOutLengthPtr = &inOutLength) {
                return GetStartupStringArgImpl(arg, output, inOutLengthPtr);
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1178)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe ParameterCode GetStartupStringArgImpl(
            int arg,
            char * output,
            int * inOutLength);

        [NoHeapAllocation]
        public static ParameterCode GetStartupLongArg(
            int index,
            out long value)
        {
            unsafe {
                fixed (long * valuePtr = &value) {
                    return GetStartupLongArgImpl(index, valuePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe ParameterCode GetStartupLongArgImpl(
            int index,
            long * value);

        [NoHeapAllocation]
        public static ParameterCode GetStartupBoolArg(
            int index,
            out bool value)
        {
            unsafe {
                fixed (bool * valuePtr = &value) {
                    return GetStartupBoolArgImpl(index, valuePtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1174)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe ParameterCode GetStartupBoolArgImpl(
            int index,
            bool * value);

        [NoHeapAllocation]
        public static unsafe ParameterCode GetStartupStringArrayArg(
                                                int index,
                                                char *args,
                                                int *argLengths,
                                                out int arrayLength,
                                                out int totalCharCount
                                         )
        {
            fixed (int * arrayLengthPtr = &arrayLength,
                         totalCharCountPtr = &totalCharCount) {
                return GetStartupStringArrayArgImpl(index, args, argLengths,
                    arrayLengthPtr, totalCharCountPtr);
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1186)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe ParameterCode GetStartupStringArrayArgImpl(
                                                int index,
                                                char *args,
                                                int *argLengths,
                                                int *arrayLength,
                                                int *totalCharCount
                                         );
    }
}
