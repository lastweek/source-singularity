///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: ProcessHandle.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using Microsoft.Singularity.V1.Security;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.V1.Types;

namespace Microsoft.Singularity.V1.Processes
{
    public enum ProcessState {
        Active,
        Suspended,
        Stopped,
    }

    [AccessedByRuntime("referenced from halforgc.asm")]
    public struct ProcessHandle
    {
        public readonly UIntPtr id;

        [NoHeapAllocation]
        public static unsafe bool Create(
            char *args,
            int *argLengths,
            int argCount,
            char *role,
            int roleLength,
            int endpointCount,
            out ProcessHandle handle)
        {
            fixed (ProcessHandle *handlePtr = &handle) {
                return CreateImpl(args, argLengths, argCount, role, roleLength,
                    endpointCount, handlePtr);
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(3456)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool CreateImpl(char *args,
            int *argLengths,
            int argCount,
            char *role,
            int roleLength,
            int endpointCount,
            ProcessHandle *handle);


        [NoHeapAllocation]
        public static unsafe bool Create(
            char *cmd,
            int cmdLength,
            char *action,
            int actionLength,
            char *role,
            int roleLength,
            out ProcessHandle handle)
        {
            fixed (ProcessHandle *handlePtr = &handle) {
                return CreateImpl(cmd, cmdLength, action, actionLength, role,
                    roleLength, handlePtr);
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(3456)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool CreateImpl(char *cmd,
            int cmdLength,
            char *action,
            int actionLength,
            char *role,
            int roleLength,
            ProcessHandle * handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool SetStartupEndpoint(ProcessHandle handle,
                                                            int index,
                                                            SharedHeapService.Allocation * endpoint);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(192)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Dispose(ProcessHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Start(ProcessHandle handle);

        [NoHeapAllocation]
        public static void Join(ProcessHandle handle, out bool started)
        {
            unsafe {
                fixed (bool *startedPtr = &started) {
                    JoinImpl(handle, startedPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1170)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe void JoinImpl(
            ProcessHandle handle,
            bool *started);

        [NoHeapAllocation]
        public static bool Join(ProcessHandle handle,
                                TimeSpan timeout,
                                out bool started)
        {
            unsafe {
                fixed (bool *startedPtr = &started) {
                    return JoinImpl(handle, timeout, startedPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1182)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool JoinImpl(
            ProcessHandle handle,
            TimeSpan timeout,
            bool *started);

        [NoHeapAllocation]
        public static bool Join(ProcessHandle handle,
                                SchedulerTime stop,
                                out bool started)
        {
            unsafe {
                fixed (bool *startedPtr = &started) {
                    return JoinImpl(handle, stop, startedPtr);
                }
            }
        }

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1182)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe bool JoinImpl(
            ProcessHandle handle,
            SchedulerTime stop,
            bool *started);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Suspend(ProcessHandle handle,
                                          bool recursive);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern bool Resume(ProcessHandle handle,
                                         bool recursive);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void Stop(ProcessHandle handle,
                                       int exitcode);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1152)]
        [AccessedByRuntime("called from halforgc.asm")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern void SuspendBarrier();

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetProcessId(ProcessHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetExitCode(ProcessHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern PrincipalHandle GetPrincipalHandle(ProcessHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ProcessState GetState(ProcessHandle handle);

        /// <summary>
        /// Given 2 system types generate and initialize the two endpoints of
        /// a channel. The imp side will be set in the processes startup endpoint array
        /// at position "index". The exp side will be bound to a service based on global policy
        /// </summary>
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(1024)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static unsafe extern bool BindToService(
            ProcessHandle handle,
            SystemType impType,
            SystemType expType,
            char *contract,
            int  contractLen,
            int startState,
            int index
            );

        // String Parameters

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe ParameterCode SetStartupStringArrayArg(
                                                ProcessHandle handle,
                                                int index,
                                                char *args,
                                                int *argLengths,
                                                int argCount
                                         );

#if false
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupStringArgCount(ProcessHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe int GetStartupStringArg(ProcessHandle handle,
                                            int arg, char * output, int maxout);
#endif
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe ParameterCode SetStartupStringArg(ProcessHandle handle,
                                            int arg, char * input, int length);

        // Long Parameters
#if false
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern int GetStartupLongArgCount(ProcessHandle handle);

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ParameterCode GetStartupLongArg(ProcessHandle handle,
                                                int index, out long value);
#endif
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ParameterCode SetStartupLongArg(ProcessHandle handle,
                                            int index, long value);

        // Bool Parameters
#if false

        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(128)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern ParameterCode GetStartupBoolArg(ProcessHandle handle,
                                            int index, out bool value);
#endif
        [OutsideGCDomain]
        [NoHeapAllocation]
        [StackBound(896)]
        [MethodImpl(MethodImplOptions.InternalCall)]
        public static extern unsafe ParameterCode SetStartupBoolArg(ProcessHandle handle,
                                                        int index, bool value);


    }
}
