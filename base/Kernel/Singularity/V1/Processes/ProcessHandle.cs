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
using System.Collections;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Loader;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.V1.Security;
using Microsoft.Singularity.Security;
using Microsoft.Singularity.V1.Types;

using InternalProcessState = System.Threading.ProcessState;
using ExternalProcessState = Microsoft.Singularity.V1.Processes.ProcessState;

namespace Microsoft.Singularity.V1.Processes
{
    public enum ProcessState {
        Active,
        Suspended,
        Stopped,
    }

    //| <include path='docs/doc[@for="ProcessHandle"]/*' />
    [CLSCompliant(false)]
    public struct ProcessHandle
    {
        public readonly UIntPtr id;

        public static readonly ProcessHandle Zero = new ProcessHandle();

        internal ProcessHandle(UIntPtr id)
        {
            this.id = id;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(
            char *cmdName,
            int cmdLength,
            char *actionName,
            int actionLength,
            char *role,
            int roleLength,
            ProcessHandle *handle)
        {
            return Create(cmdName, cmdLength, actionName, actionLength,
                role, roleLength, out *handle);
        }

        public static unsafe bool Create(char *cmdName,
            int cmdLength,
            char *actionName,
            int actionLength,
            char *role,
            int roleLength,
            out ProcessHandle handle) {

            Kernel.Waypoint(550);

            string mycmd = null;

            if (cmdName != null && cmdLength > 0) {
                mycmd = String.StringCTOR(cmdName, 0, cmdLength);
            }
            else {
                //should never happen
                DebugStub.Break();
            }

            string myrole = null;

            if (role != null && roleLength > 0) {
                myrole = String.StringCTOR(role, 0, roleLength);
            }

            string myaction = null;

            if (actionName != null && actionLength > 0) {
                myaction = String.StringCTOR(actionName, 0, actionLength);
            }

            Kernel.Waypoint(551);

            //
            // Find image to run.
            //
            Manifest appManifest;
            IoMemory image = Binder.LoadImage(Thread.CurrentProcess,
                mycmd,
                out appManifest);
            Kernel.Waypoint(552);
            if (image != null && image.Length > 0 && appManifest != null) {
                //
                // Check manifest to see what resources are needed
                //

                //
                // Create a Managed process, and a handle in the current
                // process to hold it.
                //

                // REVIEW: create empty args array so that we
                // do not need to change the process constructor;
                String[] myargs;
                if (myaction != null) {
                    myargs = new String[2];
                    myargs[1] = myaction;
                }
                else myargs = new String[1];
                myargs[0] = mycmd;

                Process process = new Process(Thread.CurrentProcess,
                    image,
                    myrole,
                    myargs,
                    appManifest);
                //
                // Check manifest to see what resources are needed
                //

                int epCount = appManifest.SetEndpoints(process, myaction);
#if VERBOSE
                DebugStub.WriteLine("new process create: endpoints from manifest {0}",
                                    __arglist( epCount));
#endif

                int boolCount, longCount, stringCount, stringArrayCount;
                bool ok = appManifest.GetParameterCounts(myaction,
                    out  boolCount,
                    out  longCount,
                    out  stringCount,
                    out  stringArrayCount);


                //DebugStub.WriteLine("ProcessHandle: args strings={0}, longs={1}, bools={2}",
                //    __arglist(stringCount, longCount, boolCount));

                process.SetBoolArgCount(boolCount);
                process.SetLongArgCount(longCount);
                process.SetStringArgCount(stringCount);
                process.SetStringArrayArgCount(stringArrayCount);

                handle = new ProcessHandle(
                    Thread.CurrentProcess.AllocateHandle(process));
                Tracing.Log(Tracing.Debug,
                    "ProcessHandle.Create(out id={0:x8})",
                    handle.id);
                Kernel.Waypoint(553);
                IoMemory.Release(image);
                appManifest = null;
                return true;
            }

            Tracing.Log(Tracing.Debug, "ProcessHandle.Create() failed");
            handle = new ProcessHandle();
            Kernel.Waypoint(554);
            return false;
        }

        [ExternalEntryPoint]
        public static unsafe bool CreateImpl(
            char *args,
            int *argLengths,
            int argCount,
            char *role,
            int roleLength,
            int endpointCount,
            ProcessHandle * handle)
        {
            return Create(args, argLengths, argCount, role, roleLength,
                endpointCount, out *handle);
        }

        public static unsafe bool Create(char *args,
                                         int *argLengths,
                                         int argCount,
                                         char *role,
                                         int roleLength,
                                         int endpointCount,
                                         out ProcessHandle handle)
        {
            Kernel.Waypoint(550);

            //
            // Create a kernel String[] object populated with the argument
            // values passed in from userland.
            //
            String[] arguments = new String[argCount];
            int offset = 0;

            for (int argument = 0; argument < argCount; argument++) {
                arguments[argument] = String.StringCTOR(
                    args, offset, argLengths[argument]);
                offset += argLengths[argument];
            }

            string myrole = null;

            if (role != null && roleLength > 0) {
                myrole = String.StringCTOR(role, 0, roleLength);
            }

            Kernel.Waypoint(551);

            //
            // Find image to run.
            //
            Manifest appManifest;
            IoMemory image = Binder.LoadImage(Thread.CurrentProcess,
                                              arguments[0],
                                              out appManifest);
            Kernel.Waypoint(552);
            if (image != null && image.Length > 0 && appManifest != null) {
                //
                // Check manifest to see what resources are needed
                //

                //
                // Create a Managed process, and a handle in the current
                // process to hold it.
                //
                Process process = new Process(Thread.CurrentProcess,
                                              image,
                                              myrole,
                                              arguments,
                                              appManifest);

                //
                // Check manifest to see what resources are needed
                //

                int epCount = appManifest.SetEndpoints(process,null);
#if VERBOSE
                DebugStub.WriteLine("endpoints passed in={0},  endpoints from manifest {1}",
                                    __arglist(endpointCount, epCount));
#endif
                if (epCount == 0) {
                    process.SetEndpointCount(endpointCount);
                }

                int boolCount, longCount, stringCount, stringArrayCount;
                bool ok = appManifest.GetParameterCounts(null,
                                                         out  boolCount,
                                                         out  longCount,
                                                         out  stringCount,
                                                         out  stringArrayCount);


                //DebugStub.WriteLine("ProcessHandle: args strings={0}, longs={1}, bools={2}",
                //    __arglist(stringCount, longCount, boolCount));

                process.SetBoolArgCount(boolCount);
                process.SetLongArgCount(longCount);
                process.SetStringArgCount(stringCount);
                process.SetStringArrayArgCount(stringArrayCount);

                handle = new ProcessHandle(
                    Thread.CurrentProcess.AllocateHandle(process));
                Tracing.Log(Tracing.Debug,
                            "ProcessHandle.Create(out id={0:x8})",
                            handle.id);
                Kernel.Waypoint(553);
                IoMemory.Release(image);
                appManifest = null;
                return true;
            }

            Tracing.Log(Tracing.Debug, "ProcessHandle.Create() failed");
            handle = new ProcessHandle();
            Kernel.Waypoint(554);
            return false;
        }

        /// <summary>
        /// Given 2 system types generate and initialize the two endpoints of
        /// a channel. The imp side will be set in the processes startup endpoint array
        /// at position "index". The exp side will be bound to a service based on global policy
        /// </summary>
        [ExternalEntryPoint]
        public  static unsafe bool BindToService(
                                      ProcessHandle handle,
                                      SystemType impType,
                                      SystemType  expType,
                                      char *contractChars,
                                      int contractLen,
                                      int startState,
                                      int index)
        {
            //convert contract to string
            if (contractLen == 0) return false;
            Process process = HandleTable.GetHandle(handle.id) as Process;
            string contract = String.StringCTOR(contractChars, 0, contractLen);
            if (contract == null) return false;

            return Binder.BindToService(process,
                                impType,
                                expType,
                                contract,
                                startState,
                                index);
        }

        [ExternalEntryPoint]
        public static unsafe bool SetStartupEndpoint(ProcessHandle handle,
                                                     int index,
                                                     SharedHeapService.Allocation * endpoint)
        {
            Tracing.Log(Tracing.Debug,
                        "ProcessHandle.SetStartupEndpoint(id={0:x8}, ndx={1}, ep={2:x8})",
                        handle.id, (UIntPtr)index, (UIntPtr)endpoint);

            //
            // Convert the handle to a process; set the endpoint.
            //
            SharedHeap.Allocation *ep = (SharedHeap.Allocation *)endpoint;
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return process.SetEndpoint(index, ref ep);
        }

        [ExternalEntryPoint]
        public static void Dispose(ProcessHandle handle)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Dispose(id={0:x8})",
                        handle.id);

            //
            // Releasing the handle will allow the process to be
            // garbage-collected.
            //
            Thread.CurrentProcess.ReleaseHandle(handle.id);
        }

        [ExternalEntryPoint]
        public static bool Start(ProcessHandle handle)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Start(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; call Start method.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return process.Start();
        }

        [ExternalEntryPoint]
        public static unsafe void JoinImpl(ProcessHandle handle, bool * started)
        {
            Join(handle, out *started);
        }

        public static void Join(ProcessHandle handle, out bool started)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Join(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; call Join method.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;

            process.Join(out started);
        }

        [ExternalEntryPoint]
        public static unsafe bool JoinImpl(
            ProcessHandle handle,
            TimeSpan timeout,
            bool * started)
        {
            return Join(handle, timeout, out *started);
        }

        public static bool Join(ProcessHandle handle,
                                TimeSpan timeout,
                                out bool started)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Join(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; call Join method.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;
            bool ret = process.Join(timeout, out started);

            return ret;
        }

        [ExternalEntryPoint]
        public static unsafe bool JoinImpl(
            ProcessHandle handle,
            SchedulerTime stop,
            bool * started)
        {
            return Join(handle, stop, out *started);
        }

        public static bool Join(ProcessHandle handle,
                                SchedulerTime stop,
                                out bool started)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Join(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; call Join method.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;
            bool ret = process.Join(stop, out started);

            return ret;
        }

        [ExternalEntryPoint]
        public static bool Suspend(ProcessHandle handle, bool recursive)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Suspend(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; call Suspend method.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return process.Suspend(recursive);
        }

        [ExternalEntryPoint]
        public static bool Resume(ProcessHandle handle, bool recursive)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Resume(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; call Resume method.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return process.Resume(recursive);
        }

        [ExternalEntryPoint]
        public static void Stop(ProcessHandle handle, int exitcode)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.Stop(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; call Stop method.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;
            process.Stop(exitcode);
        }

        [ExternalEntryPoint]
        public static void SuspendBarrier()
        {
            Process.SuspendBarrier();
        }

        [ExternalEntryPoint]
        public static int GetProcessId(ProcessHandle handle)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.GetProcessId(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; retrieve ProcessId.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;

            return process.ProcessId;
        }

        [ExternalEntryPoint]
        public static int GetExitCode(ProcessHandle handle)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.GetExitCode(id={0:x8})",
                        handle.id);

            //
            // Convert the handle to a process; retrieve ExitCode.
            //
            Process process = HandleTable.GetHandle(handle.id) as Process;

            return process.ExitCode;
        }

        [ExternalEntryPoint]
        public static PrincipalHandle GetPrincipalHandle(ProcessHandle handle)
        {
            Tracing.Log(Tracing.Debug, "ProcessHandle.GetPrincipalHandle(id={0:x8})", handle.id);

            Process process = HandleTable.GetHandle(handle.id) as Process;
            return new PrincipalHandle(process.Principal.Val);
        }

        [ExternalEntryPoint]
        public static ExternalProcessState GetState(ProcessHandle handle)
        {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            switch (process.State) {
            case InternalProcessState.Unstarted:
            case InternalProcessState.Running:
                return ExternalProcessState.Active;

            case InternalProcessState.Suspending:
            case InternalProcessState.SuspendingRecursive:
            case InternalProcessState.Suspended:
                return ExternalProcessState.Suspended;

            case InternalProcessState.Stopping:
            case InternalProcessState.Stopped:
                return ExternalProcessState.Stopped;

            default:
                // handle new missing case
                DebugStub.Break();
                return ExternalProcessState.Stopped;
            }
        }

        [ExternalEntryPoint]
        public static unsafe ParameterCode SetStartupStringArrayArg (
                                         ProcessHandle handle,
                                         int index,
                                         char *args,
                                         int *argLengths,
                                         int argCount)
        {
            Process process = HandleTable.GetHandle(handle.id) as Process;

            //
            // Create a kernel String[] object populated with the argument
            // values passed in from userland.
            //
            String[] arguments = new String[argCount];
            int offset = 0;

            for (int argument = 0; argument < argCount; argument++) {
                arguments[argument] = String.StringCTOR(
                    args, offset, argLengths[argument]);
                offset += argLengths[argument];
            }

           return (ParameterCode) process.SetStartupStringArrayArg(index, arguments);
        }
#if false
        [ExternalEntryPoint]
        public static int GetStartupStringArgCount(ProcessHandle handle) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return process.GetStartupStringArgCount();
        }

        [ExternalEntryPoint]
        public static unsafe int GetStartupStringArg(ProcessHandle handle, int arg, char * output, int maxput) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            string s = process.GetStartupStringArg(arg);
            Tracing.Log(Tracing.Debug,
                "Process.GetStartupStringArg(arg={0}, out={1:x8}, max={2}) = {3}",
                (UIntPtr)unchecked((uint)arg),
                (UIntPtr)output,
                (UIntPtr)unchecked((uint)maxput),
                (UIntPtr)unchecked((uint)(s != null ? s.Length : 0)));

            if (s == null) {
                return 0;
            }
            if (output == null) {
                return s.Length + 1;
            }
            return s.InternalGetChars(output, maxput);
        }
#endif
        [ExternalEntryPoint]
        public static unsafe ParameterCode SetStartupStringArg(
                ProcessHandle handle, int arg, char * input, int length)
        {
            string s;
            if (length == 0) s = null;
            else s = String.StringCTOR(input, 0, length);
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return (ParameterCode) process.SetStartupStringArg(arg, s);
        }
#if false
        [ExternalEntryPoint]
        public static int GetStartupLongArgCount(ProcessHandle handle) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return process.GetStartupLongArgCount();
        }

        [ExternalEntryPoint]
        public static ParameterCode GetStartupLongArg(ProcessHandle handle, int index, out long value) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return (ParameterCode) process.GetStartupLongArg(index, out value);
        }
#endif
        [ExternalEntryPoint]
        public static ParameterCode SetStartupLongArg(ProcessHandle handle, int index, long value) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return (ParameterCode) process.SetStartupLongArg(index, value);
        }
#if false
        [ExternalEntryPoint]
        public static int GetStartupBoolArgCount(ProcessHandle handle) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return process.GetStartupBoolArgCount();
        }

        [ExternalEntryPoint]
        public static ParameterCode GetStartupBoolArg(ProcessHandle handle, int index, out bool value) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return (ParameterCode)process.GetStartupBoolArg(index, out value);
        }
#endif
        [ExternalEntryPoint]
        public static ParameterCode SetStartupBoolArg(ProcessHandle handle, int index, bool value) {
            Process process = HandleTable.GetHandle(handle.id) as Process;
            return (ParameterCode) process.SetStartupBoolArg(index, value);
        }

    }
}
