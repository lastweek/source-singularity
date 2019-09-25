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
using System.Reflection;
using System.Threading;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

using Microsoft.Bartok.Runtime;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.V1.Services;

using Microsoft.Singularity.Eventing;

[assembly: AssemblyTitle("Microsoft.Singularity")]
[assembly: AssemblyProduct("Microsoft Research Singularity Runtime")]
[assembly: AssemblyCompany("Microsoft Corporation")]
[assembly: AssemblyVersion("1.0.0.0")]
[assembly: AssemblyKeyFile("public.snk")]
[assembly: AssemblyDelaySign(true)]

namespace Microsoft.Singularity
{

    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from hal.cpp")]
    public class AppRuntime
    {
        // Note: This function is called by Hal.cpp.
        [AccessedByRuntime("referenced from hal.cpp")]
        public static unsafe int AppStart(Type userClass)
        {
            System.GCs.Transitions.ThreadStart();

            int result = 0;

            string arg0 = "(unknown)";

            try {
                Tracing.Log(Tracing.Audit, "Runtime.Main()");

                // Initialize the primitive runtime, which calls the
                // class constructor for Runtime().
                VTable.Initialize((RuntimeType)typeof(AppRuntime));
                //VTable.ParseArgs(args);  

                Tracing.Log(Tracing.Audit, "Enabling GC Heap");
                GC.EnableHeap();
                Controller.InitializeSystem();
                GCProfilerLogger.StartProfiling();

                InitializeConsole();

                SetDebuggerPresence(DebugService.IsDebuggerPresent());

                int argCount = 0;
                int argMaxLen = 0;
                for (;; argCount++) {
                    int len = ProcessService.GetStartupArg(argCount, null, 0);
                    if (len == 0) {
                        break;
                    }
                    if (argMaxLen < len) {
                        argMaxLen = len;
                    }
                }
                char[] argArray = new char [argMaxLen];
                string[] args = new string[argCount];
                for (int arg = 0; arg < argCount; arg++) {
                    fixed (char *argptr = &argArray[0]) {
                        int len = ProcessService.GetStartupArg(arg,
                                                               argptr,
                                                               argArray.Length);
                        args[arg] = String.StringCTOR(argptr, 0, len);
                        if (arg == 0)
                            arg0 = args[arg];
                    }
                }

#if DEBUG || true
                // Record the first argument passed to this program, under the assumption that
                // this is the application name.  We use this string in DebugStub.WriteLine.
                // Also, if the name has an extension, such as ".x86", chop it off.
                // Also chop off any path prefix, such as "/init/".
                appName = arg0;
                int index = appName.LastIndexOf('.');
                if (index != -1)
                    appName = appName.Substring(0, index);
                index = appName.LastIndexOf('/');
                if (index != -1)
                    appName = appName.Substring(index + 1);

                // The default DebugName value for the main thread is "main";
                // apps can override this by setting Thread.CurrentThread.DebugName.
                Thread mainThread = Thread.CurrentThread;
                if (mainThread != null) {
                    mainThread.DebugName = "main";
                }
#endif

                if (userClass != null) {
                    VTable.initType((RuntimeType)userClass);
                }

                result = CallMain(args);
                if (!MainReturnsInt()) result = 0;

                Tracing.Log(Tracing.Audit, "Main thread exited [{0}]",
                            (UIntPtr)unchecked((uint)result));
            }
            catch (Exception e) {
                Tracing.Log(Tracing.Fatal, "Failed with exception {0}.{1}",
                            e.GetType().Namespace, e.GetType().Name);
                Tracing.Log(Tracing.Trace, "Exception message was {0}",
                            e.ToString());
                TopLevelException(e);
                result = -1;
            }

            Thread.RemoveThread(Thread.CurrentThread.threadIndex);
            Thread.JoinAll();

            try {
                FinalizeConsole();
            }
            catch (Exception e) {
                Tracing.Log(Tracing.Fatal, "An exception occurred while shutting down the console: {0}",
                    e.ToString());
            }

            Controller.Finalize();
            Tracing.Log(Tracing.Audit, "Runtime shutdown started.");
            VTable.Shutdown(result);
            Tracing.Log(Tracing.Audit, "Runtime exiting [{0}]",
                        (UIntPtr)unchecked((uint)result));
            return result;
        }


        /// <summary>
        /// This method runs when the "main" thread terminates by throwing an exception.
        /// It is a separate method, rather than simply code within the AppStart method,
        /// in order to make life easier during debugging.
        /// </summary>
        /// <param name="ex"></param>
        private static void TopLevelException(Exception/*!*/ ex)
        {
            DebugStub.WriteLine("AppRuntime: Main app thread terminated with exception:");
            for (Exception focus = ex; focus != null; focus = focus.InnerException) {
                DebugStub.WriteLine("{0}: {1}", __arglist(focus.GetType().FullName, focus.Message));
            }
        }

#if DEBUG || true
        /// <summary>
        /// Returns the name of the application, as determined by the first parameter
        /// passed in the argv block.  This property is only present on DEBUG builds 
        /// (Debug and Prototype).  It is provided for DebugStub.WriteLine, to provide 
        /// useful debugging spew.
        /// </summary>
        public static string AppName
        {
            [NoHeapAllocation]
            get
            {
                return appName;
            }
        }

        private static string appName;
#endif

        [AccessedByRuntime("output to header : defined in hal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        private static extern int CallMain(String[] args);

        [AccessedByRuntime("output to header: defined in hal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        private static extern bool MainReturnsInt();

        [AccessedByRuntime("output to header: defined in hal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        private static extern void SetDebuggerPresence(bool debuggerPresent);

        internal static void Shutdown(int exitCode)
        {
            //
            // Gracefully close down the process.
            //
            Tracing.Log(Tracing.Audit, "Runtime.Shutdown({0})",
                        (UIntPtr)unchecked((uint)exitCode));

            DebugStub.WriteLine("Runtime.Shutdown({0})", __arglist(exitCode));

            VTable.Shutdown(exitCode);
            Tracing.Log(Tracing.Audit, "Runtime.Shutdown({0}) terminating",
                        (UIntPtr)unchecked((uint)exitCode));
            ProcessService.Stop(exitCode);
        }

        internal static void Stop(int exitCode)
        {
            //
            // Halt the process immediately.
            //
            Tracing.Log(Tracing.Audit, "Runtime.Stop({0})",
                        (UIntPtr)unchecked((uint)exitCode));

            DebugStub.WriteLine("Runtime.Stop({0})", __arglist(exitCode));

            ProcessService.Stop(exitCode);
        }

        //////////////////////////////////////////////////////////////////////
        //
        [NoHeapAllocation]
        public static UIntPtr AddressOf(Object o)
        {
            return Magic.addressOf(o);
        }

        [NoHeapAllocation]
        public static UIntPtr SizeOf(Object o)
        {
            return System.GCs.ObjectLayout.Sizeof(o);
        }

        public static void InitType(Type ty)
        {
            VTable.initType((RuntimeType) ty);
        }

        public static void DumpPageTable()
        {
            System.GCs.PageTable.Dump("PageTable");
        }

        //////////////////////////////////////////////////////////////////////
        //
        public static bool EnableGCVerify
        {
            get {
                return VTable.enableGCVerify;
            }
            set {
                VTable.enableGCVerify = value;
            }
        }

        public static bool EnableGCAccounting
        {
            get {
                return VTable.enableGCAccounting;
            }
            set {
                VTable.enableGCAccounting = value;
                if (value == true) {
                    System.GCs.MemoryAccounting.Initialize(GC.gcType);
                }
            }
        }

        public static uint GCPerfCounter
        {
            get {
                return System.GC.perfCounter;
            }
            set {
                System.GC.perfCounter = value;
            }
        }

        /// <summary>
        /// This stub method is provided for so that System.Console.dll can override it for those
        /// apps that want a console.  This is necessary, in order to initialize and shutdown the
        /// console at the right time.
        /// </summary>
        private static void InitializeConsole()
        {
        }

        /// <summary>
        /// This stub method is provided for so that System.Console.dll can override it for those
        /// apps that want a console.  This is necessary, in order to initialize and shutdown the
        /// console at the right time.
        /// </summary>
        private static void FinalizeConsole()
        {
        }
    }
}
