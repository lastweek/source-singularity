///////////////////////////////////////////////////////////////////////////////
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

using Microsoft.Bartok.Runtime;

using Microsoft.SingSharp;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Drivers;
using Microsoft.Singularity.Eventing;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Loader;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Scheduling;
using Microsoft.Singularity.Security;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Xml;

[assembly: AssemblyTitle("Microsoft.Singularity")]
[assembly: AssemblyProduct("Microsoft Research Singularity Operating System")]
[assembly: AssemblyCompany("Microsoft Corporation")]
[assembly: AssemblyVersion("1.0.0.0")]
[assembly: AssemblyKeyFile("public.snk")]
[assembly: AssemblyDelaySign(true)]

namespace Microsoft.Singularity
{

    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from hal.cpp/hal.cpp")]
    public class Kernel
    {
        private static string[] args;
        private static ManualResetEvent mpEndEvent;
        private static int bootReturnCode;

        //  sample profiler kernel data
        public static uint ProfilerBufferSize;

#region Waypoints

        public static long[]    Waypoints;
        public static int[]     WaypointSeq;
        public static int[]     WaypointThd;
        public static int       WaypointNumber;// = 0;
        public static long      WaypointSamples;// = 0;
        public static bool      WaypointSuspicious;
        public static uint      WaypointInterrupt;
        public const int        NWP = 2048; // XXX PBAR if this is readonly then it seems to read as 0!

        // This is temporary, until we get a HAL-based plug-and-play system going.
        public const byte       HalIpiInterrupt = 249;

        /// <summary> Flag indicating if kernel has succesfully booted </summary>
        private static bool             hasBooted;
        private static Scheduler        scheduler;

        ///
        /// <summary>
        ///     Property to find out if kernel finished booting
        /// </summary>
        ///
        public static bool HasBooted
        {
            [NoHeapAllocation]
            get
            {
                return hasBooted;
            }
        }

        /// <summary>
        ///     Get a default kernel scheduler
        /// </summary>
        internal static Scheduler TheScheduler
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return scheduler;
            }
        }

        [Conditional("WAYPOINTS")]
        [NoHeapAllocation]
        public static void Waypoint0()
        {
            WaypointSamples++;
            Waypoints[0] = (long)Processor.CycleCount;
            WaypointNumber = 1;
            WaypointSuspicious = false;
            WaypointInterrupt = Processor.CurrentProcessor.NumInterrupts;
        }

        [Conditional("WAYPOINTS")]
        [NoHeapAllocation]
        public static void Waypoint(int num)
        {
            if (Waypoints == null || Waypoints[0] == 0 || WaypointNumber > NWP - 1) {
                return;
            }

            long delta = (long)Processor.CycleCount - Waypoints[0];
            if (delta > 7000000) {
                WaypointSuspicious = true;
            }

            WaypointSeq[WaypointNumber] = num;
            WaypointThd[WaypointNumber] = Thread.GetCurrentThreadIndex();
            Waypoints[WaypointNumber++] = delta;
        }

        [Conditional("WAYPOINTS")]
        [NoHeapAllocation]
        public static void WaypointDone()
        {
            Waypoints[0] = 0;
        }

#if false
        [Conditional("WAYPOINTS")]
        [NoHeapAllocation]
        public static void WaypointDump()
        {
            WaypointDump(NWP);
        }
#endif

        [Conditional("WAYPOINTS")]
        public static void WaypointDump()
        {
            bool iflag = Processor.DisableInterrupts();

            DebugStub.WriteLine("Interrupts: {0}",
                                __arglist(Processor.CurrentProcessor.NumInterrupts
                                          - WaypointInterrupt));
            DebugStub.WriteLine("WPT Waypoint   Sequence   THD Diff");

            for (int i = 1; i < WaypointNumber; i++) {
                DebugStub.WriteLine("{0,3:d} {1,10:d} {2,10:d} {3,3:d} {4,10:d}",
                                    __arglist(
                                        i,
                                        Waypoints[i],
                                        WaypointSeq[i],
                                        WaypointThd[i].GetHashCode(),
                                        Waypoints[i] - Kernel.Waypoints[i-1]));
            }
            Processor.RestoreInterrupts(iflag);
        }

        [Conditional("WAYPOINTS")]
        [NoHeapAllocation]
        public static void WaypointReset()
        {
            for (int i = 0; i < NWP; i++) {
                Waypoints[i] = 0;
            }
            WaypointSamples = 0;
        }
#endregion // Waypoints

        internal static DateTime BootTime;

        //        [System.Diagnostics.Conditional("ISA_ARM")]
        private static void ARM_PROGRESS(string msg)
        {
            DebugStub.WriteLine(msg);
        }

        [System.Diagnostics.Conditional("ISA_ARM")]
        private static void ARM_SPIN_FOREVER(string msg)
        {
            DebugStub.Assert(!Processor.InterruptsDisabled());
            Processor p = Processor.CurrentProcessor;

            DebugStub.WriteLine(msg);
            DateTime last = DateTime.Now;

            uint n = 0;

            while (true) {
                Thread.Sleep(1000);
            }
        }

        // Note: This function is called by Hal.cpp.
        [AccessedByRuntime("referenced from hal.cpp")]
        internal static int Main()
        {
            bootReturnCode = Platform.EXIT_AND_RESTART;
            InitPreMonitoring();
            try {
                InitServices();
                // Consider boot successful at this stage.
                bootReturnCode = Platform.EXIT_AND_SHUTDOWN;

                ARM_SPIN_FOREVER("kernel.arm Spinning forever");

                bootReturnCode = SpawnAndWaitForShell();
                // The shell has exited when we get here

                FinalizeServices();
            }
            catch (Exception e) {
                System.Console.WriteLine("EXCEPTION:: " + e.Message);
                Tracing.Log(Tracing.Fatal, "Caught exception {0}", e.Message);
                DebugStub.WriteLine("Caught {0}", __arglist(e.Message));
                bootReturnCode = -1;
                DebugStub.Break();
            }
            DebugStub.WriteLine("Kernel exiting with 0x{0:x4}", __arglist(bootReturnCode));
            FinalizePreMonitoring();
            if (bootReturnCode != Platform.EXIT_AND_WARMBOOT) {
                Kill(bootReturnCode);
            }
            return bootReturnCode;
        }

        private static void InitPreMonitoring()
        {
            Tracing.Log(0);
            Tracing.Log(1);
            Tracing.Log(2);
            Tracing.Log(3);
            DebugStub.WriteLine("-------------------------------------------------------------------------------");

            ARM_PROGRESS("Kernel!001");
            // Indicate that we are not booted yet
            hasBooted = false;

            // Rather than mark all bootstrap code with [NoBarriers], perform a mini-
            // initialization that gives us a working WriteBarrier.
            System.GCs.Barrier.PreInitialize();

            ARM_PROGRESS("Kernel!002");
            // Initialize the memory subsystem. If enabled this turns on paging
            MemoryManager.Initialize();

            // Note for Monitoring early boot process:
            // if you ever want to monitor stuff before this point, you should
            // allocate a static memory area in BootInit.cs, init the
            // monitoring system earlier, hold the system at this point here,
            // copy over all the collected data up to now to the new
            // dynamically created buffer and continue
            Monitoring.Initialize();  // uses page memory
            ARM_PROGRESS("Kernel!003");
            HandleTable.Initialize();
        }

        private static void InitGCSupport()
        {
            ARM_PROGRESS("Kernel!004");
            // Initialize the rest of the primitive runtime.
            VTable.Initialize((RuntimeType)typeof(Kernel));
            ARM_PROGRESS("Kernel!005");
            // Must occur before MemoryManager.PostGCInitialize()
            ProtectionDomain.Initialize();
            ARM_PROGRESS("Kernel!006");
            // Must occur before SharedHeap.Initialize()
            MemoryManager.PostGCInitialize();
            ARM_PROGRESS("Kernel!007");
            // Allocates callback objects for stack growth
            Stacks.Initialize();
            ARM_PROGRESS("Kernel!008");
            // Initialize the HAL parts which require GC allocation
            Platform.ThePlatform.InitializeServices();
            ARM_PROGRESS("Kernel!009");
            SharedHeap.Initialize();
            ARM_PROGRESS("Kernel!010");
            // Must occur after SharedHeap.Initialize();
            ProtectionDomain.DefaultDomain.InitHook();
        }

        private static void InitServices()
        {
            InitGCSupport();
            args = GetCommandLine();
            VTable.ParseArgs(args);

            ARM_PROGRESS("Kernel!011");
            InitSchedulerTypes();

            ARM_PROGRESS("Kernel!018");
            Controller.InitializeSystem();
            Tracing.InitializeSystem();

            ARM_PROGRESS("Kernel!019");
            //  Read the profiler settings. The values are assumed in kbytes
            //  convert them to bytes for direct consumption
            ProfilerBufferSize = (uint)GetIntegerArgument("profiler", 0);
            ProfilerBufferSize *= 1024;

            ARM_PROGRESS("Kernel!020");

            SpinLock.StaticInitialize();

            int cpusLength;
            int cpuCount = GetCpuCount(out cpusLength);

            Processor.InitializeProcessorTable(cpusLength);
            ARM_PROGRESS("Kernel!021");
            Tracing.Log(Tracing.Audit, "processor");
            Processor processor = Processor.EnableProcessor(0);

            PEImage.Initialize();
            ARM_PROGRESS("Kernel!034");

            //  Initialize the sample profiling for the processor
            //  after the initial breakpoint in kd in the call
            //  PEImage.Initialize(). This will allow enabling profiling
            //  from kd, by overwriting the ProfilerBufferSize value
            processor.EnableProfiling();
            ARM_PROGRESS("Kernel!035");
            FlatPages.InitializeMemoryMonitoring();

            // initialize endpoints
            InitType(typeof(Microsoft.Singularity.Channels.EndpointCore));

            // TODO Bug 59: Currently broken, need to review paging build.
//#if PAGING
//            Microsoft.Singularity.Channels.EndpointTrusted.StaticInitialize();
//#endif
            ARM_PROGRESS("Kernel!036");

            // get the system manifest
            IoMemory systemManifest = GetSystemManifest();
            ARM_PROGRESS("Kernel!037");
            XmlReader xmlReader = new XmlReader(systemManifest);
            XmlNode xmlData = xmlReader.Parse();
            XmlNode manifestRoot = xmlData.GetChild("system");
            XmlNode initConfig = manifestRoot.GetChild("initConfig");
            ARM_PROGRESS("Kernel!038");

            PerfCounters.Initialize();
            // need to have processed the manifest before we can call Process initialize
            ARM_PROGRESS("Kernel!039");
            PrincipalImpl.Initialize(initConfig);

            ARM_PROGRESS("Kernel!040");
            Process.Initialize(manifestRoot.GetChild("processConfig"));

            InitIO(processor, initConfig, manifestRoot.GetChild("drivers"));

            InitBootTime();

            ARM_PROGRESS("Kernel!045");
            // From here on, we want lazy type initialization to worry about
            // competing threads.
            VTable.InitializeForMultipleThread();

            ARM_PROGRESS("Kernel!046");
            Console.WriteLine("Running C# Kernel of {0}", GetLinkDate());
            Console.WriteLine();

            // TODO: remove this
            Console.WriteLine("Current time: {0}", SystemClock.GetUtcTime().ToString("r"));
            ARM_PROGRESS("Kernel!047");

            InitScheduling();

            DirectoryService.StartNotificationThread();

            Console.WriteLine("Initializing Shared Heap Walker");
            ProtectionDomain.InitializeSharedHeapWalker();
            ARM_PROGRESS("Kernel!050");

            Console.WriteLine("Initializing Service Thread");
            ServiceThread.Initialize();
            ARM_PROGRESS("Kernel!051");

            GC.EnableHeap();
            GCProfilerLogger.StartProfiling();
            ARM_PROGRESS("Kernel!052");

            Tracing.Log(Tracing.Audit, "Waypoints init");
            Waypoints = new long[2048];
            WaypointSeq = new int[2048];
            WaypointThd = new int[2048];

            Tracing.Log(Tracing.Audit, "Interrupts ON.");
            Processor.RestoreInterrupts(true);
            ARM_PROGRESS("Kernel!053");

#if ISA_ARM && TEST_GC
            for (int i = 0; i < 1000; i++) {
                DebugStub.WriteLine("Iteration {0}", __arglist(i));
                ArrayList a = new ArrayList();
                for (int j = 0; j < 128; j++) {
                    int size = 1024 * 1024;
                    a.Add(new byte [size]);
                }
            }
#endif // ISA_ARM

            ARM_PROGRESS("Kernel!054");

            Tracing.Log(Tracing.Audit, "Binder");
            Binder.Initialize(manifestRoot.GetChild("namingConventions"));

#if ISA_ARM
            DebugStub.WriteLine("Exporting local namespace to BSP\n");
            DirectoryService.ExportArmNamespace();
            DebugStub.WriteLine("Export complete...redirecting binder\n");
            Binder.RedirectRootRef();
            DebugStub.WriteLine("Binder redirect complete\n");
#endif

#if false
            Tracing.Log(Tracing.Audit, "Starting Security Service channels");
            PrincipalImpl.Export();
            ARM_PROGRESS("Kernel!055");
#endif
            Tracing.Log(Tracing.Audit, "Creating Root Directory.");

            //This can be moved below
            IoSystem.InitializeDirectoryService();
            ARM_PROGRESS("Kernel!055");

#if false
            // Start User space namespace manager
            Console.WriteLine("Starting Directory Service SIP");
            DirectoryService.StartUserSpaceDirectoryService();
#endif
            ARM_PROGRESS("Kernel!055.5");

#if !ISA_ARM
            Tracing.Log(Tracing.Audit, "Starting Security Service channels");
            PrincipalImpl.Export();
#endif

            ARM_PROGRESS("Kernel!056");

            Console.WriteLine("Initializing system channels");

            // starting channels services
            DebugStub.Print("Initializing Channel Services\n");
            ChannelDeliveryImplService.Initialize();

            ARM_PROGRESS("Kernel!057");
            ConsoleOutput.Initialize();

            ARM_PROGRESS("Kernel!058");

            // Initialize MP after Binder and ConsoleOutput
            // are initialized so there are no
            // initialization races if the additional
            // threads try to use them.
            Tracing.Log(Tracing.Audit, "Starting additional processors");

            // For ABI to ARM support
            MpExecution.Initialize();
            ARM_PROGRESS("Kernel!059");

            mpEndEvent = new ManualResetEvent(false);

            Tracing.Log(Tracing.Audit, "Initializing Volume Manager.");

#if !ISA_ARM
            IoSystem.InitializeVolumeManager();
#endif // ISA_ARM
            ARM_PROGRESS("Kernel!060");

            InitDrivers();

            if (cpuCount > 1) {
                unsafe {
                    Console.WriteLine("Enabling {0} cpus out of {1} real cpus\n", cpuCount, Platform.ThePlatform.CpuRealCount);
                }
                Processor.EnableMoreProcessors(cpuCount);
                ARM_PROGRESS("Kernel!064");
            }

            Tracing.Log(Tracing.Audit, "Initializing Service Manager.");
            IoSystem.InitializeServiceManager(manifestRoot.GetChild("serviceConfig"));
            ARM_PROGRESS("Kernel!065");

            InitDiagnostics();

#if !ISA_ARM
            // At this point consider kernel finshed booting
            hasBooted = true;
#endif // ISA_ARM

            Processor.StartSampling();
            ARM_PROGRESS("Kernel!069");

            Microsoft.Singularity.KernelDebugger.KdFilesNamespace.StartNamespaceThread();
            ARM_PROGRESS("Kernel!070");

        }

        private static void InitSchedulerTypes()
        {
            InitType(typeof(Processor));
            InitType(typeof(Scheduler));
            InitType(typeof(ProcessorDispatcher));
            // InitType(typeof(AffinityScheduler));
            InitType(typeof(MinScheduler));

            ARM_PROGRESS("Kernel!013");
            // Create scheduler before initializing processes
            scheduler = new MinScheduler();

            ARM_PROGRESS("Kernel!017");
            // Initialize processor dispatcher
            ProcessorDispatcher.StaticInitialize(scheduler);
        }

        private static void InitScheduling()
        {
            Console.WriteLine("Initializing Scheduler");

            ARM_PROGRESS("Kernel!047");
            // Finish scheduler initialization:
            scheduler.Initialize();
            ARM_PROGRESS("Kernel!048");

            // Initialize initial dispatcher
            Processor.InitializeDispatcher(0);
            Processor.ActivateTimer(0);
            ARM_PROGRESS("Kernel!049");
        }

        private static void InitIO(Processor p, XmlNode initConfig, XmlNode driverConfig)
        {
            // obtain the configuration for the namespace service
            // and initialize the namespace service
            ARM_PROGRESS("Kernel!041");
            DirectoryService.Initialize(initConfig);

            Tracing.Log(Tracing.Audit, "IoSystem");
            ARM_PROGRESS("Kernel!042");
            IoSystem.Initialize(driverConfig);

            Tracing.Log(Tracing.Audit, "Registering HAL Drivers.");

            ARM_PROGRESS("Kernel!043");

            Devices.RegisterPnpResources(); // add the root devices

            ARM_PROGRESS("Kernel!044");

            Platform.InitializeHal(p);
        }

        private static int SpawnAndWaitForShell()
        {

#if ISA_ARM
            // spin here for now
            while (true) {
                Thread.Yield();
            }
#else

            Tracing.Log(Tracing.Audit, "Creating Shell Process");
            ARM_PROGRESS("Kernel!071");
            int exit = -10000;
            Manifest manifest;
#if KERNEL_USE_LOGIN
            IoMemory memory;
            if (args[0] == "bvt") {
                memory = Binder.LoadImage(Thread.CurrentProcess, "tty", out manifest);
            }
            else{
                // TODO: The login app needs to be fixed to setup stdin and stdout pipes for
                // the shell and pump the data back and forth.
                memory = Binder.LoadImage(Thread.CurrentProcess, "login", out manifest);
            }
#else
            IoMemory memory = Binder.LoadImage(Thread.CurrentProcess, "tty", out manifest);
#endif
            ARM_PROGRESS("Kernel!073");

            if (memory == null || memory.Length > 0) {
                String[] shellArgs = new String[args.Length + 2];
                shellArgs[0] = "tty";
                shellArgs[1] = "shell";
                for (int i = 0; i < args.Length; i++) {
                    shellArgs[i + 2] = args[i];
                }
                Process process = new Process(Thread.CurrentProcess, memory, null, shellArgs, manifest);
                if (process != null) {
                    PrintBootTime();
                    process.Start();
                    process.Join();
                    exit = process.ExitCode;
                }

                ARM_PROGRESS("Kernel!074");
            }
            return DetermineShutdown(exit);
#endif
        }

        private static int DetermineShutdown(int exit)
        {
            switch (exit) {
                case -10000:
                    Tracing.Log(Tracing.Audit, "Failed to start shell process.");
                    return Platform.EXIT_AND_RESTART;
                case Platform.EXIT_AND_WARMBOOT:
                case Platform.EXIT_AND_RESTART:
                case Platform.EXIT_AND_SHUTDOWN:
                    return exit;
                default:
                    DebugStub.WriteLine("Shell process terminated improperly (0x{0:x4})",
                                        __arglist(exit));
                    Tracing.Log(Tracing.Audit, "Shell process terminated improperly");
                    DebugStub.Break();
                    return Platform.EXIT_AND_SHUTDOWN;
            }
        }

        private static void InitBootTime()
        {
            if (Platform.ThePlatform.BootYear != 0) {
                BootTime = new DateTime((int)Platform.ThePlatform.BootYear,
                                        (int)Platform.ThePlatform.BootMonth,
                                        (int)Platform.ThePlatform.BootDay,
                                        (int)Platform.ThePlatform.BootHour,
                                        (int)Platform.ThePlatform.BootMinute,
                                        (int)Platform.ThePlatform.BootSecond,
                                        0);
                //  There is no time zone support in Singularity, the clock assumes GMT
                //  but the CMOS reports it in local time. Hardcode the correction here for now
                BootTime = BootTime.AddHours(8);
            }
            else {
                //  Other HALs do not capture the load time. Make the best effort to
                //  capture now, after the devices are initialized.
                BootTime = DateTime.Now;
            }
        }

        private static void InitDrivers()
        {
            // Register drivers who depend on scheduling and resource management.
            DebugStub.WriteLine("--- Registering Drivers ---------------------------");
            Console.WriteLine("Registering Non-HAL Drivers.");
            // register the metadata-based drivers
            IoSystem.RegisterDrivers();
            ARM_PROGRESS("Kernel!061");

            // register the internal kernel drivers
            Devices.RegisterInternalDrivers();
            ARM_PROGRESS("Kernel!062");
#if DEBUG
            // and output the results
            IoSystem.Dump(false);
#endif
            DebugStub.WriteLine("--- Activating Devices ----------------------------");
            // now do device initialization
            IoSystem.ActivateDrivers();
            ARM_PROGRESS("Kernel!063");
#if DEBUG
            // and output the results
            // IoSystem.Dump(true);
#endif
        }

        private static void InitDiagnostics()
        {
            // Start up the kernel's diagnostics module
            Console.WriteLine("Starting diagnostics module...");
            Diagnostics.DiagnosticsModule.Initialize();
            ARM_PROGRESS("Kernel!066");
            // Start up the kernel's stress test module
            Console.WriteLine("Initializing stress module...");
            Stress.StressService.Initialize();
            ARM_PROGRESS("Kernel!067");
        }

        private static IoMemory GetSystemManifest()
        {
            IoMemory res = Binder.GetSystemManifest();
            if (res == null) {
                DebugStub.WriteLine("Failed to load system manifest.");
                DebugStub.Break();
                throw new Exception("The system manifest could not be loaded.");
            }
            return res;
        }

        private static void FinalizeServices()
        {
            ARM_PROGRESS("Kernel!075");
            Tracing.Log(Tracing.Audit, "Shutting down AP processors");
            Processor.StopApProcessors();

            Tracing.Log(Tracing.Audit, "Shutting down I/O system");
            Console.WriteLine("Shutting down I/O system");
            IoSystem.Finalize();

            Tracing.Log(Tracing.Audit, "Interrupts OFF.");
            Processor.DisableInterrupts();

            Tracing.Log(Tracing.Audit, "Shutting down scheduler");
            Console.WriteLine("Shutting down scheduler");
            for (int i = 0; i < Processor.processorTable.Length; i++) {
                Processor p = Processor.processorTable[i];
                if (p != null) {
                    Console.WriteLine("  cpu {0}: {1} context switches, {2} interrupts", i, p.NumContextSwitches, p.NumInterrupts);
                }
            }

            // Finalize the scheduler
            scheduler.Finalize();

            // We should turn off interrupts here!
            Platform.ReleaseResources();
            PEImage.Finalize();

            DebugStub.WriteLine("Kernel Exiting [{0}]",
                                __arglist(bootReturnCode));
        }

        private static void FinalizePreMonitoring()
        {
            Stacks.Finalize();
            HandleTable.Finalize();
            SharedHeap.Finalize();
            MemoryManager.Finalize();
        }

        private static int GetCpuCount(out int cpusLength)
        {
            int cpuReal = Platform.ThePlatform.CpuRealCount;
            int cpuLimit = Platform.ThePlatform.CpuMaxCount;
            DebugStub.Assert(cpuReal <= cpuLimit);

            // See if the command line argument limits our processor count
            int cpuCount = GetIntegerArgument("mp", cpuReal);
            cpusLength = cpuReal;

#if !SINGULARITY_MP
            if (cpuCount > 1) {
                Console.WriteLine("Limiting processors to 1 due to SP build");
                cpuCount = 1;
            }
#endif
            return cpuCount;
        }

        // Note: This function is entry point to the managed
        // kernel for CPU's other than the bootstrap processor.
        // It is called from the Hal or Hal.
        [AccessedByRuntime("referenced from hal.cpp")]
        internal static int MpMain(int cpu)
        {
            Tracing.Log(Tracing.Audit, "processor");
            Processor processor = Processor.EnableProcessor(cpu);

            // Initialize dispatcher
            Processor.InitializeDispatcher(cpu);

            // Initialize the HAL processor services
            // Note that this must occur after EnableProcessor, as the kernel
            // thread does not get bound until then. (It gets bound much
            // earlier in the boot processor case -- need to decide if this difference is
            // really appropriate.)
            Platform.Cpu(cpu).InitializeServices();

            Platform.InitializeHal(processor);

            Thread.CurrentThread.Affinity = cpu;

            Processor.ActivateTimer(cpu);

#if DEBUG_SYSTEM_LOCKUP
            // Spin one CPU on debugger. For instance with a quad-proc
            // box, spin CPU 3.
            while (cpu == 3) {
                if (DebugStub.PollForBreak() == true) {
                    DebugStub.Break();
                }
            }
#endif // DEBUG_SYSTEM_LOCKUP

            Processor.RestoreInterrupts(true);

            Tracing.Log(Tracing.Audit,
                        "Looping in processor's kernel thread.");
            //while (cpu > 0) {
            //    Thread.Yield();
            //}

            // This probably won't be the
            // ultimate way of dissociating kernel entry threads
            // from the kernel.
            DebugStub.Print("AP Processor started, about to wait\n");
            mpEndEvent.WaitOne();

            return 0;
        }

        // This function is called by the GC to locate all non-static object
        // references allocated somewhere other than the stack.
        internal static
        void VisitSpecialData(System.GCs.DirectReferenceVisitor visitor)
        {
            Platform.ThePlatform.VisitSpecialData(visitor);
            Process.VisitSpecialData(visitor);
            visitor.VisitReferenceFields(Processor.processorTable);
        }

        // This function is called by GCs that move object to update all
        // object references contained in non-objects (i.e. unsafe structs).
        internal static void UpdateAfterGC(Thread currentThread)
        {
            Processor.UpdateAfterGC(currentThread);
        }

        [AccessedByRuntime("defined in HAL.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(256)]
        [NoHeapAllocation]
        private static unsafe extern char * HalGetLinkDate();

        internal static unsafe string GetLinkDate()
        {
            return new String(HalGetLinkDate());
        }

        internal static unsafe string[] GetCommandLine()
        {
            String[] args =
                (new String((char *)(Platform.ThePlatform.CommandLine),
                            0, Platform.ThePlatform.CommandLineCount)).Split(null);
            int dst = 0;
            for (int src = 0; src < args.Length; src++) {
                if (args[src] != null && args[src].Length > 0) {
                    args[dst++] = args[src];
                }
            }
            if (dst < args.Length) {
                String[] list = new String[dst];
                for (int i = 0; i < dst; i++) {
                    list[i] = args[i];
                }
                return list;
            }
            return args;
        }

        // kind the argument "key" and extract the string value following a colon.
        internal static string
        GetStringArgument(string key, string defaultValue)
        {
            key = key + ":";
            for (int i = 0; i < args.Length; i++) {
                string arg = args[i];
                if ((arg.StartsWith("-") || arg.StartsWith("/")) &&
                    0 == String.Compare(arg, 1, key, 0, key.Length, true)) {
                    string result = arg.Substring(key.Length+1);
                    string[] newargs = new string[args.Length - 1];
                    Array.Copy(args, 0, newargs, 0, i);
                    Array.Copy(args, i + 1, newargs, i, args.Length - i - 1);
                    args = newargs;
                    return result;
                }
            }
            return defaultValue;
        }

        internal static int GetIntegerArgument(string key, int defaultValue)
        {
            key = key + ":";
            for (int i = 0; i < args.Length; i++) {
                string arg = args[i];
                if ((arg.StartsWith("-") || arg.StartsWith("/")) &&
                    0 == String.Compare(arg, 1, key, 0, key.Length, true)) {
                    string result = arg.Substring(key.Length+1);
                    string[] newargs = new string[args.Length - 1];
                    Array.Copy(args, 0, newargs, 0, i);
                    Array.Copy(args, i + 1, newargs, i, args.Length - i - 1);
                    args = newargs;
                    // TODO this should be try-parse
                    return Int32.Parse(result);
                }
            }
            return defaultValue;
        }

        [NoHeapAllocation]
        public static void RequestWarmBoot()
        {
            bootReturnCode = Platform.EXIT_AND_WARMBOOT;
        }

        [NoHeapAllocation]
        public static void RequestRestart()
        {
            bootReturnCode = Platform.EXIT_AND_RESTART;
        }

        [NoHeapAllocation]
        public static void RequestShutdown()
        {
            bootReturnCode = Platform.EXIT_AND_SHUTDOWN;
        }

        private static void Kill(int exitCode)
        {
            Platform.ThePlatform.Kill(exitCode);
        }

        internal static void Shutdown(int exitCode)
        {
            unchecked {
                Tracing.Log(Tracing.Audit, "Kernel.Shutdown({0})", (UIntPtr)(uint)exitCode);
            }
            DebugStub.WriteLine("Kernel.Shutdown(0x{0:x4})",
                                __arglist(exitCode));
            DebugStub.Break();
            VTable.Shutdown(exitCode);
        }

        // Rationale for cutting the fact that no stack probes are permitted in this
        // tree of calls:
        //
        // * We are already hosed.
        // * Without this cut, places that cannot (transitively) tolerate stack link extensions
        // * cannot call Panic.
        [NoStackLinkCheckTransCut][IgnoreLockRank]
        internal static void Panic(string why)
        {
            DebugStub.WriteLine("KERNEL PANIC: {0}", __arglist(why));
            Shutdown(Platform.EXIT_AND_HALT);
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

        [NoHeapAllocation]
        public static UIntPtr AddressOf(ITracked tracked)
        {
            return Magic.addressOf(tracked);
        }

        [NoHeapAllocation]
        unsafe public static UIntPtr AddressOf(void * ptr)
        {
            return (UIntPtr)ptr;
        }

        public static void InitType(Type ty)
        {
            VTable.initType((RuntimeType) ty);
        }

        [NoHeapAllocation]
        public static string TypeName(Object o)
        {
            if (o == null) {
                return "null";
            }
            else {
                Type t = o.GetType();
                RuntimeType r = (RuntimeType)t;
                return r.Name;
            }
        }

        [NoHeapAllocation]
        public static string TypeNameSpace(Object o)
        {
            if (o == null) {
                return "null";
            }
            else {
                Type t = o.GetType();
                RuntimeType r = (RuntimeType)t;
                return r.Namespace;
            }
        }

        public static string FullTypeName(Object o)
        {
            if (o == null) {
                return "null";
            }
            else {
                Type t = o.GetType();
                RuntimeType r = (RuntimeType)t;
                return r.Namespace + "." + r.Name;
            }
        }

        public static void DumpPageTable()
        {
            System.GCs.PageTable.Dump("PageTable");
        }

        internal static void PrintBootTime()
        {
            // Console.WriteLine("Current time: {0}", SystemClock.GetUtcTime().ToString("r"));
            // Console.WriteLine("Boot time: {0}", BootTime.ToString("r"));

            TimeSpan delta = SystemClock.GetUtcTime() - BootTime;
            DebugStub.WriteLine("Elapsed boot time = {0} msec.", __arglist(delta.TotalMilliseconds));
        }
    }
}
