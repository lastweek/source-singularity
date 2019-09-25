////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Process.cs
//
//  Note:
//

// #define TEST_CREATE_PROCESS_TIME
// #define VERBOSE
// #define APPLY_TPM

using System;
using System.Collections;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;

using Microsoft.Singularity;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Xml;
using Microsoft.Singularity.Loader;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Scheduling;

using Microsoft.Singularity.V1.Threads;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Security;
using Microsoft.Singularity.Eventing;

namespace Microsoft.Singularity
{
    [CLSCompliant(false)]
    public enum ProcessEvent : ushort
    {
        CreateKernelProcess = 1,
        CreateUserProcess = 2,
        ImageLoad = 3,
    }

    //
    //  Per-SIP privileges. They are available only to the kernel side of the process
    //  They cannot also be altered by the SIP, assumming strong guarantees about mnemory
    //  safety.
    //

    [CLSCompliant(false)]
    public class ProcessPrivileges
    {
        //
        //  Default privileges for processes which do not override them from a
        //  trusted component base.
        //

        public static ProcessPrivileges DefaultPrivileges = new ProcessPrivileges(Operations.None);

        [Flags]
        public enum Operations
        {
            None = 0,

            // This privilege is checked for operations such as enabling / disabling
            // interrupts and querying the interrupts flag. SIP should not have this
            // privilege set by default, with the few exceptions of drivers

            DisableInterrupts = 1,
        };

        public ProcessPrivileges(Operations allowedOpperations)
        {
            AllowedOperations = allowedOpperations;
        }

        [NoHeapAllocation]
        public static ProcessPrivileges GetCurrentPrivileges()
        {
            Process process = Thread.CurrentProcess;

            // The privileges should only be checked within a valid context

            VTable.Assert(process != null);
            return process.GetPrivileges();
        }

        public readonly Operations AllowedOperations;
    }

    [NoCCtor]
    [CLSCompliant(false)]
    public class Process
    {
        // Per-Class Members:
        internal static HandleTable kernelHandles;
        public static bool systemSilentLoad;
        public static Process kernelProcess;
        public static Process idleProcess;
        public static Process[] processTable;
        private static SpinLock processTableLock;
        private static int processIndexGenerator;

        internal const int maxProcesses = 1024; // Must be power of 2 >= 64

        private static bool useSeparateAddressSpaces;

        private static ProcessGroup [] processGroups;
        // Xml processing constants
        internal const string PolicyXmlTag      = "policy";
        internal const string ProcessSetXmlTag  = "processSet";

        internal const string SeparateAddressSpaceXmlAttribute  = "separateAddressSpace";
        internal const string NameXmlAttribute                  = "name";
        internal const string SetXmlAttribute                   = "set";
        internal const string KernelDomainXmlAttribute          = "kernelDomain";

        public enum  ParameterCode {
            Success,
            OutOfRange,
            NotSet,
            Retrieved,
            AlreadySet,
            Undefined,
        }

        // Arrays used set/get process arguments

        private class BoolArg {
            public bool Value;
            public bool Set;
            public bool Retrieved;

            public BoolArg (bool value)
            {
                this.Value      = value;
                this.Set        = false;
                this.Retrieved  = false;
            }
        }

        private class LongArg {
            public long Value;
            public bool Set;
            public bool Retrieved;

            public LongArg (long value)
            {
                this.Value      = value;
                this.Set        = false;
                this.Retrieved  = false;
            }
        }

        private class StringArg {
            public string   Value;
            public bool     Set;
            public bool     Retrieved;

            public StringArg (string value)
            {
                this.Value      = value;
                this.Set        = false;
                this.Retrieved  = false;
            }
        }

         private class StringArrayArg
         {
            public string[] Value;
            public bool     Set;
            public bool     Retrieved;

            public StringArrayArg (string[] value)
            {
                this.Value      = value;
                this.Set        = false;
                this.Retrieved  = false;
            }
        }

       internal class ProcessGroup
        {
            public string GroupName;
            public string [] ProcessSet;
            public bool KernelDomain;
            public ProcessGroup(string name, string[] procs, bool kernelDomain)
            {
                this.GroupName = name;
                this.ProcessSet = procs;
                this.KernelDomain = kernelDomain;
            }
        }

        internal static string [] Tokenize(string str) {
            int start = 0;
            int end = str.Length;
            int count = 0;
            int at = 0;
            ArrayList tokens = new ArrayList();
            string[] retVal = null;

            if (str == null) return null;

            while ((start <= end) && (at > -1)) {
                count = end - start;
                at = str.IndexOf(' ', start, count);
                if (at == -1) {
                    tokens.Add(str.Substring(start));
                    break;
                }
                string s = str.Substring(start, at-start);
                tokens.Add(s);
                start = at+1;
            }

            retVal = new string[tokens.Count];
            for (int i = 0; i < tokens.Count; i++) {
                retVal[i] = (string) tokens[i];
            }
            return retVal;
        }

        internal static void ProcessConfig (XmlNode config)
        {
            if (config == null) {
                return;
            }

            // process address space policy

            XmlNode policy = config.GetChild(PolicyXmlTag);
            if (policy != null) {
                useSeparateAddressSpaces = policy.GetAttribute(SeparateAddressSpaceXmlAttribute, false);
            }

            int groupNodes = config.CountNamedChildren(ProcessSetXmlTag);
            if (groupNodes != 0) {
                // allocate memory for groups
                processGroups = new ProcessGroup[groupNodes];
                int idx = 0;
                foreach (XmlNode group in config.Children) {
                    if (group.Name != ProcessSetXmlTag) {
                        continue;
                    }
                    string groupName =  group.GetAttribute(NameXmlAttribute, "");
                    string appSet =  group.GetAttribute(SetXmlAttribute, "");
                    // break up appset into array of names
                    string[] procs = Tokenize(appSet);
                    bool kernelDomain = group.GetAttribute(KernelDomainXmlAttribute,false);
                    processGroups[idx] = new ProcessGroup(groupName, procs, kernelDomain);
                    idx++;
                }
            }
        }

        internal static
        void VisitSpecialData(System.GCs.DirectReferenceVisitor visitor)
        {
            visitor.VisitReferenceFields(Process.processTable);

            for (int i = 0; i < processTable.Length; i++) {
                Process process = processTable[i];
                // Conditions to check:
                //  1.  process is not null.
                //  2.  process.handles is not null (during process initialization,
                //      the process instance is added to processTable before
                //      handles is initialized).
                //  3.  process.processIndex is not -1 (during process shutdown,
                //      processIndex is set to -1 as a signal that GC shouldn't
                //      touch the pages, so the pages can be freed safely).
                if (process != null && process.handles != null && process.processIndex != -1) {
                    process.handles.VisitSpecialData(visitor);
                }
            }
        }

        internal static int AllocateProcessTableSlot(Process process)
        {
            Thread currentThread = Thread.CurrentThread;

            Kernel.Waypoint(621);
            bool saved = Processor.DisableInterrupts();
            processTableLock.Acquire(currentThread);
            int foundIndex = -1;
            try {
                for (int i = 0; i < processTable.Length; i++) {
                    int index = (processIndexGenerator + i) % processTable.Length;
                    if (processTable[index] == null) {
                        Kernel.Waypoint(622);
                        foundIndex = index;
                        processTable[foundIndex] = process;
                        processIndexGenerator = (index + 1) % processTable.Length;
                        break;
                    }
                }
            }
            finally {
                processTableLock.Release(currentThread);
                Processor.RestoreInterrupts(saved);
            }
            Kernel.Waypoint(623);

            DebugStub.Assert(foundIndex >= 0, "Out of thread slots!");
            return foundIndex;
        }

        internal static void Initialize(XmlNode config)
        {
            // Create pre-existent processes.
            kernelProcess = new Process(1);
            idleProcess = new Process(2);

            // Initialize process management table.
            processTableLock = new SpinLock(SpinLock.Types.ProcessTable);
            processTable = new Process[maxProcesses];
            processTable[0] = kernelProcess;    // ensure slot zero is never used
            processTable[1] = kernelProcess;    // 1 is the kernel process.
            processTable[2] = idleProcess;      // 2 is the idle process.
            processIndexGenerator = 3;

            // Create table told hold kernel handles.
            kernelHandles = new HandleTable(null);

            Thread.initialThread.process = kernelProcess;

            //policy config data
            ProcessConfig(config);
        }

        // The next 2 functions are used by the loader to determine
        // what address space SIPs should be created in

        public static bool  RunInSeparateSpace()
        {
            return useSeparateAddressSpaces;
        }

        public static string GetGroupFromName(string name, out bool isKernelDomain)
        {
            isKernelDomain = false;
            if (processGroups == null) return null;
            for (int i = 0; i < processGroups.Length; i++) {
                for (int j = 0; j < processGroups[i].ProcessSet.Length; j++) {
                    if (processGroups[i].ProcessSet[j] == name) {
                        isKernelDomain = processGroups[i].KernelDomain;
                        return processGroups[i].GroupName;
                    }
                }
            }
            return null;
        }

        [NoHeapAllocation]
        public static Process GetProcessByID(int procID)
        {
            return processTable[procID];
        }

        // Per-Instance Members:
        private ProcessState state; // acquire processMutex before modifying
        private bool wasStarted; // were we ever in the Running state?
        private Mutex suspendMutex; // lock ordering: if you acquire both suspendMutex and processMutex, acquire suspendMutex first
        private Mutex processMutex; // lock ordering: acquire child lock before acquiring parent lock
        private int processIndex;
        private uint processTag;
        private Process parent;
        private IoConfig ioconfig;
        private Process[] children;
        private Thread[] threads;
        private int startedChildCount;
        private int startedThreadCount;
        private HandleTable handles;
        private ManualResetEvent joinEvent;
        private int exitCode;
        private bool silentLoad;
        private UIntPtr pagesNow;
        private UIntPtr pagesMax;
#if false
        private ThreadScheduleData defaultScheduleData;
#endif

        private PEImage image;
        private IoMemory loadedImage;
        private ProcessStart entry;
        private String imageName;
        private String[] args;

        private long deadThreadCount;
        private TimeSpan deadThreadExecutionTime;
        private int gcCount;
        private TimeSpan gcTotalTime;
        private long gcTotalBytes;

        private unsafe SharedHeap.Allocation * [] endpointSet;
        private BoolArg[]               boolArgSet;
        private StringArg[]             stringArgSet;
        private LongArg[]               longArgSet;
        private StringArrayArg[]        stringArrayArgSet;

        private ProtectionDomain protectionDomain;
        private ProcessPrivileges privileges = null;

        // The principal of the process
        private Principal principal;

        /// <summary>
        /// Get the process's current privileges
        /// </summary>
        [NoHeapAllocation]
        public ProcessPrivileges GetPrivileges()
        {
            if (privileges != null) {
                return privileges;
            } else {
                return ProcessPrivileges.DefaultPrivileges;
            }
        }

        [NoHeapAllocation]
        public void SetPrivileges(ProcessPrivileges newPrivileges)
        {
            privileges = newPrivileges;
        }

        /// <summary>
        /// Get the parent process
        /// </summary>
        public Process Parent
        {
            get { return parent; }
        }

#if false
        internal ThreadScheduleData DefaultScheduleData
        {
            [Inline]
            [NoHeapAllocation]
            get
            {
                return defaultScheduleData;
            }
        }
#endif

        private Process(int index)
        {
            this.state = ProcessState.Unstarted;
            this.suspendMutex = new Mutex();
            this.processMutex = new Mutex();
            this.processIndex = index;
            this.processTag = ((uint)processIndex) << 16;
            this.children = new Process[16];
            this.threads = new Thread[16];
            this.handles = new HandleTable(this);
            this.parent = null;

            this.joinEvent = new ManualResetEvent(false);
            this.imageName = index == 1 ? "kernel" : "idle";
            this.deadThreadCount = 0;
            this.deadThreadExecutionTime = new TimeSpan(0);
            this.gcCount = 0;
            this.gcTotalTime = TimeSpan.Zero;
            this.gcTotalBytes = 0;

            //DebugStub.WriteLine("new process(index): clearing StringArray");
            this.stringArrayArgSet = null;
            this.protectionDomain = ProtectionDomain.DefaultDomain;
            protectionDomain.AddRef();
#if VERBOSE
            DebugStub.WriteLine("Loaded process \"{0}\" into {1}protection domain \"{2}\"",
                                __arglist(this.imageName,
                                          this.protectionDomain.KernelMode ? "kernel " : "",
                                          this.protectionDomain.Name));
#endif

            // This constructor is currently used only to create the
            // process for the kernel. If this changes, the code below should
            // change as well. In general, use the other constructor, as it
            // provides sufficient information to create the process principal.
            this.principal = PrincipalImpl.Self();
            Monitoring.Log(Monitoring.Provider.Process,
                           (ushort)ProcessEvent.CreateKernelProcess,
                           GetProcessName());
        }

        private Process(Process parent)
        {
            Kernel.Waypoint(620);
            this.processIndex = AllocateProcessTableSlot(this);
#if false
            this.defaultScheduleData = parent.defaultScheduleData;
#endif
            Kernel.Waypoint(625);
            this.state = ProcessState.Unstarted;
            this.suspendMutex = new Mutex();
            this.processMutex = new Mutex();
            this.processTag = ((uint)processIndex) << 16;
            this.children = new Process[16];
            this.threads = new Thread[16];
            this.handles = new HandleTable(this);
            this.parent = parent;
            this.imageName = parent.imageName;
            this.ioconfig = parent.ioconfig;    // replicate IoConfig to children.
            Kernel.Waypoint(626);

            this.joinEvent = new ManualResetEvent(false);
            //DebugStub.WriteLine("clearing StringArray");
            this.stringArrayArgSet = null;

            parent.AddChild(this);

            Monitoring.Log(Monitoring.Provider.Process,
                           (ushort)ProcessEvent.CreateUserProcess, 0,
                           (uint)this.ProcessId, (uint)parent.ProcessId,
                           0, 0, 0);
       }

        public Process(Process parent,
                       IoMemory rawImage,
                       String role,
                       String[] args,
                       Manifest appManifest)
            : this(parent)
        {
            this.imageName = appManifest.Name;
            this.args = args;

#if PAGING
            if (RunInSeparateSpace()) {
                bool kernelMode;
                string domainName = GetGroupFromName(this.imageName, out kernelMode);

                if (domainName != null) {
                    this.protectionDomain = ProtectionDomain.FindOrCreateByName(domainName, kernelMode);
                }
            }
#endif

            if (this.protectionDomain == null) {
                // Just inherit from our parent
                this.protectionDomain = parent.protectionDomain;
            }

            protectionDomain.AddRef();
#if PAGING
            try {
                // Temporarily switch to the domain of the process
                // we are creating
                Thread.SwitchToDomain(this.protectionDomain);
                this.protectionDomain.InitHook(); // we might be first
#endif

                Kernel.Waypoint(510);

                // this is a normal load (for BSP), so
                // set the 4th argument (isForMp) to false
                this.image = PEImage.Load(this, rawImage, out loadedImage,
                                          false);

                Monitoring.Log(Monitoring.Provider.Process,
                               (ushort)ProcessEvent.ImageLoad,
                               imageName);

                Kernel.Waypoint(511);

                // Trap-door to turn off debugger notification for micro-benchmark.
                if (args.Length > 0) {
                    if (args[args.Length-1] == "!") {
                        silentLoad = true;
                    }
                    else if (args[args.Length-1] == "!+") {
                        DebugStub.WriteLine();
                        DebugStub.WriteLine("*** Disabled debugger load notifications. Type \".reload\" to retrieve full symbols.");
                        DebugStub.WriteLine();
                        systemSilentLoad = true;
                    }
                    else if (args[args.Length-1] == "!-") {
                        DebugStub.WriteLine();
                        DebugStub.WriteLine("*** Enabled debugger load notifications.");
                        DebugStub.WriteLine();
                        systemSilentLoad = false;
                    }
                }
                if (!silentLoad && systemSilentLoad) {
                    silentLoad = true;
                }

#if DEBUG
                DebugStub.WriteLine(
                    "Loading {0} [{1:x}...{2:x} bytes]",
                    __arglist(imageName,
                              loadedImage.VirtualAddress,
                              loadedImage.VirtualAddress + loadedImage.Length));
#endif
                DebugStub.WriteLine(
                    "Loaded process \"{0}\" into {1}protection domain \"{2}\"",
                    __arglist(this.imageName,
                              this.protectionDomain.KernelMode ? "kernel " : "",
                              this.protectionDomain.Name));

                DebugStub.LoadedBinary(loadedImage.VirtualAddress,
                                       (UIntPtr) loadedImage.Length,
                                       imageName,
                                       image.checkSum,
                                       image.timeDateStamp,
                                       silentLoad);

                Kernel.Waypoint(512);
                threads[0] = Thread.CreateThread(this, new ThreadStart(this.PeStart));
                Kernel.Waypoint(513);
#if PAGING
            }
            finally {
                Thread.RevertToParentDomain();
            }
#endif

            // create the principal of the process
#if APPLY_TPM
            this.principal = PrincipalImpl.NewInvocation(parent.Principal, appManifest, role, rawImage);
#else
            this.principal = PrincipalImpl.NewInvocation(parent.Principal, appManifest, role, null);
#endif

            Tracing.Log(Tracing.Audit, "Created PE process at {0:x8}",
                        loadedImage.VirtualAddress);

        }

        public static Process KernelProcess
        {
            [NoHeapAllocation]
            get { return kernelProcess; }
        }

        public int ProcessId
        {
            [NoHeapAllocation]
            get { return processIndex; }
        }

        public Principal Principal
        {
            [NoHeapAllocation]
            get { return this.principal; }
        }

        public uint ProcessTag
        {
            [NoHeapAllocation]
            get { return processTag; }
        }

        public IoConfig IoConfig
        {
            [NoHeapAllocation]
            get { return ioconfig; }
            [NoHeapAllocation]
            set { ioconfig = value; }
        }

        public SharedHeap ProcessSharedHeap
        {
            [Inline]
#if PAGING
            get { return protectionDomain.UserSharedHeap; }
#else
            // Everyone uses the same heap
            get { return SharedHeap.KernelSharedHeap; }
#endif
        }

        public ProtectionDomain Domain
        {
            get {
                return protectionDomain;
            }
        }

#if PAGING
        public bool RunsAtKernelPrivilege {
            get {
                return protectionDomain.KernelMode;
            }
        }
#else
        public bool RunsAtKernelPrivilege {
            get {
                // All processes run at ring-0 on
                // the non-PAGING build
                return true;
            }
        }
#endif

        // Routines to maintain child process list.
        //

        // Called when a child process object is allocated (not called when
        // a child Process starts).
        private void AddChild(Process child)
        {
            Kernel.Waypoint(514);
            processMutex.AcquireMutex();
            try {
                for (int i = 0; i < children.Length; i++) {
                    if (children[i] == null) {
                        children[i] = child;
                        return;
                    }
                }

                // Grow array if necessary
                Process[] nc = new Process[children.Length * 2];
                for (int i = 0; i < children.Length; i++) {
                    nc[i] = children[i];
                }
                nc[children.Length] = child;
                children = nc;
            }
            finally {
                processMutex.ReleaseMutex();
            }
        }

        // Should only be called from the kernel service thread.
        private bool ServiceRemoveChild(Process child)
        {
            Kernel.Waypoint(515);
            processMutex.AcquireMutex();
            try {
                for (int i = 0; i < children.Length; i++) {
                    if (children[i] == child) {
                        children[i] = null;
                        if (child.wasStarted) {
                            startedChildCount--;
                        }
                        return true;
                    }
                }
            }
            finally {
                processMutex.ReleaseMutex();
            }
            return false;
        }

        // Routines to maintain child thread list.
        //

        // Called when a thread is created (not when a thread
        // is started)
        internal void AddThread(Thread thread, bool needThreadHandle)
        {
            Kernel.Waypoint(516);
            processMutex.AcquireMutex();
            try {
                VTable.Assert(thread.threadHandle.id == UIntPtr.Zero);
                if (needThreadHandle) {
                    thread.threadHandle = new ThreadHandle(AllocateHandle(thread));
                }

                for (int i = 0; i < threads.Length; i++) {
                    if (threads[i] == null) {
                        threads[i] = thread;
                        return;
                    }
                }

                // Grow array if necessary
                Thread[] nc = new Thread[threads.Length * 2];
                for (int i = 0; i < threads.Length; i++) {
                    nc[i] = threads[i];
                }
                nc[threads.Length] = thread;
                threads = nc;
            }
            finally {
                processMutex.ReleaseMutex();
            }
        }

        // Should be called only by the service thread
        private bool ServiceRemoveThread(Thread thread)
        {
            Kernel.Waypoint(517);
            processMutex.AcquireMutex();
            try {
                for (int i = 0; i < threads.Length; i++) {
                    if (threads[i] == thread) {
                        threads[i] = null;
                        if (thread.ThreadState !=
                            System.Threading.ThreadState.Unstarted) {
                            Interlocked.Decrement(ref startedThreadCount);
                        }
                        return true;
                    }
                }
            }
            finally {
                processMutex.ReleaseMutex();
            }
            return false;
        }

        public bool CreateThread(ThreadStart start)
        {
            Thread thread = Thread.CreateThread(this, new ThreadStart(start));
            if (thread == null) {
                Tracing.Log(Tracing.Audit, "Failed CreateThread request too late.");
                return false;
            }
            VTable.Assert(thread.threadHandle.id == UIntPtr.Zero);

            unchecked {
                Tracing.Log(Tracing.Audit, "Created new PE thread {1:x3}.",
                            (UIntPtr)unchecked((uint)thread.threadIndex));
            }
            return true;
        }

        public unsafe bool CreateThread(int threadIndex,
                                        out ThreadHandle handle,
                                        out UIntPtr threadContext)
        {
            Thread thread =
                Thread.CreateThread(this, new ThreadStart(this.PeStartThread), true);
            if (thread != null) {
                VTable.Assert(thread.threadHandle.id != UIntPtr.Zero);
                thread.processThreadIndex = threadIndex;
                handle = thread.threadHandle;
                fixed (void *contextAddr = &thread.context) {
                    threadContext = (UIntPtr) contextAddr;
                }
            }
            else {
                handle = new ThreadHandle();
                threadContext = 0;
                Tracing.Log(Tracing.Audit, "Failed CreateThread lid={0:x3}.",
                            (UIntPtr)unchecked((uint)threadIndex));
                return false;
            }

            unchecked {
                Tracing.Log(Tracing.Audit, "Created new PE thread tid={0:x3}, lid={1:x3}.",
                            (UIntPtr)unchecked((uint)thread.threadIndex),
                            (UIntPtr)unchecked((uint)threadIndex));
            }
            return true;
        }

        // Should only be called from the kernel service thread.
        private void ServiceRelease()
        {
            Kernel.Waypoint(521);

            processMutex.AcquireMutex();
            try {
                if (state == ProcessState.Stopped) {
                    return;
                }
                state = ProcessState.Stopped;
            }
            finally {
                processMutex.ReleaseMutex();
            }

            // Clear out any unstarted children and threads
            processMutex.AcquireMutex();
            Process[] childArray = children;
            Thread[] threadArray = threads;
            processMutex.ReleaseMutex();
            foreach (Process c in childArray) {
                if (c != null) {
                    VTable.Assert(c.state == ProcessState.Unstarted);
                    c.ServiceRelease();
                }
            }
            foreach (Thread t in threadArray) {
                if (t != null) {
                    VTable.Assert(t.ThreadState
                        == System.Threading.ThreadState.Unstarted);
                    t.ServiceStopped();
                }
            }

            // Remove ourself
            bool found = parent.ServiceRemoveChild(this);
            VTable.Assert(found);

            VTable.Assert(processIndex >= 0);
            Kernel.Waypoint(522);

            // Set processIndex to -1 so that we don't race with GC
            // (see VisitSpecialData)
            int cachedProcessIndex = this.processIndex;
            this.processIndex = -1;

            UIntPtr imageBytes = UIntPtr.Zero;
            UIntPtr handleBytes;
            UIntPtr pageBytes;

            // Must switch to the target process' address space
            // to free memory properly
#if PAGING
            try {
                Thread.SwitchToDomain(this.protectionDomain);
#endif
                if (loadedImage != null) {
                    imageBytes = (UIntPtr)loadedImage.Length;
                    Tracing.Log(Tracing.Debug, "UnloadingBinary at {0:x8}",
                                loadedImage.VirtualAddress);
                    Kernel.Waypoint(523);
                    DebugStub.UnloadedBinary(loadedImage.VirtualAddress, silentLoad);
                    Kernel.Waypoint(524);
                    IoMemory.Release(this, loadedImage);

                    loadedImage = null;
                    image = null;
                    entry = null;
                }

                Kernel.Waypoint(525);
                handleBytes = handles.FreeAllPages();
                Controller.GetSystemController().UnRegisterController(cachedProcessIndex);
                Kernel.Waypoint(526);
                pageBytes = Memory.MemoryManager.FreeProcessMemory(this);
                Kernel.Waypoint(527);

#if PAGING
            }
            finally {
                Thread.RevertToParentDomain();
            }
#endif

            Tracing.Log(Tracing.Audit, "Memory: [image={0:x}, pages={1:x}, max={2:x}, handles={3:x}] total = {4} bytes",
                        imageBytes, pageBytes, pagesMax, handleBytes,
                        imageBytes + pageBytes + handleBytes);

            PrincipalImpl.Dispose(principal);
            // This must follow handles.FreeAllPages, which relies on processTag.
            // If we null out the entry earlier then the tag could be
            // reused and handles.FreeAllPages could free another process's memory
            processTable[cachedProcessIndex] = null;

            joinEvent.Set();
            SharedHeapWalker.walker.RequestWalk();
            parent.ServiceCheckForExit();

#if PAGING
            // Release our enclosing protection domain
            protectionDomain.Release();
#endif

#if false
            DebugStub.WriteLine(
                "Memory: [image={0:x8}, pages={1:x8}, maxpages={2:x8}, " +
                "handles={3:x8}] total={4:x8} bytes\n",
                __arglist(
                    imageBytes,
                    pageBytes,
                    pagesMax,
                    handleBytes,
                    (long)(imageBytes + pageBytes + handleBytes)));
#endif
        }

        internal unsafe bool CheckEndpointsSet ()
        {
            if (endpointSet == null) return true;
            for (int i = 0; i < endpointSet.Length; i++) {
                if (endpointSet[i] == null) {
                    DebugStub.WriteLine("Process.Start: Cannot start process (id {0}, image {1}), because endpoint {2} is not set",
                         __arglist(processIndex, imageName, i));
                    return false;
                }
            }
            return true;
        }

        // Start the process.
        public bool Start()
        {
            // If we're to be suspended, wait until after resumption to start
            // other processes.
            SuspendBarrierCheckParents();

            processMutex.AcquireMutex();
            parent.processMutex.AcquireMutex();
            try {
                if (state != ProcessState.Unstarted) {
                    DebugStub.WriteLine(" process not in unstarted state!\n");
                    return false;
                }
                if (!CheckEndpointsSet()) {
                    return false;
                }
                parent.startedChildCount++;
                state = ProcessState.Running;
                wasStarted = true;
                threads[0].SetMainThreadRunning();
            }
            finally {
                parent.processMutex.ReleaseMutex();
                processMutex.ReleaseMutex();
            }
            Kernel.Waypoint(528);
            threads[0].StartRunningThread();
            Kernel.Waypoint(529);
            return true;
        }

        internal void StartThread()
        {
            // If we're being suspended, wait until after resumption to start.
            SuspendBarrier();

            // Increment number of threads in a process and continue
            Interlocked.Increment (ref this.startedThreadCount);
        }

        // precondition: processMutex held
        internal void StartMainThread()
        {
            VTable.Assert(state == ProcessState.Running);
            VTable.Assert(startedThreadCount == 0);
            startedThreadCount++;
        }

        // started==true indicates a started process; false
        // indicates an unstarted process.
        public void Join(out bool started)
        {
            Join(SchedulerTime.MaxValue, out started);
        }

        public void Join()
        {
            bool started;
            Join(out started);
            if (!started) {
                throw new ProcessStateException("joining unstarted process");
            }
        }

        // started==true indicates a started process; false
        // indicates an unstarted process.
        // Returns false if the join timed out, true otherwise.
        public bool Join(TimeSpan timeout, out bool started)
        {
            return Join(SchedulerTime.Now + timeout, out started);
        }

        // started==true indicates a started process; false
        // indicates an unstarted process.
        // Returns false if the join timed out, true otherwise.
        public bool Join(SchedulerTime timeOut, out bool started)
        {
            if (state == ProcessState.Unstarted) {
                started = false;
                return false;
            }
            started = true;
            return joinEvent.WaitOne(timeOut);
        }

        // Freeze all the threads in a process.  If recursive==true, then
        // freeze all threads in all descendant processes as well.  This
        // method blocks until all freezing is complete.  Before a thread
        // in kernel mode is frozen, it is allowed to run until it reaches
        // a blocking operation, until it exits, or until it enters process
        // mode.  Semantically, suspended thread execution should be
        // equivalent to running thread execution, except that suspended
        // threads appear to receive time slices of length 0.
        // Returns true if successful; returns false to indicate an
        // unstarted process.
        public bool Suspend(bool recursive)
        {
            // Ask the kernel service thread to call ServiceSuspend.
            return ThreadLocalServiceRequest.SuspendProcess(this, recursive);
        }

        // Should only execute in the kernel service thread
        internal bool ServiceSuspend(bool recursive)
        {
            return ServiceSuspend(recursive, false);
        }

        // Should only execute in the kernel service thread
        private bool ServiceSuspend(bool recursive, bool aboutToStop)
        {
            bool alreadySuspended = false;

            processMutex.AcquireMutex();
            try {
                // The service thread should not already be in the middle of an operation:
                Debug.Assert(state != ProcessState.Suspending, "unexpected process state");
                Debug.Assert(state != ProcessState.SuspendingRecursive, "unexpected process state");
                Debug.Assert(state != ProcessState.Stopping, "unexpected process state");
                if (state == ProcessState.Running) {
                    state = (recursive)?(ProcessState.SuspendingRecursive):(ProcessState.Suspending);
                }
                else if (!aboutToStop && state == ProcessState.Unstarted) {
                    return false;
                }
                else {
                    alreadySuspended = true;
                }
            }
            finally {
                processMutex.ReleaseMutex();
            }

            if (!alreadySuspended) {
                // Hold suspendMutex until suspension is complete, so that other
                // threads in this process block when acquiring suspendMutex.
                // Only try to acquire suspendMutex if the process isn't already
                // suspended, though -- otherwise, one of the suspended threads
                // might be holding suspendMutex.
                suspendMutex.AcquireMutex();
            }

            if (recursive) {
                // Note: now that this.state==Suspending[Recursive], a barrier
                // prevents new child processes, so we can safely traverse the
                // existing children without missing any.
                for (int index = 0;; index++) {
                    Process child = null;
                    processMutex.AcquireMutex();
                    try {
                        if (index >= children.Length) {
                            break;
                        }
                        else if (children[index] == null) {
                            continue;
                        }
                        child = children[index];
                    }
                    finally {
                        processMutex.ReleaseMutex();
                    }
                    if (child != null) {
                        child.ServiceSuspend(true, aboutToStop);
                    }
                }
            }

            if (alreadySuspended) {
                // This process is already suspended, the children are
                // suspended (if recursive==true), so we're done.
                return true;
            }

            bool yieldAndRepeat;
            do {
                yieldAndRepeat = false;

                // Note: now that this.state==Suspending[Recursive], a barrier
                // prevents starting threads, so we can safely traverse the
                // existing threads without missing any started threads.
                for (int index = 0;; index++) {
                    Thread thread = null;
                    processMutex.AcquireMutex();
                    try {
                        if (index >= threads.Length) {
                            break;
                        }
                        else if (threads[index] == null) {
                            continue;
                        }
                        thread = threads[index];
                    }
                    finally {
                        processMutex.ReleaseMutex();
                    }
                    if (thread != null) {
                        thread.Suspend(aboutToStop);
                    }
                }

                if (yieldAndRepeat) {
                    Thread.Yield();
                }
            } while (yieldAndRepeat);

            processMutex.AcquireMutex();
            state = ProcessState.Suspended;
            processMutex.ReleaseMutex();

            suspendMutex.ReleaseMutex();

            return true;
        }

        // Returns true if successful; returns false to indicate an
        // unstarted process.
        public bool Resume(bool recursive)
        {
            // Ask the kernel service thread to call ServiceResume.
            return ThreadLocalServiceRequest.ResumeProcess(this, recursive);
        }

        // Should only execute in the kernel service thread
        internal bool ServiceResume(bool recursive)
        {
            bool alreadyResumed = false;

            processMutex.AcquireMutex();
            try {
                // The service thread should not already be in the middle of an operation:
                Debug.Assert(state != ProcessState.Suspending, "unexpected process state");
                Debug.Assert(state != ProcessState.SuspendingRecursive, "unexpected process state");
                Debug.Assert(state != ProcessState.Stopping, "unexpected process state");
                if (state == ProcessState.Suspended) {
                    state = ProcessState.Running;
                }
                else if (state == ProcessState.Unstarted) {
                    return false;
                }
                else {
                    alreadyResumed = true;
                }
            }
            finally {
                processMutex.ReleaseMutex();
            }

            if (recursive) {
                for (int index = 0;; index++) {
                    Process child = null;
                    processMutex.AcquireMutex();
                    try {
                        if (index >= children.Length) {
                            break;
                        }
                        else if (children[index] == null) {
                            continue;
                        }
                        child = children[index];
                    }
                    finally {
                        processMutex.ReleaseMutex();
                    }
                    if (child != null) {
                        child.ServiceResume(true);
                    }
                }
            }

            if (alreadyResumed) {
                // This process is already resumed, the children are
                // resumed (if recursive==true), so we're done.
                return true;
            }

            for (int index = 0;; index++) {
                Thread thread = null;
                processMutex.AcquireMutex();
                try {
                    if (index >= threads.Length) {
                        break;
                    }
                    else if (threads[index] == null) {
                        continue;
                    }
                    thread = threads[index];
                }
                finally {
                    processMutex.ReleaseMutex();
                }
                if (thread != null) {
                    thread.Resume();
                }
            }
            return true;
        }

        public void Stop(int exitCode)
        {
            //
            //  Terminate the process forcefully.
            //  Should remove all user code from threads, then force them
            //  to terminate ASAP, close out objects, etc.

            // Ask the kernel service thread to call ServiceStop.
            ThreadLocalServiceRequest.StopProcess(this, exitCode);
        }

        // Should only execute in the kernel service thread
        //
        // ServiceStop does not block waiting for threads to exit,
        // so it is recommended that whoever makes the service
        // request (currently ThreadLocalServiceRequest) perform
        // a Process.Join to block until the threads have exited
        // and the process has stopped.
        internal void ServiceStop(int exitCode)
        {
            processMutex.AcquireMutex();
            try {
                if (state == ProcessState.Stopped) {
                    return;
                }
            }
            finally {
                processMutex.ReleaseMutex();
            }

            // Make sure that any suspended process we're about to stop has
            // a chance to process any pending signals before getting stopped
            // forever:
            ServiceResume(true);

            // Now suspend it for good:
            ServiceSuspend(true, true);

            ServiceStopAfterSuspend(exitCode);
        }

        // Should only execute in the kernel service thread
        private void ServiceStopAfterSuspend(int exitCode)
        {
            processMutex.AcquireMutex();
            try {
                // Note: we cannot be "Stopped" here, because there
                // are no calls to ServiceRelease between here and
                // the beginning of ServiceStop.  If we ever decide to have
                // more than one service thread, we'll have to revisit this.
                Debug.Assert(state == ProcessState.Suspended
                          || state == ProcessState.Unstarted, "unexpected process state");
                state = ProcessState.Stopping;
            }
            finally {
                processMutex.ReleaseMutex();
            }

            processMutex.AcquireMutex();
            Process[] childArray = children;
            processMutex.ReleaseMutex();
            // Don't hold processMutex while calling ServiceStop; it
            // would try to double-acquire the lock in RemoveChild.
            // No locking should be necessary here, because a
            // suspended process should not add new children.
            foreach (Process c in childArray) {
                if (c != null) {
                    c.ServiceStopAfterSuspend(exitCode);
                }
            }

            // Throw an exception in each suspended thread.
            for (int index = 0;; index++) {
                Thread thread = null;
                processMutex.AcquireMutex();
                try {
                    if (index >= threads.Length) {
                        break;
                    }
                    else if (threads[index] == null) {
                        continue;
                    }
                    thread = threads[index];
                }
                finally {
                    processMutex.ReleaseMutex();
                }
                if (thread != null) {
                    thread.StopSuspended();
                }
            }

            if (exitCode >= (int) ProcessExitCode.StopMin &&
                exitCode <= (int) ProcessExitCode.StopMax) {
                this.exitCode = exitCode;
            }
            else {
                this.exitCode = (int) ProcessExitCode.StopDefault;
            }

            // Needed only to handle the Unstarted state:
            ServiceCheckForExit();
        }

        // Should only execute in the kernel service thread
        internal void ServiceOnThreadStop(Thread thread)
        {
#if THREAD_TIME_ACCOUNTING
            deadThreadExecutionTime += thread.ExecutionTime;
            deadThreadCount++;
#endif
            bool found = ServiceRemoveThread(thread);
            VTable.Assert(found);
            ServiceCheckForExit();
        }

        // Check to see if a process should exit.  If so, release its
        // resources.
        // Should only execute in the kernel service thread
        private void ServiceCheckForExit()
        {
            if (startedThreadCount == 0 && startedChildCount == 0) {
                ServiceRelease();
            }
        }

        // If the current process is about to suspend, block until
        // the process resumes.  Note: if efficiency is more important than
        // immediate blocking, you can check ThreadContext.suspendAlert
        // before calling SuspendBarrier, which (assuming a reasonable
        // multiprocessor memory model) will eventually become
        // true during a suspension if the thread runs long enough:
        //   if (Thread.CurrentThread.context.suspendAlert) SuspendBarrier();
        // The important thing is that each running thread eventually enters a
        // suspendable state (process-unblocked-running or
        // kernel-blocked-running) so that the loop in ServiceSuspend will
        // terminate.
        internal static void SuspendBarrier()
        {
            Process p = Thread.CurrentProcess;
            // The service thread holds the suspendMutex throughout the
            // suspension process, so we'll block if we try to acquire
            // it during suspension:
            p.suspendMutex.AcquireMutex();
            Thread.CurrentThread.context.suspendAlert = false;
            // Ok, we must be running now.  Release the mutex.
            p.suspendMutex.ReleaseMutex();
        }

        // Block if any the current process is suspending or if any of its
        // ancestors is known by this processor to be suspending recursively.
        internal static void SuspendBarrierCheckParents()
        {
            bool yieldAndRepeat;
            do {
                yieldAndRepeat = false;
                SuspendBarrier();
                for (Process p = Thread.CurrentProcess.parent; p != null; p = p.parent) {
                    // Don't try to acquire another process's suspendMutex;
                    // instead, just check its state field.
                    // MULTIPROCESSOR NOTE: It's not
                    // important that we see the most up-to-date value of
                    // p.state immediately -- we just need to see
                    // SuspendingRecursive eventually if we call this
                    // barrier enough times.
                    if (p.state == ProcessState.SuspendingRecursive) {
                        // An ancestor is suspending recursively.  This
                        // means we'll be suspended soon.  Just wait
                        // for this to happen by yielding repeatedly;
                        // we'll eventually block in SuspendBarrier().
                        yieldAndRepeat = true;
                    }
                }
                if (yieldAndRepeat) {
                    Thread.Yield();
                }
            } while (yieldAndRepeat);
        }

        public void Allocated(UIntPtr bytes)
        {
#if THREAD_SAFE_INTERNAL_ONLY
            UIntPtr used;
            UIntPtr now;
            do {
                now = pagesNow;
                used = now + bytes;
            } while (now != Interlocked.CompareExchange(ref pagesNow, used, now));

            do {
                now = pagesMax;
            } while (used > now &&
                     now != Interlocked.CompareExchange(ref pagesMax, used, now));
#else
            pagesNow += bytes;
            if (pagesMax < pagesNow) {
                pagesMax = pagesNow;
            }
#endif
        }

        public void Freed(UIntPtr bytes)
        {
#if THREAD_SAFE_INTERNAL_ONLY
            UIntPtr used;
            UIntPtr now;
            do {
                now = pagesNow;
                used = now - bytes;
            } while (now != Interlocked.CompareExchange(ref pagesNow, used, now));
#else
            pagesNow -= bytes;
#endif
        }

        // Returns the currently allocated memory in bytes.
        public UIntPtr AllocatedMemory {
            [NoHeapAllocation]
            get { return pagesNow; }
        }

        // Returns the peak allocated memory in bytes.
        public UIntPtr PeakAllocatedMemory {
            [NoHeapAllocation]
            get { return pagesMax; }
        }

        // Returns number of pages in the handle table
        public int NumHandlePages {
            [NoHeapAllocation]
            get { return handles.GetPageCount(); }
        }

        public int ExitCode {
            [NoHeapAllocation]
            get { return exitCode; }
        }

        // Return parameter is really: DirectoryService.Imp opt(ExHeap) *
        public unsafe SharedHeap.Allocation * GetNamespaceEndpoint()
        {
            return DirectoryService.NewClientEndpointEx();
        }

        //
        // Endpoint Argument Processing
        //

        // Set the size of the endpoint set.
        public unsafe bool SetEndpointCount(int count) {
            if (state != ProcessState.Unstarted) {
                throw new ProcessStateException("process not unstarted");
            }
            if (count == 0) {
                // don't create array if the count is zero.
                return true;
            }

            endpointSet = new SharedHeap.Allocation * [count];
            //DebugStub.WriteLine("-- Process.SetEndpointCount({0})",
            //__arglist(count));
            return true;
        }

        // Set the endpoint and individual endpoint.
        public unsafe bool SetEndpoint(int index, ref SharedHeap.Allocation * endpoint)
        {
            // TODO: FIXFIX: I short-circuited the check below to bypass
            // issues with stdin pipes.

            // if (state != ProcessState.Unstarted) {
            //     throw new ProcessStateException("process not unstarted");
            //

            if (endpointSet == null) {
                DebugStub.WriteLine("Process.SetEndpoint is NULL!");
                throw new ProcessStateException("endpoint set not allocated, attempting to set");
            }
            if (index > endpointSet.Length - 1) {
                DebugStub.WriteLine("Process.SetEndpoint {0} out of range!",__arglist(index));
                throw new ProcessStateException("endpoint index out of range");
            }
            if (endpointSet[index] != null) {
                DebugStub.Break();
                DebugStub.WriteLine("Process.SetEndpoint {0} was already set!",__arglist(index));
                throw new ProcessStateException("endpoint already non-null");
            }

            // We first move it to the kernel. When the target process retrieves it,
            // we move it into its heap.
            endpointSet[index] =
                Microsoft.Singularity.Channels.EndpointCore.MoveEndpoint(
                    Thread.CurrentProcess.ProcessSharedHeap,
                    SharedHeap.KernelSharedHeap, this, endpoint);

            endpoint = null;
            return true;
        }

        public unsafe int GetStartupEndpointCount()
        {
            //DebugStub.WriteLine("-- Process.GetStartupEndpointCount() -> {0}",
            //__arglist((int)(endpointSet != null ? endpointSet.Length : 0)));
            return endpointSet != null ? endpointSet.Length : 0;
        }

        public unsafe SharedHeap.Allocation * GetStartupEndpoint(int arg)
        {
            // Endpoints can only be retrieved once.
            if (endpointSet == null || arg >= endpointSet.Length) {
                // legacy code will always ask for a null endpoint 0.
                //DebugStub.WriteLine("-- Process.GetStartupEndpoint({0}) -> {1:x8}",
                //__arglist(arg, 0));
                return null;
            }
            SharedHeap.Allocation * used = endpointSet[arg];
            endpointSet[arg] = null;

#if PAGING
            // now move it from kernel to user process
            used = Microsoft.Singularity.Channels.EndpointCore.MoveEndpoint(
                SharedHeap.KernelSharedHeap, this.ProcessSharedHeap, this, used);
#endif

            return used;
        }

        // String Argument Processing
        //          <set,get>StringArg
        //          <set,get>StringArgCount

        public  bool SetStringArgCount(int count) {
            if (state != ProcessState.Unstarted) {
                throw new ProcessStateException("process not unstarted");
            }
            if (count == 0) {
                // don't create array if the count is zero.
                return true;
            }

            stringArgSet = new StringArg [count];
            //DebugStub.WriteLine("-- Process.SetStringArgCount({0})",
            //__arglist(count));
            return true;
        }

        public bool SetStringArrayArgCount(int count) {
            //DebugStub.WriteLine("SetStringArrayArg called. count={0}", __arglist(count));
            if (state != ProcessState.Unstarted) {
                throw new ProcessStateException("process not unstarted");
            }
            if (count == 0) {
                // don't create array if the count is zero.
                return true;
            }
            stringArrayArgSet = new StringArrayArg [count];
            if (stringArrayArgSet == null) {
                throw new Exception("out of memory in process SetStringArrayArgCount");
            }
            return true;
        }

        public int GetStartupStringArrayArgCount() {
            return stringArrayArgSet != null ? stringArrayArgSet.Length : 0;
        }

        public ParameterCode GetStartupStringArrayArg(int index, out string [] strings)
        {
            //DebugStub.WriteLine("GetStartupStringArrayArg called. index={0}", __arglist(index));
            if (stringArrayArgSet == null) {
                strings = null;
                return ParameterCode.NotSet;
            }
            if (index > stringArrayArgSet.Length - 1) {
                strings = null;
                return ParameterCode.OutOfRange;
            }
            if (stringArrayArgSet[index] == null) {
                strings = null;
                return ParameterCode.NotSet;
            }


            if (!stringArrayArgSet[index].Set) {
                strings = null;
                return ParameterCode.NotSet;
            }
            //DebugStub.WriteLine("GetStartupStringArrayArg getting value");
            strings = stringArrayArgSet[index].Value;
            return ParameterCode.Success;
        }

        public ParameterCode SetStartupStringArrayArg(int index, string[] strings)
        {
            //DebugStub.WriteLine("Setting string Arg array");
            if (index > stringArrayArgSet.Length - 1) {
                return ParameterCode.OutOfRange;
            }

            if (stringArrayArgSet[index] == null) {
                stringArrayArgSet[index]  = new StringArrayArg(strings);
            }
            else {
                stringArrayArgSet[index].Value = strings;
            }
            stringArrayArgSet[index].Set = true;
            return ParameterCode.Success;
        }

        public ParameterCode SetStartupStringArg(int index, string value) {
            //DebugStub.WriteLine("set string attempting to set idx={0}", __arglist(index));
            if (index > stringArgSet.Length - 1) {
                //DebugStub.WriteLine("Process.SetStringArg {0} out of range!",__arglist(index));
                //throw new ProcessStateException("StringArg index out of range");
                return ParameterCode.OutOfRange;
            }

            if (stringArgSet[index] != null) {
                //DebugStub.Break();
                //DebugStub.WriteLine("Process.SetStringArg {0} was already set!",__arglist(index));
                //throw new ProcessStateException("StringArg already non-null");
                return ParameterCode.AlreadySet;
            }

            stringArgSet[index] = new StringArg(value);
            stringArgSet[index].Set = true;
            return ParameterCode.Success;
        }

        public unsafe int GetStartupStringArgCount() {
            return stringArgSet != null ? stringArgSet.Length : 0;
        }

        public unsafe ParameterCode GetStartupStringArg(int arg, out string value) {
            if (stringArgSet == null) {
                value = null;
                return ParameterCode.NotSet;
            }
            if (arg >= stringArgSet.Length) {
                value = null;
                return ParameterCode.OutOfRange;
            }
            if (stringArgSet[arg] == null) {
                value = null;
                return ParameterCode.Success;
            }

            if (!stringArgSet[arg].Set) {
                value = null;
                return ParameterCode.NotSet;
            }
            value = stringArgSet[arg].Value;
            return ParameterCode.Success;
        }

        // int Argument Processing
        //          <set,get>StringArg
        //          <set,get>StringArgCount

        public unsafe bool SetLongArgCount(int count) {
            if (state != ProcessState.Unstarted) {
                throw new ProcessStateException("process not unstarted");
            }
            if (count == 0) {
                // don't create array if the count is zero.
                return true;
            }

            longArgSet = new LongArg [count];
            //DebugStub.WriteLine("-- Process.SetLongArgCount({0})",
            //__arglist(count));
            return true;
        }

        public unsafe ParameterCode SetStartupLongArg(int index, long value) {
            if (index > longArgSet.Length - 1) {
                //DebugStub.WriteLine("Process.SetLongArg {0} out of range!",__arglist(index));
                //throw new ProcessStateException("LongArg index out of range");
                return ParameterCode.OutOfRange;
            }
            // TODO checks for setting more than once
            if (longArgSet[index] != null) {
                return ParameterCode.AlreadySet;
            }

            longArgSet[index] = new LongArg(value);
            longArgSet[index].Set = true;

            return ParameterCode.Success;
        }

        public unsafe int GetStartupLongArgCount() {
            return longArgSet != null ? longArgSet.Length : 0;
        }

        public unsafe ParameterCode GetStartupLongArg(int arg, out long value) {
            if (longArgSet == null || arg >= longArgSet.Length) {
                //DebugStub.WriteLine("Process.GetLongArg {0} out of range!",__arglist(arg));
                //throw new ProcessStateException("LongArg index out of range");
                value = -1;
                return ParameterCode.OutOfRange;
            }

            if (longArgSet[arg] == null) {
                value = -1;
                return ParameterCode.NotSet;
            }

            if (longArgSet[arg].Set == false) {
                value = -1;
                return ParameterCode.NotSet;
            }
#if EXTRA
            if (longArgSet[arg].Retrieved == true) {
                value = -1;
                return ParameterCode.Retrieved;
            }
#endif
            value = longArgSet[arg].Value;
            longArgSet[arg].Retrieved = true;
            return ParameterCode.Success;
        }

        // bool Argument Processing
        //          <set,get>StringArg
        //          <set,get>StringArgCount

        public unsafe bool SetBoolArgCount(int count) {
            if (state != ProcessState.Unstarted) {
                throw new ProcessStateException("process not unstarted");
            }
            if (count == 0) {
                // don't create array if the count is zero.
                return true;
            }

            boolArgSet = new BoolArg [count];
            //DebugStub.WriteLine("-- Process.SetBoolArgCount({0})",
            //__arglist(boolArgSet.Length));
            return true;
        }

        public unsafe ParameterCode SetStartupBoolArg(int index, bool value) {
            if (boolArgSet == null) return ParameterCode.OutOfRange;

            if (index > boolArgSet.Length - 1) {
                //DebugStub.WriteLine("Process.SetBoolArg {0} out of range!",__arglist(index));
                //throw new ProcessStateException("BoolArg index out of range");
                return ParameterCode.OutOfRange;
            }
            // TODO checks for setting more than once
            boolArgSet[index] = new BoolArg(value);
            boolArgSet[index].Set = true;
            return ParameterCode.Success;
        }

        public unsafe ParameterCode GetStartupBoolArg(int index, out bool value) {
            value = false;
            if (boolArgSet == null || index >= boolArgSet.Length) {
                //DebugStub.WriteLine("Process.GetBoolArg {0} out of range!",__arglist(index));
                //throw new ProcessStateException("BoolArg index out of range");\
                value = false;
                return ParameterCode.OutOfRange;
            }

            if (boolArgSet[index] == null) {
                value = false;
                return ParameterCode.NotSet;
            }

            if (boolArgSet[index].Set == false) {
                return ParameterCode.NotSet;
            }
            value = boolArgSet[index].Value;
            boolArgSet[index].Retrieved = true;
            return ParameterCode.Success;
        }

        public unsafe int GetStartupBoolArgCount() {
            //if ( boolArgSet != null) DebugStub.WriteLine("bool args=", __arglist(boolArgSet.Length));
            return boolArgSet != null ? boolArgSet.Length : 0;
        }


        public void SetArgs(string[] args)
        {
            this.args = args;
        }

        [NoHeapAllocation]
        public int GetStartupArgCount()
        {
            return args.Length;
        }

        [NoHeapAllocation]
        public string GetStartupArg(int arg)
        {
            if (arg >= args.Length) {
                return null;
            }
            return args[arg];
        }

        [NoHeapAllocation]
        public string GetProcessName() {
            return imageName;
        }

        [NoHeapAllocation]
        public void SetGcPerformanceCounters(TimeSpan timeSpent, long bytes) {
            gcCount++;
            gcTotalTime = gcTotalTime.AddNoAlloc(timeSpent);
            gcTotalBytes += bytes;
        }

        [NoHeapAllocation]
        public void GetGcPerformanceCounters( out int count, out TimeSpan time, out long bytes)
        {
            count = gcCount;
            time  = gcTotalTime;
            bytes = gcTotalBytes;
        }

        public long GetThreadTimes()
        {
#if THREAD_TIME_ACCOUNTING
            long total = 0;
            for (int i = 0; i < threads.Length; i++) {
                if (threads[i] != null) {
                    total += threads[i].ExecutionTime.Ticks;
                }
            }
            return total;
#else
            return 0;
#endif
        }

        public long DeadThreadCount
        {
            get
            {
                return deadThreadCount;
            }
        }

        public long DeadThreadTime
        {
            get
            {
                return deadThreadExecutionTime.Ticks;
            }
        }

        public int [] GetThreadIDs()
        {
            int threadCount = 0;
            int [] temp = null;

            processMutex.AcquireMutex();
            try {
                for (int i = 0; i < threads.Length; i++) {
                    if (threads[i] != null) threadCount++;
                }
                if (threadCount > 0) {
                    temp = new int[threadCount];

                    int current = 0;
                    for (int i = 0; i < threads.Length; i++) {
                        if (threads[i] != null) {
                            temp[current++] = threads[i].GetThreadId();
                        }
                    }
                }
                //else DebugStub.Break();
            }
            finally {
                processMutex.ReleaseMutex();
            }
            return temp;
        }

        // Start the execution within the PE Image.
        private void PeStart()
        {
            Tracing.Log(Tracing.Audit, "** Start of process {0}.", args[0]);
            UIntPtr entryPoint = image.GetEntryPoint(loadedImage);

#if VERBOSE
            DebugStub.WriteLine("calling CallEntryPoint");
            DebugStub.WriteLine(" entry:{0:x8}, args{1}",__arglist((uint)entryPoint, args));
            for (int i = 0; i < args.Length; i++) {
                DebugStub.WriteLine("  {0}: [{1}]", __arglist(i, args[i]));
            }
#endif
            try {
                Tracing.Log(Tracing.Audit, "Calling entryPoint={0:x}", entryPoint);
                Kernel.Waypoint(530);
#if THREAD_TIME_ACCOUNTING
                Processor.GetCurrentThread().context.lastExecutionTimeUpdate =
                    Processor.CycleCount;
#endif
                int code = PEImage.CallEntryPoint(entryPoint, -1, !RunsAtKernelPrivilege);
                if (code >= (int) ProcessExitCode.MainMin &&
                    code <= (int) ProcessExitCode.MainMax) {
                    exitCode = code;
                }
                else {
                    exitCode = (int) ProcessExitCode.ErrorDefault;
                }
                Kernel.Waypoint(531);
                unchecked {
                    Tracing.Log(Tracing.Audit, "Main thread exited with (exit={0})",
                                (UIntPtr)(uint)exitCode);
                }
            }
            catch (Exception e) {
                // Don't set exitCode here; the only exception we should see is
                // ProcessStopException, and Stop sets exitCode in this case.
                Tracing.Log(Tracing.Fatal, "Main thread failed with exception {0}.{1}",
                            e.GetType().Namespace, e.GetType().Name);
                Tracing.Log(Tracing.Trace, "Exception message was {0}",
                            e.ToString());
                DebugStub.WriteLine("Process.cs: Caught exception {0}.", __arglist(e.ToString()));
            }
        }

        // Start the execution of the new thread within the PE Image.
        private void PeStartThread()
        {
            UIntPtr entryPoint = image.GetEntryPoint(loadedImage);
            int threadIndex = Thread.CurrentThread.processThreadIndex;
            int threadExit = 0;

            Tracing.Log(Tracing.Debug,
                        "PeStartThread(entry={0:x8}, threadIndex={1}",
                        entryPoint, (uint)threadIndex);
#if VERBOSE
            DebugStub.WriteLine("calling CallEntryPoint for thread");
            DebugStub.WriteLine(" entry:{0:x8}, threadIndex={1}",
                                __arglist((uint)entryPoint, threadIndex));
#endif
            try {
                Tracing.Log(Tracing.Audit, "Calling thread entryPoint={0:x}", entryPoint);
                Kernel.Waypoint(532);
#if THREAD_TIME_ACCOUNTING
                Processor.GetCurrentThread().context.lastExecutionTimeUpdate =
                    Processor.CycleCount;
#endif
                threadExit = PEImage.CallEntryPoint(entryPoint, threadIndex,
                                                    !RunsAtKernelPrivilege);
                Kernel.Waypoint(533);
                unchecked {
                    Tracing.Log(Tracing.Audit, "Thread exited with (exit={0})",
                                (UIntPtr)(uint)threadExit);
                }
            }
            catch (Exception e) {
                Tracing.Log(Tracing.Fatal, "Process thread failed with exception {0}.{1}",
                            e.GetType().Namespace, e.GetType().Name);
                Tracing.Log(Tracing.Trace, "Exception message was {0}",
                            e.ToString());
                DebugStub.WriteLine("Caught exception {0}.", __arglist(e.ToString()));
            }
        }

        public ProcessState State {
            get { return this.state; }
        }

#region HandleTable
        public unsafe UIntPtr AllocateHandle()
        {
            return handles.AllocateHandle();
        }

        public unsafe UIntPtr AllocateHandle(object obj)
        {
            DebugStub.Assert(obj != null, "Can't allocate handle for null object.");

            UIntPtr handle = handles.AllocateHandle();
            HandleTable.SetHandle(handle, obj);
            return handle;
        }

        public void ReleaseHandle(UIntPtr id)
        {
            unchecked {
                Tracing.Log(Tracing.Debug, "Process[{0:x3}].ReleaseHandle(id={1:x})",
                            (UIntPtr)(uint)processIndex, id);
            }
            handles.FreeHandle(id);
        }
#endregion
    }
}
