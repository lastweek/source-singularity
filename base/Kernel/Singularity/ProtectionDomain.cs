////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ProtectionDomain.cs
//
//  Note:
//

//#define VERBOSE

using System;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.Singularity.Io;
using Microsoft.Singularity.Loader;
using Microsoft.Singularity.Memory;

namespace Microsoft.Singularity
{

    //
    // A protection domain consists of an address space, a communication
    // heap, and a general-purpose memory range. A protection domain
    // can host multiple processes.
    //
    [CLSCompliant(false)]
    public class ProtectionDomain
    {
        /////////////////////////////////////
        // STATIC DATA
        /////////////////////////////////////

        // Table of protection domains
        private const uint maxPDs = 1024;
        private static ProtectionDomain[] PdTable;
        private static SmartSpinlock tableLock;
        private static uint PdIndexGenerator;

        /////////////////////////////////////
        // INSTANCE DATA
        /////////////////////////////////////

        // -------------- Valid before InitHook()
        private AddressSpace space;
        private int refCount;
        private uint id;
        private readonly bool kernelMode;
        private readonly string name;

        // Used to protect the user-range page mapping
        // descriptors.
        private readonly SmartSpinlock userMappingLock;

        // -------------- Valid after InitHook()
        private VirtualMemoryRange userRange;
#if PAGING
        private SharedHeap userSharedHeap;

        // These are always null for a kernel domain
        private PEImage ring3AbiImage;
        private ExportTable ring3AbiExports;
#endif

        // Used for initialization
        private bool initialized;
        private SmartSpinlock initSpin;

        /////////////////////////////////////
        // PUBLIC STATIC METHODS
        /////////////////////////////////////

        internal static void Initialize()
        {
            tableLock = new SmartSpinlock(SpinLock.Types.ProtectionDomainTable);
            PdTable = new ProtectionDomain[maxPDs];
            PdIndexGenerator = 1;

            // Create the default protection domain
            AddressSpace defaultSpace = VMManager.GetBootstrapSpace();
            PdTable[0] = new ProtectionDomain(defaultSpace, "Default", true);
        }

        internal static void InitializeSharedHeapWalker()
        {
            // TODO: The walker needs to become per-protection-domain
            // on paging systems
            SharedHeapWalker.Initialize(
                SharedHeap.KernelSharedHeap.DataOwnerId,
                SharedHeap.KernelSharedHeap.EndpointOwnerId);
        }

        internal static ProtectionDomain FindOrCreateByName(string name,
                                                            bool kernelMode)
        {
            bool iflag = tableLock.Lock();

            try {
                for (uint i = 0; i < PdTable.Length; i++) {
                    if ((PdTable[i] != null) &&
                        (PdTable[i].name == name)) {
                        // found it
                        return PdTable[i];
                    }
                }

                return CreateProtectionDomain(name, kernelMode);
            }
            finally {
                tableLock.Unlock(iflag);
            }
        }

        internal static ProtectionDomain DefaultDomain
        {
            get {
                DebugStub.Assert(PdTable[0] != null);
                return PdTable[0];
            }
        }

        internal static ProtectionDomain CurrentDomain
        {
            get {
#if PAGING
                return Thread.CurrentThread.CurrentDomain;
#else
                return Thread.CurrentThread.Process.Domain;
#endif
            }
        }

        /////////////////////////////////////
        // PUBLIC INSTANCE METHODS
        /////////////////////////////////////

        internal void AddRef()
        {
            Interlocked.Increment(ref refCount);
        }

        internal int Release()
        {
            int decreased = Interlocked.Decrement(ref refCount);
            DebugStub.Assert(decreased > 0);
            return decreased;
        }

        internal AddressSpace AddressSpace {
            get {
                return space;
            }
        }

        internal SmartSpinlock UserMappingLock {
            get {
                return userMappingLock;
            }
        }

        internal bool KernelMode {
            get {
                return kernelMode;
            }
        }

#if PAGING
        internal ExportTable ABIStubs {
            get {
                return ring3AbiExports;
            }
        }
#endif

        //
        // Someone must arrange to call this from *within* the
        // Protection Domain for us to have an opportunity to finish
        // initializing.
        //
        internal unsafe void InitHook()
        {
            // If paging is disabled then just return immediately
            if (!MemoryManager.UseAddressTranslation) {
                return;
            }

            DebugStub.Assert(AddressSpace.CurrentAddressSpace == this.AddressSpace);

            if (this.initialized) {
                // Someone else has already set up the space
                return;
            }

            bool iflag = initSpin.Lock();

            try {
                if (this.initialized) {
                    // Someone else snuck in and initialized
                    return;
                }

                //
                // We're first into this space, so set it up.
                //
#if VERBOSE
                DebugStub.WriteLine("Setting up protection domain \"{0}\"",
                                    __arglist(this.name));
#endif

                userRange = new VirtualMemoryRange(VMManager.UserHeapBase,
                                                   VMManager.UserHeapLimit,
                                                   this);
#if PAGING
                if (kernelMode) {
                    // This will be a ring-0, trusted domain, so just
                    // point the userSharedHeap at the kernel's comm heap.
                    userSharedHeap = SharedHeap.KernelSharedHeap;

                    this.initialized = true;
                }
                else {
                    // Create a new shared heap that lives in
                    // user-land.
                    userSharedHeap = new SharedHeap(this, userRange);
#if VERBOSE
                    DebugStub.WriteLine("  ...Created a shared heap");
#endif

                    //
                    // N.B.: this is kind of tricky. Loading an
                    // executable image involves allocating memory,
                    // which goes through this object. So, before
                    // attempting the load, mark ourselves as initialized.
                    //
                    // ---- DON'T PUT GENUINE INITIALIZATION
                    //      CODE BELOW HERE! ---------
                    this.initialized = true;

                    // Load our own, protection-domain-private copy of the
                    // ABI stubs. These will get shared by all apps in
                    // this domain.
                    IoMemory syscallsMemory = Binder.LoadRawImage("/init", "syscalls.dll");
                    IoMemory loadedMemory;

                    // Load the stubs library into the user range, but make
                    // the kernel process the logical owner. This seems like
                    // the only sensible approach since the stubs do not
                    // belong to any particular process but must be in the
                    // user range of memory.

                    // N.B.: RE-ENTERS this object!
                    ring3AbiImage = PEImage.Load(Process.kernelProcess, syscallsMemory,
                                                 out loadedMemory,
                                                 false, // isForMp
                                                 false // inKernelSpace
                                                 );

                    ring3AbiExports = ring3AbiImage.GetExportTable(loadedMemory);
#if VERBOSE
                    DebugStub.WriteLine("  ...Loaded ring-3 ABI stubs");
#endif
                }
#else // PAGING
                this.initialized = true;
#endif // PAGING

            }
            finally {
                DebugStub.Assert(this.initialized);
                initSpin.Unlock(iflag);
            }
        }

        internal string Name {
            get {
                return this.name;
            }
        }

        //
        // Accessors below are only usable after InitHook()
        //
        internal VirtualMemoryRange UserRange {
            get {
                DebugStub.Assert(initialized);
                return userRange;
            }
        }

#if PAGING
        internal SharedHeap UserSharedHeap {
            [Inline]
            get {
                DebugStub.Assert(initialized);
                return userSharedHeap;
            }
        }

        internal SharedHeap.AllocationOwnerId DataOwnerId
        {
            get {
                DebugStub.Assert(initialized);
                return UserSharedHeap.DataOwnerId;
            }
        }

        internal SharedHeap.AllocationOwnerId EndpointOwnerId
        {
            get {
                DebugStub.Assert(initialized);
                return UserSharedHeap.EndpointOwnerId;
            }
        }

        internal SharedHeap.AllocationOwnerId EndpointPeerOwnerId
        {
            get {
                DebugStub.Assert(initialized);
                return UserSharedHeap.EndpointPeerOwnerId;
            }
        }
#endif

        /////////////////////////////////////
        // PRIVATE METHODS
        /////////////////////////////////////

        private static ProtectionDomain CreateProtectionDomain(
            string name, bool isKernelDomain)
        {
            ProtectionDomain dp = new ProtectionDomain(name, isKernelDomain);
            dp.id = AssignNewPDSlot(dp);
            return dp;
        }

        private ProtectionDomain(string name, bool isKernelDomain)
            : this(VMManager.CreateNewAddressSpace(), name, isKernelDomain)
        {
        }

        private ProtectionDomain(AddressSpace space, string name, bool isKernelDomain)
        {
            this.space = space;
            this.name = name;
            this.kernelMode = isKernelDomain;
            this.initSpin = new SmartSpinlock(SpinLock.Types.ProtectionDomainInit);
            this.userMappingLock = new SmartSpinlock(SpinLock.Types.ProtectionDomainMapping);
            this.refCount = 1; // represents the table entry
#if VERBOSE
            DebugStub.WriteLine("Created protection domain \"{0}\"", __arglist(name));
#endif
        }

        private static uint AssignNewPDSlot(ProtectionDomain pd)
        {
            // Consider; Assert tableLock is aquired?

            for (uint i = 0; i < PdTable.Length; i++) {
                uint index = (uint)((PdIndexGenerator + i) % PdTable.Length);

                if (PdTable[index] == null) {
                    PdTable[index] = pd;
                    PdIndexGenerator = (uint)((index + 1) % PdTable.Length);
                    return index;
                }
            }

            DebugStub.Assert(false, "Out of process domain slots!");
            return uint.MaxValue;
        }
    }
}
