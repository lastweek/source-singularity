////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Pdt.cs
//
//  Note:
//

namespace Microsoft.Singularity.Isal.IX
{
    using System;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;

    ///
    /// <remarks> PAE Paging Constants. </remarks>
    ///
    [CLSCompliant(false)]
    [AccessedByRuntime("accessed from singldr.cpp")]
    internal struct PE
    {
        // Bit masks
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong VALID        = 0x0000000000000001;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong WRITEABLE    = 0x0000000000000002;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong USER         = 0x0000000000000004;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong WRITETHROUGH = 0x0000000000000008;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong CACHEDISABLE = 0x0000000000000010;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong ACCESSED     = 0x0000000000000020;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong DIRTY        = 0x0000000000000040;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong PAT          = 0x0000000000000080;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong IS2MB        = 0x0000000000000080;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong GLOBAL       = 0x0000000000000100;
        [AccessedByRuntime("accessed from singldr.cpp")]
        internal const ulong NX           = 0x8000000000000000;

        // Address mask for 4KB entries
        internal const ulong ADDRMASK     = 0x000FFFFFFFFFF000;

        // Address mask for 2MB entries
        internal const ulong ADDRMASK_2MB = 0x000FFFFFFFF00000;
    }

    ///
    /// <remarks> IX PAE Page table entry. </remarks>
    ///
    [CLSCompliant(false)]
    internal struct PTE {
        private ulong val;

        // These bits must not be set
        private const ulong MBZ_MASK      = ~(PE.VALID | PE.WRITEABLE | PE.USER |
                                              PE.WRITETHROUGH | PE.CACHEDISABLE |
                                              PE.ACCESSED | PE.DIRTY | PE.PAT |
                                              PE.GLOBAL | PE.ADDRMASK | PE.NX);
        public bool Valid {
            get { return (val & PE.VALID) != 0; }
            set { val = value ? val | PE.VALID : val & (~PE.VALID); }
        }

        public bool Writeable {
            get { return (val & PE.WRITEABLE) != 0; }
            set { val = value ? val | PE.WRITEABLE : val & (~PE.WRITEABLE); }
        }

        public bool User {
            get { return (val & PE.USER) != 0; }
            set { val = value ? val | PE.USER : val & (~PE.USER); }
        }

        public bool WriteThrough {
            get { return (val & PE.WRITETHROUGH) != 0; }
            set { val = value ? val | PE.WRITETHROUGH : val & (~PE.WRITETHROUGH); }
        }

        public bool CacheDisable {
            get { return (val & PE.CACHEDISABLE) != 0; }
            set { val = value ? val | PE.CACHEDISABLE : val & (~PE.CACHEDISABLE); }
        }

        public bool Accessed {
            get { return (val & PE.ACCESSED) != 0; }
            set { val = value ? val | PE.ACCESSED : val & (~PE.ACCESSED); }
        }

        public bool Dirty {
            get { return (val & PE.DIRTY) != 0; }
            set { val = value ? val | PE.DIRTY : val & (~PE.DIRTY); }
        }

        public bool Global {
            get { return (val & PE.GLOBAL) != 0; }
            set { val = value ? val | PE.GLOBAL : val & (~PE.GLOBAL); }
        }

        public ulong Flags {
            get { return val & ~PE.ADDRMASK; }
            set {
                DebugStub.Assert((value & PE.ADDRMASK) == 0);
                DebugStub.Assert((value & MBZ_MASK) == 0);
                val |= value;
            }
        }

        public ulong Address {
            get { return val & PE.ADDRMASK; }
            set {
                DebugStub.Assert((value & ~PE.ADDRMASK) == 0);
                val = (val & ~(PE.ADDRMASK)) | (value & PE.ADDRMASK);
            }
        }

        public void Init() {
            val = 0;
        }
    };

    ///
    /// <remarks> IX PAE Page table. </remarks>
    ///
    [CLSCompliant(false)]
    internal struct PT {
        private PTE entry/*[512]*/;

        public unsafe void Init() {
            fixed (PTE* pEntry = &entry) {
                PTE* pte = pEntry;

                for (int i = 0; i < 512; i++) {
                    pte->Init();
                    pte++;
                }
            }
        }

        public unsafe PTE* this [ uint idx ]
        {
            get {
                DebugStub.Assert(idx < 512);

                fixed (PTE* pEntry = &entry) {
                    return &pEntry[idx];
                }
            }
        }
    };

    ///
    /// <remarks> IX PAE Page directory entry. </remarks>
    ///
    [CLSCompliant(false)]
    internal struct PDE {
        private ulong val;

        private const ulong MBZ_MASK      = ~(PE.VALID | PE.WRITEABLE | PE.USER |
                                              PE.WRITETHROUGH | PE.CACHEDISABLE |
                                              PE.ACCESSED | PE.ADDRMASK | PE.NX);

        public bool Valid {
            get { return (val & PE.VALID) != 0; }
            set { val = value ? val | PE.VALID : val & (~PE.VALID); }
        }

        public bool Writeable {
            get { return (val & PE.WRITEABLE) != 0; }
            set { val = value ? val | PE.WRITEABLE : val & (~PE.WRITEABLE); }
        }

        public bool User {
            get { return (val & PE.USER) != 0; }
            set { val = value ? val | PE.USER : val & (~PE.USER); }
        }

        public bool WriteThrough {
            get { return (val & PE.WRITETHROUGH) != 0; }
            set { val = value ? val | PE.WRITETHROUGH : val & (~PE.WRITETHROUGH); }
        }

        public bool CacheDisable {
            get { return (val & PE.CACHEDISABLE) != 0; }
            set { val = value ? val | PE.CACHEDISABLE : val & (~PE.CACHEDISABLE); }
        }

        public bool Accessed {
            get { return (val & PE.ACCESSED) != 0; }
            set { val = value ? val | PE.ACCESSED : val & (~PE.ACCESSED); }
        }

        public ulong Address {
            get { return val & PE.ADDRMASK; }
            set {
                DebugStub.Assert((value & ~PE.ADDRMASK) == 0);
                val = (val & ~(PE.ADDRMASK)) | (value & PE.ADDRMASK);
            }
        }

        public ulong Flags {
            get { return val & ~PE.ADDRMASK; }
            set {
                DebugStub.Assert((value & PE.ADDRMASK) == 0);
                DebugStub.Assert((value & MBZ_MASK) == 0);
                val |= value;
            }
        }

        public void Init() {
            val = 0;
        }
    };

    ///
    /// <remarks> IX PAE 2MB Page directory entry </remarks>
    ///
    [CLSCompliant(false)]
    internal struct PDE_2MB {
        private ulong val;

        private const ulong MBZ_MASK      = ~(PE.VALID | PE.WRITEABLE | PE.USER |
                                              PE.WRITETHROUGH | PE.CACHEDISABLE |
                                              PE.ACCESSED | PE.ADDRMASK | PE.NX);

        public bool Valid {
            get { return (val & PE.VALID) != 0; }
            set { val = value ? val | PE.VALID : val & (~PE.VALID); }
        }

        public bool Writeable {
            get { return (val & PE.WRITEABLE) != 0; }
            set { val = value ? val | PE.WRITEABLE : val & (~PE.WRITEABLE); }
        }

        public bool User {
            get { return (val & PE.USER) != 0; }
            set { val = value ? val | PE.USER : val & (~PE.USER); }
        }

        public bool WriteThrough {
            get { return (val & PE.WRITETHROUGH) != 0; }
            set { val = value ? val | PE.WRITETHROUGH : val & (~PE.WRITETHROUGH); }
        }

        public bool CacheDisable {
            get { return (val & PE.CACHEDISABLE) != 0; }
            set { val = value ? val | PE.CACHEDISABLE : val & (~PE.CACHEDISABLE); }
        }

        public bool Accessed {
            get { return (val & PE.ACCESSED) != 0; }
            set { val = value ? val | PE.ACCESSED : val & (~PE.ACCESSED); }
        }

        public bool Dirty {
            get { return (val & PE.DIRTY) != 0; }
            set { val = value ? val | PE.DIRTY : val & (~PE.DIRTY); }
        }

        public bool Global {
            get { return (val & PE.GLOBAL) != 0; }
            set { val = value ? val | PE.GLOBAL : val & (~PE.GLOBAL); }
        }

        public ulong Address {
            get { return val & PE.ADDRMASK_2MB; }
            set {
                DebugStub.Assert((value & ~PE.ADDRMASK_2MB) == 0);
                val = (val & ~(PE.ADDRMASK_2MB)) | (value & PE.ADDRMASK_2MB);
            }
        }

        public ulong Flags {
            get { return val & ~PE.ADDRMASK; }
            set {
                DebugStub.Assert((value & PE.ADDRMASK) == 0);
                DebugStub.Assert((value & MBZ_MASK) == 0);
                val |= value;
            }
        }

        public void Init() {
            // This bit is always set, obviously
            val = PE.IS2MB;
        }
    };

    ///
    /// <remarks> IX PAE Page directory table. </remarks>
    ///
    [CLSCompliant(false)]
    internal struct PDT
    {
        private PDE entry/*[512]*/;

        public unsafe void Init() {
            fixed (PDE* pEntry = &entry) {
                PDE* pde = pEntry;

                for (int i = 0; i < 512; i++) {
                    pde->Init();
                    pde++;
                }
            }
        }

        public unsafe PDE* this [ uint idx ]
        {
            get {
                DebugStub.Assert(idx < 512);

                fixed (PDE* pEntry = &entry) {
                    return &pEntry[idx];
                }
            }
        }
    };

    ///
    /// <remarks> IX PAE Page directory pointer entry. </remarks>
    ///
    [CLSCompliant(false)]
    internal struct PDPE {
        private ulong val;

        private const ulong MBZ_MASK      = ~(PE.VALID | PE.WRITETHROUGH |
                                              PE.CACHEDISABLE | PE.ADDRMASK);

        public bool Valid {
            get { return (val & PE.VALID) != 0; }
            set { val = value ? val | PE.VALID : val & (~PE.VALID); }
        }

        public bool WriteThrough {
            get { return (val & PE.WRITETHROUGH) != 0; }
            set { val = value ? val | PE.WRITETHROUGH : val & (~PE.WRITETHROUGH); }
        }

        public bool CacheDisable {
            get { return (val & PE.CACHEDISABLE) != 0; }
            set { val = value ? val | PE.CACHEDISABLE : val & (~PE.CACHEDISABLE); }
        }

        public ulong Address {
            get { return val & PE.ADDRMASK; }
            set {
                DebugStub.Assert((value & ~PE.ADDRMASK) == 0);
                val = (val & ~(PE.ADDRMASK)) | (value & PE.ADDRMASK);
            }
        }

        public ulong Flags {
            get { return val & ~PE.ADDRMASK; }
            set {
                DebugStub.Assert((value & PE.ADDRMASK) == 0);
                DebugStub.Assert((value & MBZ_MASK) == 0);
                val |= value;
            }
        }

        public void Init() {
            val = 0;
        }
    };

    ///
    /// <remarks> IX PAE Page directory pointer table. </remarks>
    ///
    [CLSCompliant(false)]
    internal struct PDPT
    {
        private PDPE entry/*[4]*/;

        public unsafe void Init() {
            fixed (PDPE* pEntry = &entry) {
                PDPE* pdpe = pEntry;

                for (int i = 0; i < 4; i++) {
                    pdpe->Init();
                    pdpe++;
                }
            }
        }

        public unsafe PDPE* this [ uint idx ]
        {
            get {
                DebugStub.Assert(idx < 4);

                fixed (PDPE* pEntry = &entry) {
                    return &pEntry[idx];
                }
            }
        }
    };
}
