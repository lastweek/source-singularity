////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MemoryManager.cs - Main entry points for OS memory management
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Threading;
using System.GCs;

using Microsoft.Singularity;
using Microsoft.Singularity.Hal;
using Microsoft.Bartok.Runtime;

namespace Microsoft.Singularity.Memory
{
    [NoCCtor]
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced from halkd.cpp")]
    public class MemoryManager {

        /////////////////////////////////////
        // STATIC FIELDS
        /////////////////////////////////////

        private static PhysicalAddress IOMemoryBaseAddr;
        private static PhysicalHeap KernelIOMemoryHeap;
        private static VirtualMemoryRange_struct KernelRange;
        private static VirtualMemoryRange KernelRangeWrapper;

        [AccessedByRuntime("referenced from halkd.cpp")]
        private static bool isInitialized;

        private static bool useAddressTranslation;

        public static bool UseAddressTranslation
        {
            get { return useAddressTranslation; }
        }

        /////////////////////////////////////
        // CONSTANTS
        /////////////////////////////////////
        // 4K pages!
        internal const byte  PageBits = 12;
        internal const uint  PageSize = 1 << PageBits;
        internal const uint  PageMask = PageSize - 1;

        //
        // These constants define the layout of the virtual-page tables
        // present in each VirtualMemoryRange (and that correspond to
        // the FlatPages page table)
        //
        internal const uint    SystemPage          = 0xffff0000u;
        internal const uint    SystemPageMask      = 0xffff000fu;
        internal const uint    ProcessPageMask     = 0xffff0000u;
        internal const uint    ExtraMask           = 0x0000fff0u;
        internal const uint    TypeMask            = 0x0000000fu;

        internal const uint    PageUnknown         = SystemPage + (uint)PageType.Unknown;
        internal const uint    PageShared          = SystemPage + (uint)PageType.Shared;
        internal const uint    PageFree            = SystemPage + (uint)PageType.Unallocated;
        internal const uint    PageFreeFirst       = PageFree + 0xfff0;

        internal const uint    KernelPage          = 0x00010000u;

        internal const uint    KernelPageNonGC     = KernelPage + (uint)PageType.NonGC;
        internal const uint    KernelPageImage     = KernelPage + (uint)PageType.System;
        internal const uint    KernelPageStack     = KernelPage + (uint)PageType.Stack;

        //
        // we must make a determination of the "useAddressTranslation" arguments existence
        // before memory management is setup -- so do this rudely using the buffer in Platform.
        //
        // If we find it in the cmdline then we actually need to remove it before continuing
        // or the shell will eventually attempt to execute it as a command.
        //
        [NoHeapAllocation]
        private unsafe static bool UseAddressTranslationInCmdLine()
        {
            const string uatKey = "/useAddressTranslation";
            char* cmdPtr = Platform.ThePlatform.CommandLine;

            fixed (char* keyPtr = uatKey) {
                if (cmdPtr != null) {
                    while (*cmdPtr != 0) {
                        char* cp = cmdPtr;
                        char* kp = keyPtr;
                        while (*cp != 0 && *kp != 0) {
                            if (*cp != *kp)
                                break;
                            ++cp; ++kp;
                        }
                        if (*kp == 0) {
                            while (*cp != 0) {
                                *cmdPtr++ = *cp++;
                            }
                            *cmdPtr = '\0';
                            return true;
                        }
                        else {
                            ++cmdPtr;
                        }
                    }
                }
            }
            return false;
        }

        /////////////////////////////////////
        // PUBLIC METHODS
        /////////////////////////////////////

        internal static void Initialize()
        {
            DebugStub.WriteLine("Initializing memory subsystem...");

            // Only allow paging in HALs which support running in Ring 0
            // but always force paging in the HIP builds for compatibility
#if !PAGING
            useAddressTranslation = UseAddressTranslationInCmdLine();
#else
            useAddressTranslation = true;
#endif

            if (useAddressTranslation) {
                DebugStub.WriteLine("Using address translation...\n");
                Platform p = Platform.ThePlatform;

                // Set up the hardware-pages table and reserve a range for
                // I/O memory

                IOMemoryBaseAddr = PhysicalPages.Initialize(Platform.IO_MEMORY_SIZE);

                // Set up the I/O memory heap
                KernelIOMemoryHeap = new PhysicalHeap((UIntPtr)IOMemoryBaseAddr.Value,
                                                      (UIntPtr)(IOMemoryBaseAddr.Value + Platform.IO_MEMORY_SIZE));

                // Set up virtual memory. ** This enables paging ** !
                VMManager.Initialize();

                // Set up the kernel's memory ranges.
                //
                // The kernel's general-purpose range is special because
                // it *describes* low memory as well as the GC range proper
                // so the kernel's GC doesn't get confused by pointers to
                // static data in the kernel image.
                KernelRange = new VirtualMemoryRange_struct(
                    VMManager.KernelHeapBase,
                    VMManager.KernelHeapLimit,
                    UIntPtr.Zero,
                    VMManager.KernelHeapLimit,
                    null); // no concurrent access to page descriptors yet

                // Mark the kernel's special areas. First, record the kernel memory.
                if (p.KernelDllSize != 0) {
                    UIntPtr kernelDllLimit = p.KernelDllBase + p.KernelDllSize;

                    KernelRange.SetRange(p.KernelDllBase, kernelDllLimit,
                        MemoryManager.KernelPageNonGC);
                }

                // Record the boot allocated kernel memory.
                if (p.BootAllocatedMemorySize != 0) {
                    UIntPtr bootAllocatedMemoryLimit = p.BootAllocatedMemory + p.BootAllocatedMemorySize;

                    KernelRange.SetRange(p.BootAllocatedMemory, bootAllocatedMemoryLimit,
                        MemoryManager.KernelPageNonGC);
                }

                // Set stack page for CPU 0
                KernelRange.SetRange(Platform.BootCpu.KernelStackLimit,
                         (Platform.BootCpu.KernelStackBegin - Platform.BootCpu.KernelStackLimit),
                         MemoryManager.KernelPageStack);

                DebugStub.WriteLine("MemoryManager initialized with {0} physical pages still free",
                                    __arglist(PhysicalPages.GetFreePageCount()));
                KernelRange.Dump("Initialized");

                isInitialized = true;
            }
            else {
                FlatPages.Initialize();
                DebugStub.WriteLine("KernelBaseAddr: {0:x8} KernelLimitAddr {1:x8}",
                                    __arglist(KernelBaseAddr,
                                              KernelBaseAddr + BytesFromPages(KernelPageCount)));
            }
        }

        internal static void Finalize()
        {
            if (useAddressTranslation) {
                VMManager.Finalize();
            }
        }

        internal static unsafe void PostGCInitialize()
        {
            if (useAddressTranslation) {
                VMManager.PostGCInitialize();

                // Create the wrapper for the kernel range. The fixed
                // statement is safe since KernelRange is a static
                // struct.
                fixed (VirtualMemoryRange_struct* pKernelRange = &KernelRange)
                {
                    KernelRangeWrapper = new VirtualMemoryRange(pKernelRange,
                                                                ProtectionDomain.DefaultDomain);
                }
            }
        }

        /// <summary>
        /// SetRange - provide access to the GC PageTable
        /// </summary>
        /// <param name="start">Beginning address</param>
        /// <param name="bytes">Number of bytes</param>
        /// <param name="tag">PageType with which to mark</param>
        [NoHeapAllocation]
        internal static void SetRange(UIntPtr start, UIntPtr bytes, uint tag)
        {
            if (useAddressTranslation) {
                KernelRange.SetRange(start, bytes, tag);
            }
            else {
                FlatPages.SetRange(start, bytes, tag);
            }
        }

        /////////////////////////////////////
        // PUBLIC PAGING-SPECIFIC METHODS
        /////////////////////////////////////

        internal static unsafe VirtualMemoryRange GetKernelRange()
        {
            DebugStub.Assert(KernelRangeWrapper != null);
            return KernelRangeWrapper;
        }

        //
        // Get a new physical page and map it to the provided virtual address
        //
        private static bool CommitAndMapNewPage(UIntPtr virtualAddr,
                                                ProtectionDomain inDomain)
        {
            DebugStub.Assert(IsPageAligned(virtualAddr));
            PhysicalAddress newPage = PhysicalPages.AllocPage();

            if (newPage == PhysicalAddress.Null) {
                // Failed.
                return false;
            }

            VMManager.MapPage(newPage, virtualAddr, inDomain);
            return true;
        }

        //
        // Get and map multiple new pages. On failure, no pages are allocated.
        //
        internal static bool CommitAndMapRange(UIntPtr virtualAddr,
                                               UIntPtr limitAddr,
                                               ProtectionDomain inDomain)
        {
            DebugStub.Assert(IsPageAligned(virtualAddr));
            DebugStub.Assert(IsPageAligned(limitAddr));

            for ( UIntPtr step = virtualAddr;
                  step < limitAddr;
                  step += PageSize) {

                if (!CommitAndMapNewPage(step, inDomain)) {
                    // Uh oh; we failed.
                    for ( UIntPtr unmapStep = virtualAddr;
                          unmapStep < virtualAddr;
                          unmapStep += PageSize) {

                        UnmapAndReleasePage(unmapStep);
                    }

                    return false;
                }
            }

            return true;
        }

        //
        // Unmap the page at the provided virtual address and release its
        // underlying physical page
        //
        internal static void UnmapAndReleasePage(UIntPtr virtualAddr)
        {
            DebugStub.Assert(VMManager.IsPageMapped(virtualAddr),
                             "Trying to unmap an unmapped page");
            PhysicalAddress phys = VMManager.UnmapPage(virtualAddr);
            DebugStub.Assert(phys != PhysicalAddress.Null);
            PhysicalPages.FreePage(phys);
        }

        //
        // Unmap and release an entire range
        //
        internal static void UnmapAndReleaseRange(UIntPtr virtualAddr,
                                                  UIntPtr limitAddr)
        {
            DebugStub.Assert(IsPageAligned(virtualAddr));
            DebugStub.Assert(IsPageAligned(limitAddr));

            for ( UIntPtr step = virtualAddr;
                  step < limitAddr;
                  step += PageSize) {

                UnmapAndReleasePage(step);
            }
        }


        /////////////////////////////////////
        // KERNEL MEMORY OPERATIONS
        /////////////////////////////////////

        internal static PhysicalAddress IOMemoryBase {
            get {
                return IOMemoryBaseAddr;
            }
        }

        private static bool InRange(UIntPtr value, UIntPtr lower, UIntPtr max)
        {
            return value >= lower && value <= max;
        }

        //
        // Calculate the size of physical memory from the boottime
        // information -- SHOULD ONLY BE CALLED FROM INITIALIZE
        //
        internal unsafe static void PhysicalMemoryLimits(out UIntPtr lowerAddress,
                                                         out UIntPtr upperAddress)
        {
            Platform p = Platform.ThePlatform;
            uint i;

            int cpuId = p.ApicId;
            uint j;
            DebugStub.WriteLine("MemoryManager.Initialize: Memory Map: Apic ID {0}\n",
                                __arglist(cpuId));

            UIntPtr baseSmapAddress = UIntPtr.MaxValue;
            UIntPtr maxSmapAddress = UIntPtr.Zero;

            // First pass over SMAP, find the highest RAM address
            unsafe {
                SMAPINFO* smap = (SMAPINFO*)p.Smap;
                for (i = 0; i < p.SmapCount; i++) {
                    uint smapType = (uint)smap[i].type;
                    if (smapType != SMAPINFO.AddressTypeFree &&
                        smapType != SMAPINFO.AddressTypeKernelStack) {
                        continue;
                    }

                    if (smap[i].addr < baseSmapAddress) {
                        baseSmapAddress = smap[i].addr;
                    }
                    if ((smap[i].addr + smap[i].size) > maxSmapAddress) {
                        maxSmapAddress = smap[i].addr + smap[i].size;
                    }

                    DebugStub.WriteLine("{0}: {1,8:x8} - {2,8:x8}, type={3,8:x8}",
                                        __arglist(i, smap[i].addr, smap[i].addr + smap[i].size, smap[i].type));

                    unchecked {
                        Tracing.Log(Tracing.Debug,
                                    "   [{0,8:x8}..{1,8:x8}] = {2,8:x8}",
                                    (UIntPtr)(uint)smap[i].addr,
                                    (UIntPtr)(uint)(smap[i].addr + smap[i].size),
                                    (UIntPtr)(uint)smap[i].type);
                    }
                }
            }

            lowerAddress = baseSmapAddress;
            upperAddress = maxSmapAddress;

            // Verify kernel and boot memory are corretly reporting within the SMAP range
            // it is a hal error to configure this otherwise.

            //DebugStub.Assert(p.KernelDllBase + p.KernelDllSize <= upperAddress);
            //DebugStub.Assert(p.BootAllocatedMemory + p.BootAllocatedMemorySize <= upperAddress);
        }

        [AccessedByRuntime("referenced from halkd.cpp")]
        internal static UIntPtr KernelMapPhysicalMemory(PhysicalAddress physStart,
                                                        UIntPtr numBytes)
        {
            if (useAddressTranslation) {
                UIntPtr permaLoc = VMManager.TranslatePhysicalRange(physStart, numBytes);

                if (permaLoc != UIntPtr.Zero) {
                    // This location has a permanent mapping
                    return permaLoc;
                }
                else {
                    // This location must be mapped on the fly
                    return VMManager.MapPhysicalMemory(KernelRangeWrapper,
                                                       Process.kernelProcess,
                                                       physStart, numBytes);
                }
            }
            else {
                // identity map without paging
                return unchecked((UIntPtr)physStart.Value);
            }
        }

        [AccessedByRuntime("referenced from halkd.cpp")]
        internal static void KernelUnmapPhysicalMemory(UIntPtr startAddr,
                                                       UIntPtr limitAddr)
        {
            if (useAddressTranslation) {
                if (VMManager.IsPermaMapped(startAddr, limitAddr)) {
                    return; // nothing to do
                }
                else {
                    VMManager.UnmapPhysicalMemory(KernelRangeWrapper,
                                                  Process.kernelProcess,
                                                  startAddr, limitAddr);
                }
            }
            // else do nothing
        }

        //
        // This is called to allocate memory for a stack, either an initial stack
        // or a dynamically allocated stack chunk.
        //
        internal static UIntPtr StackAllocate(UIntPtr numPages, Process process,
                                                uint extra, bool kernelAllocation, bool initialStack)
        {
            UIntPtr result = UIntPtr.Zero;

            if (useAddressTranslation) {
                if (KernelRangeWrapper != null) {
                    result = KernelRangeWrapper.Allocate(numPages, process, extra, PageType.Stack);
                }
                else {
                    // Very early in the initialization sequence; ASSUME there is not
                    // yet any concurrent access to paging descriptors, and allocate
                    // memory without a paging-descriptor lock.
                    result = KernelRange.Allocate(numPages, process, extra, PageType.Stack, null);
                }
            }
            else {
                result = FlatPages.StackAllocate(BytesFromPages(numPages),
                                            UIntPtr.Zero,
                                            MemoryManager.PageSize,
                                            process, extra, kernelAllocation, initialStack);
            }

            if (kernelAllocation && result == UIntPtr.Zero) {
                DebugStub.WriteLine("******** Kernel OOM on Stack ********");

                //
                // Our kernel runtime can not handle this right now, so rather than
                // return a null which will show up as a cryptic lab failure, always
                // drop to the debugger.
                //
                // Note: Reservations should avoid this, so this is an indication that
                //       something has gone wrong in our reservation policy and estimates
                //       of kernel stack usage.
                //
                DebugStub.Break();
            }

            return result;
        }

        internal static void StackFree(UIntPtr startAddr, UIntPtr numPages, Process process, bool kernelAllocation, bool initialStack)
        {
            if (useAddressTranslation) {
                KernelRange.Free(startAddr, numPages, process);
            }
            else {
                FlatPages.StackFree(startAddr, MemoryManager.BytesFromPages(numPages), process, kernelAllocation, initialStack);
            }
        }

        internal static UIntPtr KernelAllocate(UIntPtr numPages, Process process,
                                                uint extra, PageType type)
        {
            UIntPtr result = UIntPtr.Zero;

            if (useAddressTranslation) {
                if (KernelRangeWrapper != null) {
                    result = KernelRangeWrapper.Allocate(numPages, process, extra, type);
                }
                else {
                    // Very early in the initialization sequence; ASSUME there is not
                    // yet any concurrent access to paging descriptors, and allocate
                    // memory without a paging-descriptor lock.
                    result = KernelRange.Allocate(numPages, process, extra, type, null);
                }
            }
            else {
                result = FlatPages.Allocate(BytesFromPages(numPages),
                                            UIntPtr.Zero,
                                            MemoryManager.PageSize,
                                            process, extra, type);
            }

            if (result == UIntPtr.Zero) {
                DebugStub.WriteLine("******** Kernel OOM on Heap ********");

                //
                // Our kernel runtime can not handle this right now, so rather than
                // return a null which will show up as a cryptic lab failure, always
                // drop to the debugger.
                //
                DebugStub.Break();
            }

            return result;
        }

        internal static UIntPtr KernelExtend(UIntPtr addr, UIntPtr numPages, Process process,
                                             PageType type)
        {
            //
            // We do not report failure here since callers will default to
            // KernelAllocate and copy if it can't extend the range
            //
            if (useAddressTranslation) {
                // TODO: Extend not yet implemented
                DebugStub.Break();
                return UIntPtr.Zero;
            }
            else {
                return FlatPages.AllocateExtend(addr, BytesFromPages(numPages), process, 0, type);
            }
        }

        internal static PageType KernelQuery(UIntPtr startAddr,
                                             out UIntPtr regionAddr,
                                             out UIntPtr regionSize)
        {
            if (useAddressTranslation) {
                // TODO: Query not yet implemented
                DebugStub.Break();
                regionAddr = UIntPtr.Zero;
                regionSize = UIntPtr.Zero;
                return PageType.Unknown;
            }
            else {
                return FlatPages.Query(startAddr, Process.kernelProcess, out regionAddr,
                                       out regionSize);
            }
        }

        [NoStackLinkCheckTrans]
        [NoStackOverflowCheck]
        internal static void KernelFree(UIntPtr startAddr, UIntPtr numPages, Process process)
        {
            if (useAddressTranslation) {
                KernelRange.Free(startAddr, numPages, process);
            }
            else {
                FlatPages.Free(startAddr, MemoryManager.BytesFromPages(numPages), process);
            }
        }

        internal static UIntPtr AllocateIOMemory(UIntPtr limitAddr,
                                                 UIntPtr bytes,
                                                 UIntPtr alignment,
                                                 Process process)
        {
            UIntPtr result = UIntPtr.Zero;

            if (useAddressTranslation) {
                result = KernelIOMemoryHeap.Allocate(limitAddr, bytes, alignment, process);
            }
            else {
                if (limitAddr > 0) {
                    result = FlatPages.AllocateBelow(limitAddr, bytes, alignment, process, 0, PageType.NonGC);
                }
                else {
                    result = FlatPages.Allocate(bytes, bytes, alignment, process, 0, PageType.NonGC);
                }
            }

            if (result == UIntPtr.Zero) {
                DebugStub.WriteLine("******** Kernel OOM on IoMemory ********");

                //
                // Our kernel runtime can not handle this right now, so rather than
                // return a null which will show up as a cryptic lab failure, always
                // drop to the debugger.
                //
                DebugStub.Break();
            }

            return result;
        }

        internal static void FreeIOMemory(UIntPtr addr, UIntPtr size, Process process)
        {
            if (useAddressTranslation) {
                KernelIOMemoryHeap.Free(addr, size, process);
            }
            else {
                FlatPages.Free(addr, size, process);
            }
        }

        internal static UIntPtr KernelBaseAddr
        {
            get {
                return useAddressTranslation ? KernelRange.BaseAddress : UIntPtr.Zero;
            }
        }

        internal static unsafe uint* KernelPageTable
        {
            get {
                return useAddressTranslation ? KernelRange.PageTable : FlatPages.PageTable;
            }
        }

        internal static UIntPtr KernelPageCount
        {
            get {
                return useAddressTranslation ? KernelRange.PageCount : FlatPages.PageCount;
            }
        }

        //
        // This returns total (kernel + SIP) memory usage information
        //
        internal static void GetUsageStatistics(out ulong allocatedCount,
                                               out ulong allocatedBytes,
                                               out ulong freedCount,
                                               out ulong freedBytes,
                                               out ulong kernelHeapReservation)
        {
            if (useAddressTranslation) {
                ProtectionDomain.CurrentDomain.UserRange.GetUsageStatistics(
                    out allocatedCount,
                    out allocatedBytes,
                    out freedCount,
                    out freedBytes);

                    kernelHeapReservation = 0;
            }
            else {
                MemoryReservations.GetUsageStatistics(out allocatedCount, out allocatedBytes,
                             out freedCount, out freedBytes, out kernelHeapReservation);
            }
        }

        //
        // Return stack usage as raw counters
        //
        [NoHeapAllocation]
        internal static void GetStackUsage(
            out ulong kernelStackCount,
            out ulong kernelStackReturnCount,
            out ulong kernelStackBytes,
            out ulong kernelStackReturnBytes,
            out ulong kernelStackReservation,
            out ulong userStackCount,
            out ulong userStackReturnCount,
            out ulong userStackBytes,
            out ulong userStackReturnBytes,
            out ulong userStackReservation
            )
        {
            MemoryReservations.GetStackUsage(
                out kernelStackCount,
                out kernelStackReturnCount,
                out kernelStackBytes,
                out kernelStackReturnBytes,
                out kernelStackReservation,
                out userStackCount,
                out userStackReturnCount,
                out userStackBytes,
                out userStackReturnBytes,
                out userStackReservation
                );
        }

        /////////////////////////////////////
        // USER MEMORY OPERATIONS
        /////////////////////////////////////

        internal static UIntPtr UserBaseAddr
        {
            get {
#if false
                return useAddressTranslation
                    ? ProtectionDomain.CurrentDomain.UserRange.BaseAddress
                    : UIntPtr.Zero;
#endif
                return useAddressTranslation
                    ? ProtectionDomain.CurrentDomain.UserRange.BaseAddress
                    : UIntPtr.Zero;

            }
        }

        internal static UIntPtr UserMapPhysicalMemory(PhysicalAddress physStart,
                                                      UIntPtr numBytes)
        {
            return useAddressTranslation
                ? VMManager.MapPhysicalMemory(ProtectionDomain.CurrentDomain.UserRange,
                                              Thread.CurrentProcess, physStart, numBytes)
                : unchecked((UIntPtr)physStart.Value);
        }

        internal static void UserUnmapPhysicalMemory(UIntPtr startAddr,
                                                     UIntPtr limitAddr)
        {
            if (useAddressTranslation) {
                VMManager.UnmapPhysicalMemory(ProtectionDomain.CurrentDomain.UserRange,
                                              Thread.CurrentProcess, startAddr, limitAddr);
            }
        }

        //
        // This is invoked on SIP OOM to "fail-fast" the SIP
        //
        internal static void UserMemoryFailure()
        {
            DebugStub.WriteLine("******** SIP OOM on Heap, Failing Fast ********");

            // This does not make a stack transition record
            Thread.CurrentProcess.Stop((int)System.ProcessExitCode.ErrorDefault);

             // Should not return
            DebugStub.Break();
        }

        internal static UIntPtr UserAllocate(UIntPtr numPages,
                                             Process process,
                                             uint extra,
                                             PageType type)
        {
            UIntPtr result = UIntPtr.Zero;

            if (useAddressTranslation) {
                result = ProtectionDomain.CurrentDomain.UserRange.Allocate(
                    numPages, process, extra, type);
            }
            else {
                result = FlatPages.Allocate(BytesFromPages(numPages),
                                            UIntPtr.Zero,
                                            MemoryManager.PageSize,
                                            process, extra, type);
            }

            if (result == UIntPtr.Zero) {
                UserMemoryFailure();
            }

            return result;
        }

        internal static UIntPtr UserExtend(UIntPtr addr, UIntPtr numPages, Process process,
                                           PageType type)
        {
            UIntPtr result = UIntPtr.Zero;

            if (useAddressTranslation) {
                // TODO: Extend NYI
                DebugStub.Break();
                result = UIntPtr.Zero;
            }
            else {
                result = FlatPages.AllocateExtend(addr, BytesFromPages(numPages), process, 0, type);
            }

            if (result == UIntPtr.Zero) {
                UserMemoryFailure();
            }

            return result;
        }

        internal static void UserFree(UIntPtr addr, UIntPtr numPages, Process process)
        {
            if (useAddressTranslation) {
                ProtectionDomain.CurrentDomain.UserRange.Free(addr, numPages, process);
            }
            else {
                FlatPages.Free(addr, BytesFromPages(numPages), process);
            }
        }

        internal static PageType UserQuery(UIntPtr startAddr,
                                           out UIntPtr regionAddr,
                                           out UIntPtr regionSize)
        {
            if (useAddressTranslation) {
                // TODO: Query NYI
                DebugStub.Break();
                regionAddr = UIntPtr.Zero;
                regionSize = UIntPtr.Zero;
                return PageType.Unknown;
            }
            else {
                return FlatPages.Query(startAddr, Thread.CurrentProcess,
                                       out regionAddr, out regionSize);
            }
        }

        internal static UIntPtr FreeProcessMemory(Process process)
        {
            if (useAddressTranslation) {
                return ProtectionDomain.CurrentDomain.UserRange.FreeAll(process);
            }
            else {
                return FlatPages.FreeAll(process);
            }
        }

        internal static unsafe uint* UserPageTable
        {
            get {
                return useAddressTranslation
                    ? ProtectionDomain.CurrentDomain.UserRange.PageTable
                    : FlatPages.PageTable;
            }
        }

        internal static UIntPtr UserPageCount
        {
            get {
                return useAddressTranslation
                    ? ProtectionDomain.CurrentDomain.UserRange.PageCount
                    : FlatPages.PageCount;
            }
        }

        /////////////////////////////////////
        // DIAGNOSTICS
        /////////////////////////////////////

        public static ulong GetFreePhysicalMemory()
        {
            return useAddressTranslation
                ? PhysicalPages.GetFreeMemory()
                : (ulong)FlatPages.GetFreeMemory();
        }

        public static ulong GetUsedPhysicalMemory()
        {
            return useAddressTranslation
                ? PhysicalPages.GetUsedMemory()
                : (ulong)FlatPages.GetUsedMemory();
        }

        public static ulong GetMaxPhysicalMemory()
        {
            return useAddressTranslation
                ? PhysicalPages.GetMaxMemory()
                : (ulong)FlatPages.GetMaxMemory();
        }

        internal static void GetUserStatistics(out ulong allocatedCount,
                                               out ulong allocatedBytes,
                                               out ulong freedCount,
                                               out ulong freedBytes)
        {
            if (useAddressTranslation) {
                ProtectionDomain.CurrentDomain.UserRange.GetUsageStatistics(
                    out allocatedCount,
                    out allocatedBytes,
                    out freedCount,
                    out freedBytes);
            }
            else {
                MemoryReservations.GetUserStatistics(out allocatedCount, out allocatedBytes,
                             out freedCount, out freedBytes);
            }
        }

        // Simpler overload
        internal static UIntPtr AllocateIOMemory(UIntPtr bytes, Process process)
        {
            return AllocateIOMemory(UIntPtr.Zero, bytes, PageSize, process);
        }

        /////////////////////////////////////
        // PUBLIC UTILITY METHODS
        /////////////////////////////////////

        [Inline]
        [NoHeapAllocation]
        internal static ulong PagePad(ulong addr) {
            return ((addr + PageMask) & ~((ulong)PageMask));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr PagePad(UIntPtr addr)
        {
            return ((addr + PageMask) & ~PageMask);
        }

        [Inline]
        [NoHeapAllocation]
        internal static ulong BytesNotAligned(ulong data, ulong size)
        {
            return ((data) & (size - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr BytesNotAligned(UIntPtr data, UIntPtr size)
        {
            return ((data) & (size - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr Pad(UIntPtr data, UIntPtr align)
        {
            return ((data + align - 1) & ~(align - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr Trunc(UIntPtr addr, UIntPtr align)
        {
            return addr - BytesNotAligned(addr, align);
        }

        [Inline]
        [NoHeapAllocation]
        internal static ulong Trunc(ulong addr, ulong align)
        {
            return addr - BytesNotAligned(addr, align);
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr PageTrunc(UIntPtr addr)
        {
            return (addr & ~PageMask);
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr Align(UIntPtr data, UIntPtr size)
        {
            return ((data) & ~(size - 1));
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr PageFromAddr(UIntPtr addr)
        {
            return (addr >> PageBits);
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr AddrFromPage(UIntPtr pageIdx)
        {
            return (pageIdx  << PageBits);
        }

        [Inline]
        [NoHeapAllocation]
        internal static ulong PagesFromBytes(ulong size)
        {
            return ((size + PageMask) >> PageBits);
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr PagesFromBytes(UIntPtr size)
        {
            return ((size + PageMask) >> PageBits);
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr BytesFromPages(UIntPtr pages)
        {
            return (UIntPtr)(pages << PageBits);
        }

        [Inline]
        [NoHeapAllocation]
        internal static UIntPtr BytesFromPages(ulong pages)
        {
            return (UIntPtr)(pages << PageBits);
        }

        [Inline]
        [NoHeapAllocation]
        [AccessedByRuntime("referenced from halkd.cpp")]
        internal static UIntPtr PageAlign(UIntPtr addr) {
            return (addr & ~PageMask);
        }

        [Inline]
        [NoHeapAllocation]
        internal static bool IsPageAligned(UIntPtr addr)
        {
            return ((addr & PageMask) == 0);
        }

        [Inline]
        [NoHeapAllocation]
        internal static bool IsPageAligned(ulong addr)
        {
            return ((addr & (ulong)PageMask) == 0);
        }
    }
}

