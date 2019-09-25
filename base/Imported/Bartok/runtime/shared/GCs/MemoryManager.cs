//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs {

    using System.Runtime.CompilerServices;
    using System.Runtime.InteropServices;
#if SINGULARITY_KERNEL
    using Microsoft.Singularity;
    using Microsoft.Singularity.Memory;
    using Sing_MemoryManager = Microsoft.Singularity.Memory.MemoryManager;
#elif SINGULARITY_PROCESS
    using Microsoft.Singularity;
    using Microsoft.Singularity.V1.Services;
#endif

    internal class MemoryManager
    {

        private static UIntPtr allocationGranularity;
        private static UIntPtr totalMemorySize;
        private static UIntPtr operatingSystemSize;

        private static bool inAllocator;

#if SINGULARITY

        internal static unsafe void Initialize()
        {
            allocationGranularity = (UIntPtr)0x10000;
            totalMemorySize = PageTable.PageSize * PageTable.pageTableCount;
            operatingSystemSize = totalMemorySize / 16;
        }

        //////////////////////////////////// Allocation and Free Routines.
        //
        // Allocation is optimized for the case where an allocation starts
        // with a relatively small amount of memory and grows over time.
        // This is exactly the behavior exhibited by stacks and GC heaps.
        //
        // The allocation strategy also works well for large initial
        // allocations.  The strategy would be very inefficient if a very
        // large number of small, completely independent allocations are
        // made.
        //
        // AllocateMemory(size) performs an initial allocation.
        // AllocateMemory(startAddr, size) performs growing allocations.
        //
        internal static unsafe UIntPtr AllocateMemory(UIntPtr size)
        {
            VTable.Assert(PageTable.PageAligned(size));
#if SINGULARITY_KERNEL
            UIntPtr addr = Sing_MemoryManager.KernelAllocate(
                Sing_MemoryManager.PagesFromBytes(size),
                Process.kernelProcess, 0, PageType.Unknown);
#elif SINGULARITY_PROCESS
            UIntPtr addr = PageTableService.Allocate(size);
#endif

#if SINGULARITY_KERNEL
            Kernel.Waypoint((int)size);
            Kernel.Waypoint(811);
#endif // SINGULARITY_KERNEL

            if (addr != UIntPtr.Zero) {
                Util.MemClear(addr, size);
            }
            return addr;
        }

        internal static unsafe bool AllocateMemory(UIntPtr startAddr,
                                                   UIntPtr size)
        {
            VTable.Deny(inAllocator);
            inAllocator = true;
            VTable.Assert(PageTable.PageAligned(startAddr));
            VTable.Assert(PageTable.PageAligned(size));

#if SINGULARITY_KERNEL
            UIntPtr addr = Sing_MemoryManager.KernelExtend(
                startAddr, Sing_MemoryManager.PagesFromBytes(size),
                Process.kernelProcess, PageType.Unknown);
#elif SINGULARITY_PROCESS
            UIntPtr addr = PageTableService.AllocateExtend(startAddr, size);
#endif
            inAllocator = false;
            if (addr != UIntPtr.Zero) {
                Util.MemClear(addr, size);
                return true;
            }
            return false;
        }

        [Inline]
        internal static void FreeMemory(UIntPtr startAddr, UIntPtr size)
        {
#if SINGULARITY_KERNEL
            DebugStub.Assert(Sing_MemoryManager.IsPageAligned(size));
            Sing_MemoryManager.KernelFree(
                startAddr, Sing_MemoryManager.PagesFromBytes(size),
                Process.kernelProcess);
#elif SINGULARITY_PROCESS
            VTable.Assert((size & PageTable.PageMask) == 0);
            PageTableService.Free(startAddr, size);
#endif
        }

        internal static void IgnoreMemoryContents(UIntPtr startAddr,
                                                  UIntPtr regionSize)
        {
            // Since we don't do swapping, we simply ignore this information
        }

        internal static bool QueryMemory(UIntPtr queryAddr,
                                             out UIntPtr regionAddr,
                                             out UIntPtr regionSize)
        {
#if SINGULARITY_KERNEL
            PageType type = Sing_MemoryManager.KernelQuery(
                queryAddr, out regionAddr, out regionSize);
            return (type != PageType.Unknown);
#elif SINGULARITY_PROCESS
            return PageTableService.Query(queryAddr, out regionAddr, out regionSize);
#endif
        }

#else // not SINGULARITY
        [NoBarriers]
        [PreInitRefCounts]
        [NoStackLinkCheckTrans]
        internal static unsafe void Initialize() {
            SYSTEM_INFO systemInfo;
            GetSystemInfo(out systemInfo);
            allocationGranularity =
                new UIntPtr(systemInfo.AllocationGranularity);
            MEMORYSTATUSEX memoryStatus = new MEMORYSTATUSEX();
            memoryStatus.Length = (uint) sizeof(MEMORYSTATUSEX);
            GlobalMemoryStatusEx(ref memoryStatus);
            if (memoryStatus.TotalPhysical <= ((ulong)UIntPtr.MaxValue)) {
                totalMemorySize = (UIntPtr) memoryStatus.TotalPhysical;
            } else {
                // TotalPhysical exceeds UIntPtr.MaxValue running in 32bit
                // mode on a machine with more than 4GB of RAM
                totalMemorySize = UIntPtr.MaxValue;
            }
            // We are just making  a random guess here
            operatingSystemSize = (UIntPtr) 1 << 26;
        }

        // Low-level routines based on Win32

        internal const int PAGE_READWRITE =    0x04;
        internal const int PAGE_EXECUTE_READWRITE = 0x40;
        internal const int PAGE_NOACCESS = 0x01;
        internal const int MEM_COMMIT     =  0x1000;
        internal const int MEM_RESERVE    =  0x2000;
        private const int MEM_DECOMMIT   =  0x4000;
        internal const int MEM_RELEASE    =  0x8000;
        private const int MEM_FREE       = 0x10000;
        private const int MEM_RESET      = 0x80000;

        [StructLayout(LayoutKind.Sequential)]
        private struct MEMORY_BASIC_INFORMATION {
            internal UIntPtr BaseAddress;
            internal UIntPtr AllocationBase;
            internal int  AllocationProtect;
            internal UIntPtr RegionSize;
            internal int  State;
            internal int  Protect;
            internal int  Type;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct SYSTEM_INFO {
            internal ushort ProcessorArchitecture;
            internal ushort Reserved;
            internal uint PageSize;
            internal UIntPtr MinimumApplicationAddress;
            internal UIntPtr MaximumApplicationAddress;
            internal uint ActiveProcessorMask;
            internal uint NumberOfProcessors;
            internal uint ProcessorType;
            internal uint AllocationGranularity;
            internal ushort ProcessorLevel;
            internal ushort ProcessorRevision;
        }

        [StructLayout(LayoutKind.Sequential)]
        private struct MEMORYSTATUSEX {
            internal uint Length;
            internal uint MemoryLoad;
            internal ulong TotalPhysical;
            internal ulong AvailPhysical;
            internal ulong TotalPageFile;
            internal ulong AvailPageFile;
            internal ulong TotalVirtual;
            internal ulong AvailVirtual;
            internal ulong AvailExtendedVirtual;
        }

        // Kernel32.dll functions (via MSVCRT.dll)
        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [NoStackLinkCheck]
        [StackBound(1024)]
        public static unsafe extern void *VirtualAlloc(void *lpAddress,
                                                       UIntPtr dwSize,
                                                       int fIAllocationType,
                                                       int fIProtect);
        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1024)]
        internal static unsafe extern int VirtualFree(void *lpAddress,
                                                      UIntPtr dwSize,
                                                      int dwFreeType);

        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [StackBound(1024)]
        private static unsafe extern UIntPtr VirtualQuery(void *lpAddress, out MEMORY_BASIC_INFORMATION memInfo, UIntPtr dwLength);

        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [NoStackLinkCheck]
        [StackBound(1024)]
        [NoBarriers]
        private static unsafe extern void GetSystemInfo(out SYSTEM_INFO systemInfo);

        [DllImport("BRT")]
        [GCAnnotation(GCOption.NOGC)]
        [NoStackLinkCheck]
        [StackBound(1024)]
        [NoBarriers]
        private static unsafe extern void GlobalMemoryStatusEx(ref MEMORYSTATUSEX memoryStatus);

        // Low-level routines based on the operating system interface

        private static unsafe UIntPtr AllocateMemoryHelper(UIntPtr startAddr,
                                                           UIntPtr size)
        {
            void *result = VirtualAlloc((void *) startAddr,
                                        size, MEM_RESERVE, PAGE_READWRITE);
            VTable.Assert
                (PageTable.Page((UIntPtr) result + size - 1)
                 < PageTable.pageTableCount,
                 "OutOfMemory: MemoryManager: memory doesn't fit in page table");
            if (result != null) {
                Trace.Log(Trace.Area.Page,
                          "VirtualAlloc {0} at {1}",
                          __arglist(size, result));
                VTable.Assert((startAddr == UIntPtr.Zero)
                              || (result == (void *) startAddr));

                void *area = VirtualAlloc(result, size,
                                          MEM_COMMIT, PAGE_READWRITE);
                if (PageTable.halPageDescriptor != null) {
                    PageTable.CreateNewPageTablesIfNecessary(PageTable.Page((UIntPtr)result), PageTable.PageCount(size));
                    PageTable.SetProcess(PageTable.Page((UIntPtr) area),
                                         PageTable.PageCount(size));
                }
                VTable.Assert(result == area);
#if HIMEM
                // This assertion intends only to catch bugs in Bartok. But if
                // the system (windows) frees memory before, the memory
                // may be in low memory, and if we happen to get that
                // memory, this assertion itself may not hold
                VTable.Assert((UIntPtr) result >= PageTable.HIMEMStart, 
                    ("High memory is expected to be allocated in HIMEM mode"));
#endif                
            }
            return new UIntPtr(result);
        }

        internal static unsafe bool AllocateMemory(UIntPtr startAddr,
                                                   UIntPtr size) {
            UIntPtr addr = AllocateMemoryHelper(startAddr, size);
            return addr != UIntPtr.Zero;
        }

        internal static unsafe UIntPtr AllocateMemory(UIntPtr size) {
            return AllocateMemoryHelper(UIntPtr.Zero, size);
        }

        internal static unsafe void FreeMemory(UIntPtr addr, UIntPtr size) {
            Trace.Log(Trace.Area.Page,
                      "VirtualFree {0} at {1}",
                      __arglist(size, addr));
            int success = VirtualFree((void *) addr, UIntPtr.Zero,
                                      MEM_RELEASE);
            VTable.Assert(success != 0);
        }

        // Indicate that we still own the memory but that we don't care
        // about the content of the memory.  The virtual memory system
        // does not have to write the memory to the swap file in order
        // to reuse the physical memory for other purposes.
        internal static unsafe void IgnoreMemoryContents(UIntPtr startAddr,
                                                         UIntPtr regionSize)
        {
            Trace.Log(Trace.Area.Page,
                      "VirtualAlloc-Reset {0} at {1}",
                      __arglist(regionSize, startAddr));
            void * result = VirtualAlloc((void *) startAddr, regionSize,
                                         MEM_RESET, PAGE_READWRITE);
            VTable.Assert(result == (void *) startAddr,
                          "VirtualAlloc MEM_RESET failed");
        }

        internal static unsafe bool QueryMemory(UIntPtr queryAddr,
                                                out UIntPtr regionAddr,
                                                out UIntPtr regionSize)
        {
            VTable.Assert(PageTable.PageAligned(queryAddr));
            MEMORY_BASIC_INFORMATION memInfo;
            UIntPtr size = (UIntPtr) sizeof(MEMORY_BASIC_INFORMATION);
            UIntPtr data = VirtualQuery((void *) queryAddr, out memInfo, size);
            Trace.Log(Trace.Area.Page,
                      "VirtualQuery {0}: base={1} size={2}",
                      __arglist(queryAddr, memInfo.AllocationBase,
                                memInfo.RegionSize));
            if (data == 0) {
                // queryAddr is a kernel-mode pointer
                regionAddr = queryAddr;
                regionSize = (UIntPtr) sizeof(int);
                return false;
            } else {
                VTable.Assert(data == size &&
                              memInfo.BaseAddress == queryAddr);
                regionAddr = memInfo.AllocationBase;
                regionSize = (queryAddr - regionAddr) + memInfo.RegionSize;
                return (memInfo.State != MEM_FREE);
            }
        }
#endif

        internal static UIntPtr OperatingSystemCommitSize {
            get {
                return allocationGranularity;
            }
        }

        // We are just guessing here
        internal static UIntPtr MemorySize {
            get { return totalMemorySize; }
        }

        // We are just making an educated guess here
        internal static UIntPtr OperatingSystemSize {
            get { return operatingSystemSize; }
        }

    }

}
