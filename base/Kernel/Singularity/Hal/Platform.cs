// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity.Isal;
using Microsoft.Singularity.Hal;
using Microsoft.Singularity.Io;

namespace Microsoft.Singularity.Hal
{
    //
    // Platform is the basic abstraction of the HAL execution platform
    //
    // Part of the platform consts
    //
    [CLSCompliant(false)]
    [AccessedByRuntime("referenced in c++", AllFields = true)]
    [StructLayout(LayoutKind.Sequential, Pack=4)]
    public class Platform
    {
        ///////////////////////////////////////////////////////////////////////
        // Constants: these remain the same on all platforms.
        ///////////////////////////////////////////////////////////////////////

        // TODO: Fix case of constants to camel case

        [AccessedByRuntime("referenced in c++")]
        // 4KB is currently the only supported size
        internal const uint PAGE_SIZE           = 0x00001000; // 4KB

        // This is the ABI Stub (MpSyscalls.x86)
        [AccessedByRuntime("referenced in c++")]
        internal const uint MP_ABI_BASE         = 0x00600000;

        //
        // These constants control the gross layout of *virtual*
        // memory
        //

        // The physical address and extent of the high-memory
        // range to map into the Kernel space, and mark
        // "uncached". This window is for communicating with
        // hardware.
        [AccessedByRuntime("referenced in c++")]
        public const uint UNCACHED_PHYSICAL     = 0xFE000000;
        [AccessedByRuntime("referenced in c++")]
        public const uint UNCACHED_MAPPED       = 0x02000000;

        // This is the amount of *contiguous, physical* memory
        // to reserve at boot for use as I/O memory
        public const uint IO_MEMORY_SIZE        = 0x00800000; // 8MB

        // This determines where the kernel/user boundary is.
        // Currently, it needs to be multiple of 1GB.
        [AccessedByRuntime("referenced in c++")]
        internal const uint KERNEL_BOUNDARY     = 0x40000000; // 1GB

        // This determines the maximum virtual address
        // we will use. Setting this to less than the
        // machine's maximum pointer size can reduce the
        // overhead of paging structures.
        //
        // NOTE: we are not currently safe to use the top
        // bit of addresses (because of the "mark" bit in the
        // multi-use word header), so restrict ourselves to the
        // bottom 2GB.
        [AccessedByRuntime("referenced in c++")]
        public const uint MAX_VIRTUAL_ADDR      = 0x80000000; // 2GB

        // Exit Codes:
        [AccessedByRuntime("referenced in c++")]
        internal const int EXIT_AND_RESTART     = 0x1fff;
        [AccessedByRuntime("referenced in c++")]
        internal const int EXIT_AND_SHUTDOWN    = 0x1ffe;
        [AccessedByRuntime("referenced in c++")]
        internal const int EXIT_AND_WARMBOOT    = 0x1ffd;
        [AccessedByRuntime("referenced in c++")]
        internal const int EXIT_AND_HALT        = 0x1ffc;

        ///////////////////////////////////////////////////////////////////////
        // Boot configuration information: this is all filled out by the loader
        ///////////////////////////////////////////////////////////////////////

        // Size of instance; this is a versioning/consistency check
        [AccessedByRuntime("referenced in c++")]
        public readonly int         Size;

#if ISA_IX64

        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     Dummy;

#endif

        [AccessedByRuntime("referenced in c++")]
        public readonly uint        BootYear;
        [AccessedByRuntime("referenced in c++")]
        public readonly uint        BootMonth;
        [AccessedByRuntime("referenced in c++")]
        public readonly uint        BootDay;
        [AccessedByRuntime("referenced in c++")]
        public readonly uint        BootHour;
        [AccessedByRuntime("referenced in c++")]
        public readonly uint        BootMinute;
        [AccessedByRuntime("referenced in c++")]
        public readonly uint        BootSecond;

        // Max # of CPUs allowed. !!! is this a long term thing? Should it be a constant?
        [AccessedByRuntime("referenced in c++")]
        public readonly int         CpuMaxCount;
        [AccessedByRuntime("referenced in c++")]
        public readonly int         CpuRealCount;

        // Warm boot count (0 = cold boot, 1 = first warm boot, etc.)
        [AccessedByRuntime("referenced in c++")]
        public readonly int         BootCount;

        // Description of memory
        // @todo: this is a simple description of devices in the physical address space.
        // Eventually we want a richer way for HAL to communicate the memory layout to
        // S, rather than having S make assumptions about where HAL is and isn't using memory.
        [AccessedByRuntime("referenced in c++")]
        // Field must be integral for 16-bit boot code
        public readonly UIntPtr     Smap32;

        public unsafe Microsoft.Singularity.SMAPINFO *Smap {
            [NoHeapAllocation]
                get {
                return (Microsoft.Singularity.SMAPINFO *) Smap32;
            }
        }

        [AccessedByRuntime("referenced in c++")]
        public readonly int         SmapCount;

        // Lowest address which should be accessed as physical memory
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     PhysicalBase;

        //For now I'm just doing a single communication channel from subservient kernel
        //to the BSP kernel.
        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly uint*OutgoingMessage;

        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly int* OutgoingCount;

        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly uint*IncomingFree;       //previously sent messages that cane be safely freed

        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly int* IncomingFreeCount;

        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly uint*IncomingMessage;    //messages bound for this kernel

        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly int* IncomingCount;

        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly uint*OutgoingFree;       // messages that this kernel has processed

        [AccessedByRuntime("referenced in c++")]
        unsafe public readonly int* OutgoingFreeCount;

        [AccessedByRuntime("referenced in c++")]
        public readonly uint        MaxBufferLength;

        [AccessedByRuntime("referenced in c++")]
        public readonly  uint       thisDestinationId;

        [AccessedByRuntime("referenced in c++")]
        public readonly  uint       hasApic;


        public int ApicId {
            [NoHeapAllocation]
                get {
#if ISA_IX
                if(hasApic == 1) {
                    // THIS SHOULD GO AWAY. WE SHOULD:
                    //  - 1. CHECK HEAP ALLOCATOR INITIALIZED AND PROCESSOR TABLE
                    //    - YES, return info from processor
                    //    - NO, return 0
                    uint p0, p1, p2, p3;
                    Isa.ReadCpuid((uint)1, out p0, out p1, out p2, out p3);
                    return (int)((p1 & 0xFF000000) >> 24);
                }

                return 0;
#elif ISA_ARM
                return 0;
#else
#error "E_UNSUPPORTED_PLATFORM"
#endif
            }
        }

        //
        // This represents "boot memory" in which
        // managed structures are allocated before the
        // GC and memory manager is initialized. These
        // pages must be marked early in MM initialization
        // so that they are known as nonGC pages.
        //
        // It is OK for this to be null if a given platform
        // allocates these classes in memory that is otherwise
        // accounted for.
        //
        // Examples are the Platform class, and each
        // processor class.
        //
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     BootAllocatedMemory;

        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     BootAllocatedMemorySize;

        // Command line (if any) given to HAL launcher.
        // !!! either generalize this or distill it to specific options.
        [AccessedByRuntime("referenced in c++")]
        // Field must be integral for 16-bit boot code
        public readonly UIntPtr     CommandLine32;
        public unsafe char *        CommandLine {
            [NoHeapAllocation]
                get {
                return (char *) CommandLine32;
            }
        }

        [AccessedByRuntime("referenced in c++")]
        public readonly int         CommandLineCount;

        // CpuContext record is stored off of FS at the value stored at the following offset
        // of fs.  A platform is guaranteed to have 2 pointers available at this offset.
        [AccessedByRuntime("referenced in c++")]
        public readonly unsafe int  CpuRecordPointerOffset;
        [AccessedByRuntime("referenced in c++")]
        public readonly unsafe int  ThreadRecordPointerOffset;

        // Various logging buffers
        // !!! Move these out of HAL
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     LogRecordBuffer;
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     LogRecordSize;
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     LogTextBuffer;
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     LogTextSize;

        // Kernel Dll (kernel.x86) where S execution will begin;
        // this is reported to S for use in debugging infrastructure
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     KernelDllBase;
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     KernelDllSize;
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     KernelDllFirstPage; // first page may be disjoint on CE

        // Initial minidump file address (if any)
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     MiniDumpBase;
        [AccessedByRuntime("referenced in c++")]
        public readonly UIntPtr     MiniDumpLimit;

        // TODO: Remove DebuggerType; replace with BOOL and always go through HAL

        // Debugger type to attach to
        [AccessedByRuntime("referenced in c++")]
        public readonly int         DebuggerType;
        // Debugger type enumeration
        [AccessedByRuntime("referenced in c++")]
        public const int            DEBUGGER_NONE       = 0;
        [AccessedByRuntime("referenced in c++")]
        public const int            DEBUGGER_SERIAL     = 1;
        [AccessedByRuntime("referenced in c++")]
        public const int            DEBUGGER_1394       = 2;

        // EntryPoint return values
        [AccessedByRuntime("referenced in c++")]
        public const int            SUCCESS = 0;
        [AccessedByRuntime("referenced in c++")]
        public const int            ERROR_BAD_SIZE       = 1;
        [AccessedByRuntime("referenced in c++")]
        public const int            ERROR_BAD_PLATFORM   = 2;

        ///////////////////////////////////////////////////////////////////////
        // Platform abstractions - these are filled in by the HAL during kernel
        // initialization
        ///////////////////////////////////////////////////////////////////////

        [AccessedByRuntime("referenced in c++")]
        public static Platform      thePlatform;

        [AccessedByRuntime("referenced in c++")]
        protected Cpu               bootCpu;

        public static Platform ThePlatform
        {
            [Inline]
                [NoHeapAllocation]
                get {
                return thePlatform;
            }
        }

        public static Cpu BootCpu
        {
            [Inline]
                [NoHeapAllocation]
                get {
                return thePlatform.bootCpu;
            }
        }

        public static Cpu CurrentCpu
        {
            [Inline]
                [NoHeapAllocation]
                get {
                return GetCurrentCpu();
            }
        }

        [AccessedByRuntime("accessed by C++")]
        [Inline]
        [NoHeapAllocation]
        public static Cpu Cpu(int id)
        {
            return thePlatform.GetCpu(id);
        }

        // Returns the current processor.  Note that in general you need to
        // have preemption disabled for this to return a meaningful value.

        [AccessedByRuntime("defined in hal.cpp")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        [StackBound(32)]
        public static extern Cpu GetCurrentCpu();

        // Platform is initially configured before Kernel.Main.  At this point
        // it is a minimal shell containing the boot records and the boot processor
        // information.  Services are not available until InitializeServices is
        // called later (which requires the object heap to be set up.)

        // called before boot; cannot allocate memory
        [NoHeapAllocation]
        [AccessedByRuntime("referenced in c++")]
        public unsafe void Initialize(Cpu bootCpu)
        {
            this.bootCpu = bootCpu;
            thePlatform = this;
        }

        /// Platform

#region BootInformation

        // Sanity Check
        public uint     RecSize;

        // Debug Stub Information
#if ISA_IX
        public ushort   DebugBasePort;
#elif ISA_ARM
        public uint     DebugBasePort;
#endif
        public ushort   DebugSpinBase;
        public uint     TwiddleSpinBase;

        // Self-descriptive information
        public ulong    Info32;
        public ulong    Kill32;
        public uint     KillAction;

        // Location (in high memory) of the executable images
        public ulong    DumpAddr32;

        // File image table ???
        public ulong    FileImageTableBase32;
        public uint     FileImageTableEntries;

        // Extent of that data
        public uint     DumpSize32;

        public ulong    DumpRemainder;

        // Marks the highest address used by the kernel image (undumped from high memory)
        public ulong    DumpLimit;
        public ulong    NativeContext;
        public ulong    Cpus;

#if ISA_IX64
        public ulong    Ppml432; // pointer to Page Map Level-4
        public ulong    AddrTss; // pointer to the 64-bit TSS containing the IST stack table
#endif

        // IDT and PIC
        public ushort   BiosPicMask;
        public byte     BiosWarmResetCmos;
        public uint     BiosWarmResetVector;
        public uint     Info16;

        // Temporary IDT
        public ulong    IdtEnter0;
        public ulong    IdtEnter1;
        public ulong    IdtEnterN;
        public ulong    IdtTarget;

        public ulong    Pdpt32;

        //
        // This is the kernel's operating map that secondary processors
        // must use. It may be updated by the kernel during the CPU 0
        // initialization process.
        //
        // Initially set to the same value as Pdpt32 by singboot when
        // CPU 0 is initialized.
        //
        public ulong    KernelPdpt64;

        public ulong    Undump;

        // PCI Information (V2.0+)
        public uint     PciBiosAX;
        public uint     PciBiosBX;
        public uint     PciBiosCX;
        public uint     PciBiosEDX;

        // BIOS Information
        public ulong    AcpiRoot32;
        public ulong    PnpNodesAddr32;
        public uint     PnpNodesSize32;
        public ulong    SmbiosRoot32;
        public ulong    DmiRoot32;
        public uint     IsaCsns;
        public ushort   IsaReadPort;
        public uint     Ebda32;
        public uint     MpFloat32;

        // 1394 Information
        public ulong    Ohci1394Base;
        public ulong    Ohci1394BufferAddr32;
        public uint     Ohci1394BufferSize32;

        // VESA Information
        public ulong    VesaBuffer;

        // MP specific variables
        public ulong    MpEnter32;          // Entry point
        public uint     MpCpuCount;         // No of AP's booted
        public uint     MpStatus32;         // Error indicator
        public ulong    MpStartupLock32;    // Pointer to MP init lock var

        public Microsoft.Singularity.MpBootInfo   MpBootInfo;

#endregion // BootInformation

        //////////////////////////////////////////////////////////////////////
        // Kernel fields initialized by early kernel code
        //////////////////////////////////////////////////////////////////////

        private Cpu[]   processors;

        private HalDevices devices;

        [NoHeapAllocation]
        public void RegisterCpu(Cpu p)
        {
            DebugStub.Assert(processors != null);
            DebugStub.Assert(p.Id >= 0);
            DebugStub.Assert(p.Id < processors.Length);
            DebugStub.Assert((processors[p.Id] == null) || (processors[p.Id] == p));
            processors[p.Id] = p;
        }

        // This routine is used to report GC objects which are manufactured by the
        // HAL, in order to trace their reference fields.  (Note that such objects
        // must also end up on pages labelled NonGC for tracing, etc to work correctly.)

        internal void VisitSpecialData(System.GCs.ReferenceVisitor visitor)
        {
            // The Platform object and the processor objects are all allocated
            // on fixed pages, so must be explicitly traced.

            visitor.VisitReferenceFields(thePlatform);

            foreach (Cpu p in processors) {
                if (p != null) {
                    visitor.VisitReferenceFields(p);
                }
            }
        }

        [NoHeapAllocation]
        public bool DisableInterrupts()
        {
            return Isa.DisableInterrupts();
        }

        [NoHeapAllocation]
        public void EnableInterrupts()
        {
            Isa.EnableInterrupts();
        }

        [NoHeapAllocation]
        public  bool AreInterruptsDisabled()
        {
            return Isa.AreInterruptsDisabled();
        }

        // Halt causes the current CPU to cease execution until an interrupt occurs.

        [NoHeapAllocation]
        public void Halt()
        {
            // @BUG this is broken - we can migrate to another CPU
            CurrentCpu.halted = true;
            Isa.Halt();
        }

        // RendezvousCpus sends a rendezvous to the other processors.

        [NoHeapAllocation]
        public void RendezvousCpus()
        {
            // Not implemented
        }

        // Kill exits the platform environment.

        [AccessedByRuntime("referenced in c++")]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [StackBound(64)]
        [NoHeapAllocation]
        private static extern void NativeKill(int exitCode);

        [NoHeapAllocation]
        public void Kill(int exitCode)
        {
            NativeKill(exitCode);
        }

        // TBD: there is currently no standard processor array, it is maintained by the HAL.
        // (Not sure if this is valuable.)
        [NoHeapAllocation]
        public Cpu GetCpu(int i)
        {
            return processors[i];
        }

        // This will cause the CPUs to get enabled; each will have EntryPoint called
        public void EnableMoreCpus(int cpus)
        {
            //
            // Currently a separate code path in kernel.cs calls the HalDevices.StartApProcessors()
            // due to layering issues with the HalPic's in the kernel, and the HAL being below
            // the kernel not allowed to call up into the kernel. Eventually when these
            // devices move into the HAL (and PNP resource assignment issues are resolved) this
            // code will call StartAppProcessors(cpus).
            //
        }

#region Debugging
        [NoHeapAllocation]
        public void FreezeAllCpus()
        {
            devices.FreezeProcessors();
        }
#endregion // debugging

#region Timer
        // Request that an interrupt fire immediately on the given processor.
        // Note that this may be called on other CPUs to facilitate IPC.

        [NoHeapAllocation]
        public void WakeNow(int cpu)
        {
            int fromCpu = Microsoft.Singularity.Processor.GetCurrentProcessorId();
            devices.SendFixedIPI((byte)Kernel.HalIpiInterrupt, fromCpu, cpu);
        }
#endregion // Timer

        // This is called to fully initialize the platform
        public void InitializeServices()
        {
            processors = new Cpu[CpuMaxCount];
            processors[0] = bootCpu;
            bootCpu.InitializeServices();

            // TBD
        }

#region HAL
        // Get our HalDevices interface from the externally implemented HAL
        public static void InitializeHal(Processor processor)
        {
            thePlatform.devices = (HalDevices)HalDevicesFactory.Initialize(processor);
        }

        public static void ReleaseResources()
        {
            thePlatform.devices.ReleaseResources();
        }

        //
        // Adding and removing interrupts from the Pic.
        //
        [NoHeapAllocation]
        public static void EnableIoInterrupt(byte irq)
        {
            thePlatform.devices.EnableIoInterrupt(irq);
        }

        [NoHeapAllocation]
        public static void DisableIoInterrupt(byte irq)
        {
            thePlatform.devices.DisableIoInterrupt(irq);
        }

        [NoHeapAllocation]
        public static bool InternalInterrupt(byte interrupt)
        {
            return thePlatform.devices.InternalInterrupt(interrupt);
        }

        [NoHeapAllocation]
        public static byte GetMaximumIrq()
        {
            return thePlatform.devices.GetMaximumIrq();
        }

        [NoHeapAllocation]
        public static int GetProcessorCount()
        {
            return thePlatform.devices.GetProcessorCount();
        }

        public static void StartApProcessors(int cpus)
        {
            thePlatform.devices.StartApProcessors(cpus);
        }

        [NoHeapAllocation]
        public static void ResetApProcessors()
        {
            thePlatform.devices.ResetApProcessors();
        }

        [NoHeapAllocation]
        public static void FreezeProcessors()
        {
            thePlatform.devices.FreezeProcessors();
        }

        // send fixed interrupt
        [NoHeapAllocation]
        public static void SendFixedIPI(byte vector, int from, int to)
        {
            thePlatform.devices.SendFixedIPI(vector, from, to);
        }

        [NoHeapAllocation]
        public static void BroadcastFixedIPI(byte vector, bool includeSelf)
        {
            thePlatform.devices.BroadcastFixedIPI(vector, includeSelf);
        }

        [NoHeapAllocation]
        public static void ClearFixedIPI(int interrupt)
        {
            thePlatform.devices.ClearFixedIPI(interrupt);
        }

        public static byte TranslatePciInterrupt(byte currentInterruptLine,
                                                 byte pciInterruptPin,
                                                 PciPort pciPort)
        {
            return thePlatform.devices.TranslatePciInterrupt(currentInterruptLine,
                                                             pciInterruptPin,
                                                             pciPort);
        }
#endregion // HAL

    }
}

