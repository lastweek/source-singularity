// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
// Simple PE Loader for Singularity
//
// Currently does not support:
//      x64
//      sections loaded at separate addresses
//      loading at preferred address

// #define verbose

// #define SINGULARITY_ASMP

namespace Microsoft.Singularity.Loader
{
    using Microsoft.Singularity;
    using Microsoft.Singularity.Io;
    using Microsoft.Singularity.Memory;

    using System;
    using System.Diagnostics;
    using System.Runtime.InteropServices;
    using System.Runtime.CompilerServices;
    using System.Threading;
    using Microsoft.Singularity.V1.Services;
    using Microsoft.Singularity.Hal;

    using PageType = System.GCs.PageType;

    [CLSCompliant(false)]
    [AccessedByRuntime("output to header : defined in hal.cpp/peimage.cpp")]
    internal class PEImage
    {
        // PE Signature
        internal readonly uint signature;

        // IMAGE_FILE_HEADER
        internal readonly ushort machine;
        internal readonly ushort numberOfSections;
        internal readonly uint   timeDateStamp;
        internal readonly ushort sizeOfOptionalHeader;
        internal readonly ushort characteristics;

#if PTR_SIZE_64
        internal readonly ulong imageBase;
#else
        internal readonly uint imageBase;
#endif
        // IMAGE_OPTIONAL_HEADER32
        internal readonly ushort magic;
        internal readonly uint   addressOfEntryPoint;
        internal readonly uint   sectionAlignment;
        internal readonly uint   fileAlignment;
        private  readonly uint   sizeOfImage; // use loadedSize (this is rnd'd)
        internal readonly uint   sizeOfHeaders;
        internal readonly uint   checkSum;
        internal readonly ushort dllCharacteristics;
        internal readonly uint   loaderFlags;
        internal readonly uint   numberOfRvaAndSizes;

        // IMAGE_DATA_DIRECTORY and SECTION_HEADERs
        internal readonly DirectoryEntry[] directory;
        internal readonly SectionHeader[] sections;
        internal readonly uint loadedSize;

        internal const ushort IMAGE_FILE_32BIT_MACHINE      = 0x0100; // 32 bit machine.
        internal const ushort IMAGE_FILE_DLL                = 0x2000; // File is a DLL.

        internal const ushort IMAGE_DOS_SIGNATURE           = 0x5A4D;     // MZ
        internal const uint   IMAGE_NT_SIGNATURE            = 0x00004550; // PE00
        internal const ushort IMAGE_NT_OPTIONAL_HDR32_MAGIC = 0x010b;
        internal const ushort IMAGE_NT_OPTIONAL_HDR64_MAGIC = 0x020b;

        enum Machine : ushort {
            UNKNOWN           = 0,
                I386              = 0x014c, // Intel 386.
                R3000             = 0x0162, // MIPS little-endian, = 0x160 big-endian
                R4000             = 0x0166, // MIPS little-endian
                R10000            = 0x0168, // MIPS little-endian
                WCEMIPSV2         = 0x0169, // MIPS little-endian WCE v2
                ALPHA             = 0x0184, // Alpha_AXP
                SH3               = 0x01a2, // SH3 little-endian
                SH3DSP            = 0x01a3,
                SH3E              = 0x01a4, // SH3E little-endian
                SH4               = 0x01a6, // SH4 little-endian
                SH5               = 0x01a8, // SH5
                ARM               = 0x01c0, // ARM Little-Endian
                THUMB             = 0x01c2,
                AM33              = 0x01d3,
                POWERPC           = 0x01F0, // IBM PowerPC Little-Endian
                POWERPCFP         = 0x01f1,
                IA64              = 0x0200, // Intel 64
                MIPS16            = 0x0266, // MIPS
                ALPHA64           = 0x0284, // ALPHA64
                MIPSFPU           = 0x0366, // MIPS
                MIPSFPU16         = 0x0466, // MIPS
                TRICORE           = 0x0520, // Infineon
                EBC               = 0x0EBC, // EFI Byte Code
                X64               = 0x8664, // AMD64, etc.
                M32R              = 0x9041, // M32R little-endian
                CEE               = 0xC0EE,
                };

        // Directory Entries

        enum DirEntry {
            Export      = 0,    // Export Directory
            Import      = 1,    // Import Directory
            Security    = 4,    // Security Directory
            BaseReloc   = 5,    // Base Relocation Table
            Debug       = 6,    // Debug Directory
            Copyright   = 7,    // Description String
        };

        internal UIntPtr VirtualAddress;

        // Corresponds to the WinNT IMAGE_NT_HEADERS data structure
        internal static PEImage kernel = null;
        internal static ExportTable kernelExports = null;
        internal static PEImage mpAbi = null;
        internal static ExportTable mpAbiExports = null;

        internal PEImage(IoMemory mem)
        {
            Kernel.Waypoint(601);
            if (mem.Length < 64) {
                throw new BadImageFormatException("Invalid MZ header");
            }

            magic = mem.Read16Unchecked(0);
            Kernel.Waypoint(602);

            int offset = (int)mem.Read32Unchecked(60);

            if (magic != IMAGE_DOS_SIGNATURE || offset < 64 || offset + 120 > mem.Length) {
                throw new BadImageFormatException("Invalid MZ header");
            }

            signature                   = mem.Read32Unchecked(offset + 0);
            machine                     = mem.Read16Unchecked(offset + 4);
            numberOfSections            = mem.Read16Unchecked(offset + 6);
            timeDateStamp               = mem.Read32Unchecked(offset + 8);
            sizeOfOptionalHeader        = mem.Read16Unchecked(offset + 20);
            characteristics             = mem.Read16Unchecked(offset + 22);
            magic                       = mem.Read16Unchecked(offset + 24);
            addressOfEntryPoint         = mem.Read32Unchecked(offset + 40);
            sectionAlignment            = mem.Read32Unchecked(offset + 56);
            fileAlignment               = mem.Read32Unchecked(offset + 60);
            sizeOfImage                 = mem.Read32Unchecked(offset + 80);
            sizeOfHeaders               = mem.Read32Unchecked(offset + 84);
            checkSum                    = mem.Read32Unchecked(offset + 88);
            dllCharacteristics          = mem.Read16Unchecked(offset + 94);
            loaderFlags                 = mem.Read32Unchecked(offset + 112);

#if PTR_SIZE_64
            imageBase                   = mem.Read64Unchecked(offset + 48);
            numberOfRvaAndSizes         = mem.Read32Unchecked(offset + 132);
            offset += 136;

            Kernel.Waypoint(603);
            // Verify that we have a valid NT header
            DebugStub.WriteLine("size of optional header ={0}", __arglist(sizeOfOptionalHeader));
            if (signature != IMAGE_NT_SIGNATURE ||
                sizeOfOptionalHeader != 240 ||
                magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC ||
                numberOfRvaAndSizes != 16) {

                throw new BadImageFormatException("Invalid PE header");
            }
#else
            imageBase = mem.Read32Unchecked(offset + 52);
            numberOfRvaAndSizes         = mem.Read32Unchecked(offset + 116);
            offset += 120;

            Kernel.Waypoint(603);
            // Verify that we have a valid NT header

            if (signature != IMAGE_NT_SIGNATURE ||
                sizeOfOptionalHeader != 224 ||
                magic != IMAGE_NT_OPTIONAL_HDR32_MAGIC ||
                numberOfRvaAndSizes != 16)
            {

                throw new BadImageFormatException("Invalid PE header");
            }
#endif

            VirtualAddress = mem.VirtualAddress;

            Kernel.Waypoint(693);

            directory = new DirectoryEntry[numberOfRvaAndSizes];

            for (uint i = 0; i < numberOfRvaAndSizes; i++) {
                directory[i] = new DirectoryEntry(mem, ref offset);
            }

            sections = new SectionHeader[numberOfSections];
            for (uint i = 0; i < numberOfSections; i++) {
                sections[i] = new SectionHeader(mem, ref offset);

            }

            Kernel.Waypoint(694);

            // Calc the sizes of the loaded regions according to starting virtual address
            loadedSize = sizeOfImage;
            for (uint i = 0; i < numberOfSections; i++) {
                if (!sections[i].IsDiscardable) {
                    uint addr = sections[i].virtualAddress;
                    uint size = sections[i].virtualSize;
                    uint last = addr + size;

                    if (loadedSize < last) {
                        loadedSize = last;
                    }
                }
            }

            Kernel.Waypoint(604);
        }

        internal ExportTable GetExportTable(IoMemory mem)
        {
            if (directory[(int)DirEntry.Export].virtualAddress == 0) {
                return null;
            }
            return new ExportTable(mem, mem.VirtualAddress,
                                   directory[(int)DirEntry.Export]);
        }

        internal ImportTable GetImportTable(IoMemory mem)
        {
            if (directory[(int)DirEntry.Import].virtualAddress == 0) {
                return null;
            }
            return new ImportTable(mem, directory[(int)DirEntry.Import]);
        }

        [NoHeapAllocation]
        internal uint GetRelocationsRaw()
        {
            uint relocationAddr = directory[(int)DirEntry.BaseReloc].virtualAddress;

            for (uint i = 0; i < numberOfSections; i++) {
                if (sections[i].virtualAddress == relocationAddr) {
                    return sections[i].pointerToRawData;
                }
            }
            return 0;
        }

        ////////////////////////////////////////////////////// Static Methods.
        //
        public static unsafe void Initialize()
        {
            Platform p = Platform.ThePlatform;
            IoMemory pages = IoMemory.MapPhysicalMemory((UIntPtr) p.KernelDllFirstPage,
                                                        4096, true, false);
            kernel = new PEImage(pages);
            pages = IoMemory.MapPhysicalMemory((UIntPtr) p.KernelDllBase,
                                               kernel.loadedSize, true, false);

            kernelExports = kernel.GetExportTable(pages);

            DebugStub.WriteLine("PEImage.Initialize: Notify KD of kernel load.");
            DebugStub.LoadedBinary(pages.VirtualAddress,
                                   kernel.sizeOfImage,
#if ISA_ARM
                                   "kernel.arm",
#elif ISA_IX64
                                   "kernel.x64",
#elif ISA_IX86
                                   "kernel.x86",
#endif
                                   kernel.checkSum,
                                   kernel.timeDateStamp,
                                   false);

            // This breakpoint is triggered by a "-d" to windbg.
            if (DebugStub.PollForBreak()) {
                DebugStub.Break();
            }

#if GENERATE_ABI_SHIM
            DebugStub.WriteLine("    InitializeMpAbi() *****");
            InitializeMpAbi();
#endif
        }

        public static void InitializeMpAbi()
        {
            // Note: When mapping the abi stub (MpSyscalls.x86), we must
            // map it with writable flag! as we want to resolve the stub's
            // imports
            IoMemory mpPages = IoMemory.MapPhysicalMemory(Platform.MP_ABI_BASE, 4096, true, true);
            mpAbi = new PEImage(mpPages);
            mpPages = IoMemory.MapPhysicalMemory(Platform.MP_ABI_BASE, mpAbi.loadedSize, true, true);
            mpAbiExports = mpAbi.GetExportTable(mpPages);

            // Resolve imports in abi shim dll with the kernel exports
            // which are the real stub that will do IPI stuffs
            ImportTable mpAbiIt = mpAbi.GetImportTable(mpPages);

            DebugStub.WriteLine("HSG: ** Resolving Imports");
            mpAbiIt.ResolveImports(kernelExports);
        }

        public static void Finalize()
        {
            // Uncomment the following line to notify debugger when we shutdown.
            // DebugStub.UnloadedBinary(UIntPtr.MaxValue, false);
        }

        internal static PEImage KernelImage
        {
            [NoHeapAllocation]
            get { return kernel; }
        }

        public static PEImage Load(Process process, IoMemory rawMemory,
                                   out IoMemory loadedMemory, bool isForMp)
        {
            return Load(process, rawMemory, out loadedMemory,
                        isForMp, process == Process.kernelProcess);
        }

        public static PEImage Load(Process process, IoMemory rawMemory,
                                   out IoMemory loadedMemory, bool isForMp,
                                   bool inKernelSpace)
        {
            UIntPtr entryPoint = UIntPtr.Zero;
            loadedMemory = null;

            DiagnosisService.DeferedUpdateNotification();

            if (null == rawMemory || 0 == rawMemory.Length) {
                DebugStub.WriteLine("No PXE image to load!");
                return null;
            }

            //
            // Allocate memory and copy the PXE image from memory to memory
            //
#if verbose
            Tracing.Log(Tracing.Debug, " PXE at {0:x8}, Length ={1:x8}",
                        (uint)rawMemory.VirtualAddress,
                        rawMemory.Length);
#endif

            Kernel.Waypoint(580);
            Tracing.Log(Tracing.Debug, "Loading:");
            PEImage image = new PEImage(rawMemory);
            image.DumpLimitedToStream();

#if verbose
            Tracing.Log(Tracing.Debug, "  Loaded Size={0:x8}", image.loadedSize);
#endif
            Kernel.Waypoint(581);
            if (0 == image.loadedSize) {
                throw new BadImageFormatException("Invalid PE, no content");
            }

            try {
                if (inKernelSpace) {
                    loadedMemory = IoMemory.AllocateFixed(
                        (UIntPtr)image.loadedSize,
                        process, PageType.System);
                }
                else {
                    // Situate the process image in the user range
                    loadedMemory = IoMemory.AllocateUserFixed(
                        (UIntPtr)image.loadedSize,
                        process, PageType.System);
                }

                Kernel.Waypoint(582);


#if verbose
                Tracing.Log(Tracing.Debug, " loaded at {0:x8}, Length ={1:x8}",
                            (uint)loadedMemory.VirtualAddress,
                            loadedMemory.Length);
#endif
                // Copy the header so the debugger can find it.
                IoMemory.Copy(rawMemory, 0, loadedMemory, 0, (int)image.sizeOfHeaders);

#if verbose
                image.DumpLimitedToStream();
#endif

                Kernel.Waypoint(583);
                // load sections into memory where they belong.
                for (int i = 0; i < image.numberOfSections; i++) {
                    if (image.sections[i].IsDiscardable ||
                        image.sections[i].sizeOfRawData == 0) {
                        continue;
                    }

                    int targetOffset = (int)image.sections[i].virtualAddress;
                    int sourceOffset = (int)image.sections[i].pointerToRawData;
                    uint rawSize = Math.Min(image.sections[i].sizeOfRawData,
                                            image.sections[i].virtualSize);
#if verbose
                    Tracing.Log(Tracing.Debug, "section[{0}] source={1:x8}..{2:x8} target={3:x8}..{4:x8}",
                                      i,
                                      sourceOffset, sourceOffset + rawSize,
                                      targetOffset, targetOffset + rawSize);
#endif

                    if (image.sections[i].virtualSize > image.sections[i].sizeOfRawData) {

                        //  The memory allocated for the new image is not zeroed, therefore
                        //  we need to clear the remaining region of a section that is not getting
                        //  copied from the source. NOTE BSS sections rely on this to be zeroed
                        //  This is fixing some random bugs with uninitialized variables in unmanaged code

                        unsafe {

                            byte * dest = (byte *) loadedMemory.VirtualAddress + targetOffset + image.sections[i].sizeOfRawData;
                            uint length = image.sections[i].virtualSize - image.sections[i].sizeOfRawData;

                            Buffer.ZeroMemory(dest, length);
                        }
                    }

                    IoMemory.Copy(rawMemory, sourceOffset, loadedMemory, targetOffset, (int)rawSize);
                }
                Kernel.Waypoint(584);

                //
                // Handle Relocations
                //
                int relocationTableOffset = (int)image.GetRelocationsRaw();
                UIntPtr diff = (UIntPtr) loadedMemory.VirtualAddress - (UIntPtr) image.imageBase;
                image.VirtualAddress = loadedMemory.VirtualAddress;

#if verbose
                Tracing.Log(Tracing.Debug, " Base loaded={0:x8}, relocated ={1:x8} diff={2:x8}",
                            image.imageBase, (uint)loadedMemory.VirtualAddress, diff);

                Tracing.Log(Tracing.Debug, " relocationTableOffset ={0:x8} ", relocationTableOffset);
#endif

                if (relocationTableOffset > 0) {
                    Relocations.FixupBlocks(rawMemory, (int)relocationTableOffset,
                                            loadedMemory, diff);
                    // TODO: We should probably zero the relocation table.
                }

                Kernel.Waypoint(585);

                //
                // Resolve Imports
                //
                ImportTable it = image.GetImportTable(loadedMemory);
                Kernel.Waypoint(586);

#if !PAGING

#if GENERATE_ABI_SHIM
                if (it != null) {
#endif
                    //it.DumpIAT("Import directory");

                    // if this is loading for remote processor
                    // then solve the imports with abi stub
                    if (isForMp) {
                        it.ResolveImports(mpAbiExports);
                    }
                    else {
                        it.ResolveImports(kernelExports);
                    }

                    //DumpIAT(loadedMemory, "Import Address Table",
                    // ref image.directory[12]);
#if GENERATE_ABI_SHIM
                }
#endif

#else
                if (it != null) {
                    // Ring-3 protection domains come with a set of
                    // stubs that accomplish the ring3-to-ring0 ABI
                    // transitions. Use these when called for.
                    ExportTable abiStubs = process.Domain.ABIStubs;

                    if (abiStubs != null) {
                        it.ResolveImports(abiStubs);
                    }
                    else {
                    it.ResolveImports(kernelExports);
                }
                }
#endif

                Kernel.Waypoint(587);

                //
                // Dump Exports
                //
                ExportTable et = image.GetExportTable(loadedMemory);
                if (et != null) {
                    et.Dump();
                }

                Kernel.Waypoint(588);

                entryPoint = (UIntPtr)loadedMemory.VirtualAddress + image.addressOfEntryPoint;

                Tracing.Log(Tracing.Debug, "  Loaded: {0:x8}..{1:x8}, Entry: {2:x8}",
                                  (ulong)loadedMemory.VirtualAddress,
                                  (ulong)(loadedMemory.VirtualAddress + loadedMemory.Length),
                                  (ulong)(entryPoint));
            }
            finally {
                if (entryPoint == UIntPtr.Zero && loadedMemory != null) {
                    // TODO: Need to dispose of target Range.
                    loadedMemory = null;
                }
            }
            return image;
        }

        // HelloMpLoad skips several procedures to be able to
        // load HelloMp.x86 properly
        public static PEImage HelloMpLoad(Process process, IoMemory rawMemory,
                                          out IoMemory loadedMemory)
        {
            UIntPtr entryPoint = UIntPtr.Zero;
            loadedMemory = null;

            if (null == rawMemory || 0 == rawMemory.Length) {
                DebugStub.WriteLine("No PXE image to load!");
                return null;
            }

            Kernel.Waypoint(580);
            Tracing.Log(Tracing.Debug, "Loading:");
            PEImage image = new PEImage(rawMemory);
            image.DumpLimitedToStream();

            Kernel.Waypoint(581);
            if (0 == image.loadedSize) {
                throw new BadImageFormatException("Invalid PE, no content");
            }

            try {
                // The loadedImage is current loaded to physical memory
                // directly
                loadedMemory = IoMemory.AllocatePhysical
                    ((UIntPtr)image.loadedSize);

                Kernel.Waypoint(582);

                // Copy the header so the debugger can find it.
                IoMemory.Copy(rawMemory, 0, loadedMemory, 0,
                              (int)image.sizeOfHeaders);
                Kernel.Waypoint(583);
                // load sections into memory where they belong.
                for (int i = 0; i < image.numberOfSections; i++) {
                    if (image.sections[i].IsDiscardable ||
                        image.sections[i].sizeOfRawData == 0) {
                        continue;
                    }
                    int targetOffset = (int)image.sections[i].virtualAddress;
                    int sourceOffset = (int)image.sections[i].pointerToRawData;
                    uint rawSize = Math.Min(image.sections[i].sizeOfRawData,
                                            image.sections[i].virtualSize);
                    IoMemory.Copy(rawMemory, sourceOffset, loadedMemory,
                                  targetOffset, (int)rawSize);
                }
                Kernel.Waypoint(584);

                int relocationTableOffset = (int)image.GetRelocationsRaw();
                UIntPtr diff = (UIntPtr) loadedMemory.VirtualAddress -
                    (UIntPtr) image.imageBase;
                entryPoint = (UIntPtr)loadedMemory.VirtualAddress +
                    image.addressOfEntryPoint;
            }
            finally {
                if (entryPoint == UIntPtr.Zero && loadedMemory != null) {
                    // TODO: Need to dispose of target Range.
                    loadedMemory = null;
                }
            }
            return image;
        }


        [NoHeapAllocation]
        public UIntPtr GetEntryPoint(IoMemory loadedImage)
        {
            return loadedImage.VirtualAddress + addressOfEntryPoint;
        }

        [AccessedByRuntime("output to header : defined in PEImage.cpp")]
        [OutsideGCDomain]
        [StackBound(256)]
        [NoInline]
        [NoStackLinkCheck]
        [NoStackOverflowCheck]
        [MethodImpl(MethodImplOptions.InternalCall)]
        [NoHeapAllocation]
        internal static extern int HalCallEntryPoint(UIntPtr entry, int threadIndex,
                                                     bool runAtRing3);

        [NoHeapAllocation]
        internal static int CallEntryPoint(UIntPtr entry, int threadIndex,
                                           bool runAtRing3)
        {
            return HalCallEntryPoint(entry, threadIndex, runAtRing3);
        }

        //
        // Output Routines
        //
        [Conditional("DEBUG")]
        internal void DumpLimitedToStream()
        {
            Tracing.Log(Tracing.Debug, "  Entry point:         {0:x8}", addressOfEntryPoint);
            Tracing.Log(Tracing.Debug, "  Image base:          {0:x8}", imageBase);
#if verbose
            Tracing.Log(Tracing.Debug, "  Section alignment:   {0:x8}", sectionAlignment);
            Tracing.Log(Tracing.Debug, "  File alignment:      {0:x8}", fileAlignment);
            Tracing.Log(Tracing.Debug, "  Directories:         {0:x8}", numberOfRvaAndSizes);
#endif
            Tracing.Log(Tracing.Debug, "  Loaded Size:         {0:x8}", loadedSize);
            if (directory[0].virtualAddress != 0) {
                directory[0].DumpToStream("Export directory      ");
            }
            if (directory[1].virtualAddress != 0) {
                directory[1].DumpToStream("Import directory      ");
            }
            if (directory[5].virtualAddress != 0) {
                directory[5].DumpToStream("Relocation Table      ");
            }
            if (directory[6].virtualAddress != 0) {
                directory[6].DumpToStream("Debug Directory       ");
            }
            if (directory[11].virtualAddress != 0) {
                directory[11].DumpToStream("Bound Import Table   ");
            }
            if (directory[12].virtualAddress != 0) {
                directory[12].DumpToStream("Import Address Table ");
            }

            for (uint i = 0; i < numberOfSections; i++) {
                sections[i].DumpToStream();
            }
        }

    }
}
