///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  expandpe.cpp: code to expand PE image into memory.
//

//#define EXPANDPE_VERBOSE 1

///////////////////////////////////////////////// Required External Functions.
//
void CopyDown(UINT8 *pbDst, UINT8 *pbSrc, UINT32 cbSrc);
void Zero(uint8 * pbData, uint32 cbData);

//////////////////////////////////////////////////////////////////////////////

#define IMAGE_DOS_SIGNATURE                 0x5A4D      // MZ
#define IMAGE_NT_SIGNATURE                  0x00004550  // PE00

typedef struct _IMAGE_DOS_HEADER {      // DOS .EXE header
    uint16 e_magic;                     // Magic number
    uint16 e_cblp;                      // Bytes on last page of file
    uint16 e_cp;                        // Pages in file
    uint16 e_crlc;                      // Relocations
    uint16 e_cparhdr;                   // Size of header in paragraphs
    uint16 e_minalloc;                  // Minimum extra paragraphs needed
    uint16 e_maxalloc;                  // Maximum extra paragraphs needed
    uint16 e_ss;                        // Initial (relative) SS value
    uint16 e_sp;                        // Initial SP value
    uint16 e_csum;                      // Checksum
    uint16 e_ip;                        // Initial IP value
    uint16 e_cs;                        // Initial (relative) CS value
    uint16 e_lfarlc;                    // File address of relocation table
    uint16 e_ovno;                      // Overlay number
    uint16 e_res[4];                    // Reserved words
    uint16 e_oemid;                     // OEM identifier (for e_oeminfo)
    uint16 e_oeminfo;                   // OEM information; e_oemid specific
    uint16 e_res2[10];                  // Reserved words
    uint32 e_lfanew;                    // File address of new exe header
  } IMAGE_DOS_HEADER, *PIMAGE_DOS_HEADER;

typedef struct _IMAGE_FILE_HEADER {
    uint16  Machine;
    uint16  NumberOfSections;
    uint32  TimeDateStamp;
    uint32  PointerToSymbolTable;
    uint32  NumberOfSymbols;
    uint16  SizeOfOptionalHeader;
    uint16  Characteristics;
} IMAGE_FILE_HEADER, *PIMAGE_FILE_HEADER;

//
// Directory format.
//

typedef struct _IMAGE_DATA_DIRECTORY {
    uint32  VirtualAddress;
    uint32  Size;
} IMAGE_DATA_DIRECTORY, *PIMAGE_DATA_DIRECTORY;

#define IMAGE_NUMBEROF_DIRECTORY_ENTRIES    16


//
// Optional header format.
//

#define IMAGE_NT_OPTIONAL_HDR32_MAGIC      0x10b
#define IMAGE_NT_OPTIONAL_HDR64_MAGIC      0x20b

typedef struct _IMAGE_OPTIONAL_HEADER32 {
    //
    // Standard fields.
    //
    uint16  Magic;
    uint8   MajorLinkerVersion;
    uint8   MinorLinkerVersion;
    uint32  SizeOfCode;
    uint32  SizeOfInitializedData;
    uint32  SizeOfUninitializedData;
    uint32  AddressOfEntryPoint;
    uint32  BaseOfCode;
    uint32  BaseOfData;

    //
    // NT additional fields.
    //
    uint32  ImageBase;
    uint32  SectionAlignment;
    uint32  FileAlignment;
    uint16  MajorOperatingSystemVersion;
    uint16  MinorOperatingSystemVersion;
    uint16  MajorImageVersion;
    uint16  MinorImageVersion;
    uint16  MajorSubsystemVersion;
    uint16  MinorSubsystemVersion;
    uint32  Win32VersionValue;
    uint32  SizeOfImage;
    uint32  SizeOfHeaders;
    uint32  CheckSum;
    uint16  Subsystem;
    uint16  DllCharacteristics;
    uint32  SizeOfStackReserve;
    uint32  SizeOfStackCommit;
    uint32  SizeOfHeapReserve;
    uint32  SizeOfHeapCommit;
    uint32  LoaderFlags;
    uint32  NumberOfRvaAndSizes;
    IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
} IMAGE_OPTIONAL_HEADER32, *PIMAGE_OPTIONAL_HEADER32;

typedef struct _IMAGE_OPTIONAL_HEADER64 {
    uint16      Magic;
    uint8       MajorLinkerVersion;
    uint8       MinorLinkerVersion;
    uint32      SizeOfCode;
    uint32      SizeOfInitializedData;
    uint32      SizeOfUninitializedData;
    uint32      AddressOfEntryPoint;
    uint32      BaseOfCode;
    uint64      ImageBase;
    uint32      SectionAlignment;
    uint32      FileAlignment;
    uint16      MajorOperatingSystemVersion;
    uint16      MinorOperatingSystemVersion;
    uint16      MajorImageVersion;
    uint16      MinorImageVersion;
    uint16      MajorSubsystemVersion;
    uint16      MinorSubsystemVersion;
    uint32      Win32VersionValue;
    uint32      SizeOfImage;
    uint32      SizeOfHeaders;
    uint32      CheckSum;
    uint16      Subsystem;
    uint16      DllCharacteristics;
    uint64      SizeOfStackReserve;
    uint64      SizeOfStackCommit;
    uint64      SizeOfHeapReserve;
    uint64      SizeOfHeapCommit;
    uint32      LoaderFlags;
    uint32      NumberOfRvaAndSizes;
    IMAGE_DATA_DIRECTORY DataDirectory[IMAGE_NUMBEROF_DIRECTORY_ENTRIES];
} IMAGE_OPTIONAL_HEADER64, *PIMAGE_OPTIONAL_HEADER64;

typedef struct _IMAGE_NT_HEADERS64 {
    uint32      Signature;
    IMAGE_FILE_HEADER FileHeader;
    IMAGE_OPTIONAL_HEADER64 OptionalHeader;
} IMAGE_NT_HEADERS64, *PIMAGE_NT_HEADERS64;

typedef struct _IMAGE_NT_HEADERS32 {
    uint32      Signature;
    IMAGE_FILE_HEADER FileHeader;
    IMAGE_OPTIONAL_HEADER32 OptionalHeader;
} IMAGE_NT_HEADERS32, *PIMAGE_NT_HEADERS32;

#define IMAGE_SIZEOF_SHORT_NAME              8

typedef struct _IMAGE_SECTION_HEADER {
    uint8   Name[IMAGE_SIZEOF_SHORT_NAME];
    uint32  VirtualSize;
    uint32  VirtualAddress;
    uint32  SizeOfRawData;
    uint32  PointerToRawData;
    uint32  PointerToRelocations;
    uint32  PointerToLinenumbers;
    uint16  NumberOfRelocations;
    uint16  NumberOfLinenumbers;
    uint32  Characteristics;
} IMAGE_SECTION_HEADER, *PIMAGE_SECTION_HEADER;

//
// Directory Entries
//
#define IMAGE_DIRECTORY_ENTRY_BASERELOC       5   // Base Relocation Table

//
// Based relocation types.
//
#define IMAGE_REL_BASED_ABSOLUTE              0
#define IMAGE_REL_BASED_HIGH                  1
#define IMAGE_REL_BASED_LOW                   2
#define IMAGE_REL_BASED_HIGHLOW               3
#define IMAGE_REL_BASED_HIGHADJ               4
#define IMAGE_REL_BASED_MIPS_JMPADDR          5
#define IMAGE_REL_BASED_MIPS_JMPADDR16        9
#define IMAGE_REL_BASED_IA64_IMM64            9
#define IMAGE_REL_BASED_DIR64                 10

//////////////////////////////////////////////////////////////////////////////
//
uintptr SizeOfPeImage(uintptr source, uintptr& base)
{
    UINT8 * pbImage = (UINT8 *)source;
    uintptr size = 0;

    IMAGE_DOS_HEADER * pidh = (IMAGE_DOS_HEADER *)pbImage;
    if (pidh->e_magic != IMAGE_DOS_SIGNATURE) {
        return 0;
    }

    IMAGE_NT_HEADERS32 * pinh = (IMAGE_NT_HEADERS32 *)(pbImage + pidh->e_lfanew);
    IMAGE_NT_HEADERS64 * pinh64 = (IMAGE_NT_HEADERS64 *)(pbImage + pidh->e_lfanew);
    if (pinh->Signature != IMAGE_NT_SIGNATURE) {
        return 0;
    }

    if ((pinh->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR32_MAGIC) &&
        (pinh64->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC)) {
        return 0;
    }

    if (pinh->OptionalHeader.Magic == IMAGE_NT_OPTIONAL_HDR32_MAGIC) {
        base = pinh->OptionalHeader.ImageBase;

        if (size < pinh->OptionalHeader.SizeOfHeaders) {
            size = pinh->OptionalHeader.SizeOfHeaders;
        }
    }
    else if (pinh64->OptionalHeader.Magic == IMAGE_NT_OPTIONAL_HDR64_MAGIC) {
        base = (uintptr)pinh64->OptionalHeader.ImageBase;

        if (size < pinh->OptionalHeader.SizeOfHeaders) {
            size = pinh->OptionalHeader.SizeOfHeaders;
        }
    }
    else {
        return 0;
    }

    IMAGE_SECTION_HEADER * pish = (IMAGE_SECTION_HEADER *)
        (((uintptr)&pinh->OptionalHeader) + pinh->FileHeader.SizeOfOptionalHeader);
    for (int i = 0; i < pinh->FileHeader.NumberOfSections; i++) {
        uint8* pbDst = (uint8 *)base + pish[i].VirtualAddress;
        uint8* pbSrc = pbImage + pish[i].PointerToRawData;
        uint32 cbSrc = (pish[i].VirtualSize < pish[i].SizeOfRawData)
            ? pish[i].VirtualSize : pish[i].SizeOfRawData;

        if (size < pish[i].VirtualAddress + pish[i].VirtualSize) {
            size = pish[i].VirtualAddress + pish[i].VirtualSize;
        }
    }
    return size;
}

uintptr ExpandPeImage(uintptr dst, uintptr src)
{
    UINT8 * pbImage = (UINT8 *)src;

    IMAGE_DOS_HEADER * pidh = (IMAGE_DOS_HEADER *)pbImage;
    if (pidh->e_magic != IMAGE_DOS_SIGNATURE) {
        printf("Mismatch MZ Signature: %04x != %04x\n",
               pidh->e_magic, IMAGE_DOS_SIGNATURE);
        return 0;
    }

    IMAGE_NT_HEADERS32 * pinh = (IMAGE_NT_HEADERS32 *)(pbImage + pidh->e_lfanew);
    IMAGE_NT_HEADERS64 * pinh64 = (IMAGE_NT_HEADERS64 *)(pbImage + pidh->e_lfanew);
    if (pinh->Signature != IMAGE_NT_SIGNATURE) {
        printf("Mismatched NT Signature: %08x != %08x\n",
               pinh->Signature, IMAGE_NT_SIGNATURE);
        return 0;
    }

    if ((pinh->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR32_MAGIC) &&
        (pinh64->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC)) {
        printf("Mismatched PE Signature: %08x != %08x or %08x != %08x\n",
               pinh->OptionalHeader.Magic, IMAGE_NT_OPTIONAL_HDR32_MAGIC,
               pinh64->OptionalHeader.Magic, IMAGE_NT_OPTIONAL_HDR64_MAGIC);
        return 0;
    }

    uintptr entry = 0;
    uintptr diff = 0;

    if (pinh->OptionalHeader.Magic == IMAGE_NT_OPTIONAL_HDR32_MAGIC) {
        diff = dst - pinh->OptionalHeader.ImageBase;
        entry = dst + pinh->OptionalHeader.AddressOfEntryPoint;

        CopyDown((uint8*)dst, pbImage, pinh->OptionalHeader.SizeOfHeaders);
    }
    else if (pinh64->OptionalHeader.Magic == IMAGE_NT_OPTIONAL_HDR64_MAGIC) {
        diff = dst - (uintptr)pinh64->OptionalHeader.ImageBase;
        entry = dst + pinh64->OptionalHeader.AddressOfEntryPoint;

        CopyDown((uint8*)dst, pbImage, pinh64->OptionalHeader.SizeOfHeaders);
    }
    else {
        printf("Forgot to update IMAGE_NT_OPTIONAL test!\n");
        return 0;
    }

    IMAGE_SECTION_HEADER * pish = (IMAGE_SECTION_HEADER *)
        (((uintptr)&pinh->OptionalHeader) + pinh->FileHeader.SizeOfOptionalHeader);
#if EXPANDPE_VERBOSE
    printf("  Section_ VirtAddr VirtSize _RawAddr _RawSize DestAddr CopySize SorcAddr\n");
#endif
    for (int i = 0; i < pinh->FileHeader.NumberOfSections; i++) {
        uint8* pbDst = (uint8 *)dst + pish[i].VirtualAddress;
        uint8* pbSrc = pbImage + pish[i].PointerToRawData;
        uint32 cbSrc = (pish[i].VirtualSize < pish[i].SizeOfRawData)
            ? pish[i].VirtualSize : pish[i].SizeOfRawData;

#if EXPANDPE_VERBOSE
        printf("  %-8.8s %08x %8x %08x %8x %8x %8x %8x\n",
               pish[i].Name,
               pish[i].VirtualAddress,
               pish[i].VirtualSize,
               pish[i].PointerToRawData,
               pish[i].SizeOfRawData,
               pbDst,
               cbSrc,
               pbSrc);
#endif

        Zero(pbDst, pish[i].VirtualSize);
        CopyDown(pbDst, pbSrc, cbSrc);
    }

    // Process the relocations.
    if (diff != 0) {
        IMAGE_DATA_DIRECTORY * pidd
            = &pinh->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_BASERELOC];

        uint8* pbReloc = (uint8*)dst + pidd->VirtualAddress;
        uint8* pbRelocEnd = pbReloc + pidd->Size;

#if EXPANDPE_VERBOSE
        printf("Relocs: %08x..%08x\n", pbReloc, pbRelocEnd);
#endif
        while (pbReloc < pbRelocEnd) {
            uint32 * ph = (uint32 *)pbReloc;

#if EXPANDPE_VERBOSE
            printf("  %08x..%08x\n", ph[0], ph[1]);
#endif
            uint16 * pr = (uint16 *)(pbReloc + 8);
            uint16 * prEnd = (uint16 *)(pbReloc + ph[1]);
            uintptr va = dst + ph[0];

            for (; pr < prEnd; pr++) {
                uintptr rva = va + (pr[0] & 0xfff);

                switch (pr[0] >> 12) {
                    case IMAGE_REL_BASED_ABSOLUTE:
#if EXPANDPE_VERBOSE
                        printf("    %p: abs:%x\n", (uint32*)rva, *(uint32*)rva);
#endif
                        break;
                    case IMAGE_REL_BASED_HIGHLOW:   // 32-bit reloc
#if EXPANDPE_VERBOSE
                        printf("    %p: r32:%x->%x\n",
                               (uint32*)rva, *(uint32*)rva, *(uint32*)rva + (uint32)diff);
#endif
                        *(uint32*)rva += (uint32)diff;
                        break;
                    case IMAGE_REL_BASED_DIR64:     // 64-bit reloc
#if EXPANDPE_VERBOSE
                        printf("    %p: r64:%lx->%lx\n",
                               (uint64*)rva, *(uint64*)rva, *(uint64*)rva + (uint64)diff);
#endif
                        *(uint64*)rva += (uint64)diff;
                        break;
                    default:
                        printf("%p: %x --- Unknown relocation type!\n", (uint32*)rva, pr[0] >> 12);
                        return 0;
                }
            }
            pbReloc = (uint8 *)prEnd;
        }
    }
    return entry;
}

// End of File.
