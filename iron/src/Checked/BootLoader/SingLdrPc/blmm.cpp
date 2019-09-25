
//

//

//

//

//

//
//--

#include "bl.h"

LIST_ENTRY BlMmPhysicalRegionList;

struct {
    BL_MM_PHYSICAL_REGION StaticArray[16];
    LIST_ENTRY FreeList;
} BlMmPhysicalRegionLookaside;

GDTR BlMmInitialGdtr;

ULONG_PTR BlMmLegacyCr3;
ULONG_PTR BlMmBootCr3;

typedef struct _BL_MM_PAGE_TABLE {
    UINT64 Entry[512];
} BL_MM_PAGE_TABLE, *PBL_MM_PAGE_TABLE;

#if defined(BOOT_X64)

__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPml4Table[1];

#endif

__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPdpTable[1];
__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPdTable[4];
__declspec(align(PAGE_SIZE)) BL_MM_PAGE_TABLE BlMmPgTable[1];

PVOID BlMmExtendedBiosDataArea;

VOID
BlMmCompactPhysicalRegionList(
    VOID
    )


//

//


//
//--

{
    PBL_MM_PHYSICAL_REGION Current;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Next;

    Head = &BlMmPhysicalRegionList;

    if (BlRtlIsListEmpty(Head) != FALSE) {

        return;
    }

    Current = CONTAINING_RECORD(Head->Flink,
                                BL_MM_PHYSICAL_REGION,
                                Entry);

    for (;;) {

        BLASSERT(Current->Size > 0);

        BLASSERT(Current->Start + Current->Size == Current->Limit);

        BLASSERT((Current->Type >= BL_MM_PHYSICAL_REGION_MIN_TYPE) && (Current->Type <= BL_MM_PHYSICAL_REGION_MAX_TYPE));

        if (Current->Entry.Flink == Head) {

            break;
        }

        Next = CONTAINING_RECORD(Current->Entry.Flink,
                                 BL_MM_PHYSICAL_REGION,
                                 Entry);

        BLASSERT(Next->Start >= Current->Limit);

        if ((Next->Start == Current->Limit) &&
            (Next->Type == Current->Type)) {

            Current->Limit = Next->Limit;
            Current->Size = Current->Limit - Current->Start;

            BlRtlRemoveEntryList(&Next->Entry);

            BlRtlInsertTailList(&BlMmPhysicalRegionLookaside.FreeList, &Next->Entry);

            continue;
        }

        Current = Next;
    }
}

VOID
BlMmInsertPhysicalRegion(
    PBL_MM_PHYSICAL_REGION Region
    )


//

//

//

//

//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Next;

    Head = &BlMmPhysicalRegionList;
    Entry = Head->Flink;

    while (Entry != Head) {

        Next = CONTAINING_RECORD(Entry,
                                 BL_MM_PHYSICAL_REGION,
                                 Entry);

        if (Next->Start > Region->Start) {

            break;
        }

        Entry = Entry->Flink;
    }

    BlRtlInsertTailList(Entry, &Region->Entry);

    BlMmCompactPhysicalRegionList();

    return;
}

VOID
BlMmCreatePhysicalRegion(
    UINT64 Start,
    UINT64 Size,
    UINT32 Type
    )


//

//

//

//

//

//

//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    UINT64 Limit;
    PBL_MM_PHYSICAL_REGION Region;

    BLASSERT((Start % PAGE_SIZE) == 0);
    BLASSERT(Size > 0);
    BLASSERT((Size % PAGE_SIZE) == 0);
    BLASSERT(Type >= BL_MM_PHYSICAL_REGION_MIN_TYPE);
    BLASSERT(Type <= BL_MM_PHYSICAL_REGION_MAX_TYPE);

    Limit = Start + Size;

    BLASSERT(Limit > Start);

    Head = &BlMmPhysicalRegionList;
    Entry = Head->Flink;

    while (Entry != Head) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if ((Start < Region->Limit) && (Limit > Region->Start)) {

            BlRtlPrintf("MM: Physical region collision!\n");
            BlRtlHalt();
        }

        Entry = Entry->Flink;
    }

    Entry = Head->Flink;

    while (Entry != Head) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if (Start < Region->Start) {

            break;
        }

        Entry = Entry->Flink;
    }

    BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

    Region = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                               BL_MM_PHYSICAL_REGION,
                               Entry);

    Region->Start = Start;
    Region->Size = Size;
    Region->Limit = Limit;
    Region->Type = Type;

    BlMmInsertPhysicalRegion(Region);

    return;
}

UINT64
BlMmAllocatePhysicalRegion(
    UINT32 Size,
    UINT32 Type
    )


//

//


//

//

//

//

//

//
//--

{
    PLIST_ENTRY Entry;
    PBL_MM_PHYSICAL_REGION FreeRegion;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    BLASSERT(Size > 0);
    BLASSERT(Type != BL_MM_PHYSICAL_REGION_FREE);

    SATISFY_OVERZEALOUS_COMPILER(Region = NULL);

    Size = ROUND_UP_TO_PAGES(Size);

    Head = &BlMmPhysicalRegionList;
    Entry = Head->Blink;

    while (Entry != Head) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if ((Region->Type == BL_MM_PHYSICAL_REGION_FREE) &&
            (Region->Size >= Size) &&
            (Region->Limit < 0x100000000UI64)) {

            break;
        }

        Entry = Entry->Blink;
    }

    if (Entry == Head) {

        BlRtlPrintf("MM: Unable to allocate %x bytes!\n", Size);
        BlRtlHalt();
    }

    if (Region->Size == Size) {

        Region->Type = Type;
        return Region->Start;
    }

    FreeRegion = Region;

    BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

    Region = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                               BL_MM_PHYSICAL_REGION,
                               Entry);

    Region->Start = FreeRegion->Limit - Size;
    FreeRegion->Limit -= Size;
    FreeRegion->Size -= Size;

    Region->Size = Size;
    Region->Limit = Region->Start + Region->Size;
    Region->Type = Type;

    BlRtlZeroMemory((PVOID) (ULONG_PTR) Region->Start, (ULONG_PTR) (UINT32) Region->Size);

    BlMmInsertPhysicalRegion(Region);

    return Region->Start;
}

BOOLEAN
BlMmAllocateSpecificPhysicalRegion(
    UINT64 Base,
    UINT64 Size,
    UINT32 Type
    )


//

//

//

//

//

//

//

//


//
//--

{
    UINT64 End;
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION NextRegion;
    PBL_MM_PHYSICAL_REGION PreviousRegion;
    PBL_MM_PHYSICAL_REGION Region;
    UINT64 Start;

    BLASSERT((Base % PAGE_SIZE) == 0);

    BLASSERT(Size > 0);

    BLASSERT((Size % PAGE_SIZE) == 0);

    BLASSERT(Type != BL_MM_PHYSICAL_REGION_FREE);

    SATISFY_OVERZEALOUS_COMPILER(Region = NULL);

    Start = Base;
    End = Start + Size;

    Head = &BlMmPhysicalRegionList;

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if ((Start >= Region->Start) && (End <= Region->Limit)) {

            break;
        }
    }

    if (Entry == Head) {

        return FALSE;
    }

    if (Region->Type != BL_MM_PHYSICAL_REGION_FREE) {

        return FALSE;
    }

    PreviousRegion = NULL;
    NextRegion = NULL;

    if (Region->Start < Start) {

        BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

        PreviousRegion = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                                           BL_MM_PHYSICAL_REGION,
                                           Entry);

        PreviousRegion->Start = Region->Start;
        PreviousRegion->Size = Start - Region->Start;
        PreviousRegion->Limit = Start;
        PreviousRegion->Type = BL_MM_PHYSICAL_REGION_FREE;
    }

    if (Region->Limit > End) {

        BLASSERT(BlRtlIsListEmpty(&BlMmPhysicalRegionLookaside.FreeList) == FALSE);

        NextRegion = CONTAINING_RECORD(BlRtlRemoveHeadList(&BlMmPhysicalRegionLookaside.FreeList),
                                       BL_MM_PHYSICAL_REGION,
                                       Entry);

        NextRegion->Start = End;
        NextRegion->Size = Region->Limit - End;
        NextRegion->Limit = Region->Limit;
        NextRegion->Type = BL_MM_PHYSICAL_REGION_FREE;
    }

    Region->Start = Start;
    Region->Size = Size;
    Region->Limit = End;
    Region->Type = Type;

    if (PreviousRegion != NULL) {

        BlMmInsertPhysicalRegion(PreviousRegion);
    }

    if (NextRegion != NULL) {

        BlMmInsertPhysicalRegion(NextRegion);
    }

    return TRUE;
}

BOOLEAN
BlMmFindFreePhysicalRegion(
    PUINT64 Base,
    PUINT64 Size
    )


//

//

//

//

//

//

//


//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    Head = &BlMmPhysicalRegionList;

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        Region = CONTAINING_RECORD(Entry,
                                   BL_MM_PHYSICAL_REGION,
                                   Entry);

        if (Region->Type == BL_MM_PHYSICAL_REGION_FREE) {

            *Base = Region->Start;
            *Size = Region->Size;
            return TRUE;
        }
    }

    return FALSE;
}

BOOLEAN
BlMmGetNextPhysicalRegion(
    PVOID *Handle,
    PUINT64 Base,
    PUINT64 Size,
    PUINT32 Type
    )


//

//

//

//



//

//

//

//

//


//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    Head = &BlMmPhysicalRegionList;

    if (*Handle == NULL) {

        Entry = Head;

    } else {

        Entry = (PLIST_ENTRY) *Handle;
    }

    Entry = Entry->Flink;

    if (Entry == Head) {

        return FALSE;
    }

    Region = CONTAINING_RECORD(Entry,
                               BL_MM_PHYSICAL_REGION,
                               Entry);

    *Handle = &Region->Entry;
    *Base = Region->Start;
    *Size = Region->Size;
    *Type = Region->Type;

    return TRUE;
}

PCHAR
BlMmPhysicalRegionTypeString(
    UINT32 Type
    )


//

//

//

//

//

//

//
//--

{

#define CASE(X) case BL_MM_PHYSICAL_REGION_##X: return #X;

    switch (Type) {

        CASE(FREE)
        CASE(BIOS)
        CASE(BOOT_LOADER)
        CASE(SMAP_RESERVED)
        CASE(DISTRO)
        CASE(KERNEL_IMAGE)
        CASE(NATIVE_PLATFORM)
        CASE(NATIVE_PROCESSOR)
        CASE(LOG_RECORD)
        CASE(LOG_TEXT)
        CASE(KERNEL_STACK)
        CASE(CONTEXT)
        CASE(TASK)
        CASE(SINGULARITY)
        CASE(BOOT_STACK)
        CASE(SINGULARITY_SMAP)
    }

#undef CASE

    BLASSERT(FALSE);
    return NULL;
}

VOID
BlMmDumpPhysicalRegionList(
    VOID
    )


//

//

//
//--

{
    PLIST_ENTRY Entry;
    PLIST_ENTRY Head;
    PBL_MM_PHYSICAL_REGION Region;

    BlRtlPrintf("MM: Physical Region:\n");

    Head = &BlMmPhysicalRegionList;

    for (Entry = Head->Flink; Entry != Head; Entry = Entry->Flink) {

        Region = CONTAINING_RECORD(Entry, BL_MM_PHYSICAL_REGION, Entry);

        BlRtlPrintf("MM:   %016I64x...%016I64x %s\n",
                    Region->Start,
                    Region->Limit,
                    BlMmPhysicalRegionTypeString(Region->Type));
    }

    BlRtlPrintf("\n");

    return;
}

//

//

VOID
BlMmInitializePageTables(
    VOID
    )


//

//

//
//--

{
    UINT64 Index;
    UINT64 *Pde;
    UINT64 PdtBase;
    UINT64 *Pdpe;
    UINT64 PdptBase;

#if defined(BOOT_X64)

    UINT64 *Pml4e;
    UINT64 Pml4tBase;

#endif

    UINT64 *Pte;
    UINT64 PtBase;

#if defined(BOOT_X64)

    Pml4tBase = (UINT64) (ULONG_PTR) BlMmPml4Table;

#endif

    PdptBase = (UINT64) (ULONG_PTR) BlMmPdpTable;
    PdtBase = (UINT64) (ULONG_PTR) BlMmPdTable;
    PtBase = (UINT64) (ULONG_PTR) BlMmPgTable;

#if defined(BOOT_X64)

    Pml4e = (UINT64 *) (PVOID) Pml4tBase;

#endif

    Pdpe = (UINT64 *) (PVOID) (ULONG_PTR) PdptBase;
    Pde = (UINT64 *) (PVOID) (ULONG_PTR) PdtBase;
    Pte = (UINT64 *) (PVOID) (ULONG_PTR) PtBase;

#if defined(BOOT_X64)

    Pml4e[0] = PdptBase | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;

#endif

    for (Index = 0; Index < 4; Index += 1) {

        Pdpe[Index] = (PdtBase + (Index * PAGE_SIZE)) | PAGE_PRESENT;

#if defined(BOOT_X64)

        Pdpe[Index] |= PAGE_WRITEABLE | PAGE_ACCESSED;

#endif

    }

    Pde[0] = PtBase | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;

    for (Index = 1; Index < 512; Index += 1) {

        Pte[Index] = (Index << 12) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;
    }

    for (Index = 1; Index < 2048; Index += 1) {

        Pde[Index] = (Index << 21) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED | PAGE_2MB;
    }

#if defined(BOOT_X86)

    BlMmBootCr3 = (ULONG_PTR) PdptBase;

#elif defined(BOOT_X64)

    BlMmBootCr3 = Pml4tBase;

#endif

    BlMmSetCr3(BlMmBootCr3);

    BlGetBeb()->LegacyReturnCr3 = (UINT32) BlMmBootCr3;

#if MM_VERBOSE

    BlRtlPrintf("MM: 4GB identity map [CR3=%p]\n", BlMmBootCr3);

#endif

    return;
}

VOID
BlMmMapVirtualPage(
    PVOID VirtualAddress,
    PVOID PhysicalAddress,
    BOOLEAN Writeable,
    BOOLEAN Cacheable,
    BOOLEAN WriteThrough
    )


//

//

//

//

//

//

//

//

//
//--

{
    UINT64 Entry;
    UINT32 Index;
    UINT64 LargePageAddress;
    PUINT64 PdBase;
    UINT32 PdIndex;
    PUINT64 PdpBase;
    UINT32 PdpIndex;
    UINT64 PhysicalPageNumber;
    PUINT64 PtBase;
    UINT32 PtIndex;
    ULONG_PTR VirtualPageNumber;

    BLASSERT((((ULONG_PTR) VirtualAddress) & 0xFFF) == 0);

    BLASSERT((((ULONG_PTR) PhysicalAddress) & 0xFFF) == 0);

#if defined(BOOT_X64)

    BLASSERT((ULONG_PTR) VirtualAddress < 0x100000000UI64);

#endif

    //
    
    //

    VirtualPageNumber = ((ULONG_PTR) VirtualAddress) / PAGE_SIZE;

    PdpIndex = (UINT32) ((VirtualPageNumber >> 18) & 0x1FF);
    PdIndex = (UINT32) ((VirtualPageNumber >> 9) & 0x1FF);
    PtIndex = (UINT32) (VirtualPageNumber & 0x1FF);

    //
    
    //

    PdpBase = &BlMmPdpTable[0].Entry[0];

    PdBase = (PUINT64) (ULONG_PTR) (PdpBase[PdpIndex] & (~(0xFFFUI64)));

    //
    
    //

    if ((PdBase[PdIndex] & PAGE_2MB) != 0) {

        PtBase = (PUINT64) (ULONG_PTR) BlMmAllocatePhysicalRegion(PAGE_SIZE, BL_MM_PHYSICAL_REGION_BOOT_LOADER);

        LargePageAddress = (PdBase[PdIndex] & (~(0xFFFUI64)));

        BLASSERT(((LargePageAddress >> 12) & 0x1FF) == 0);

        //
        
        //

        for (Index = 0; Index < 512; Index += 1) {

            PtBase[Index] = (LargePageAddress + (Index * PAGE_SIZE)) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;
        }

        //
        
        //

        PdBase[PdIndex] = ((UINT64) (ULONG_PTR) PtBase) | PAGE_PRESENT | PAGE_WRITEABLE | PAGE_ACCESSED;

        //
        
        //

        BlMmSetCr3(BlMmBootCr3);
    }

    //
    
    //

    PtBase = (PUINT64) (ULONG_PTR) (PdBase[PdIndex] & (~(0xFFFUI64)));

    PhysicalPageNumber = ((ULONG_PTR) PhysicalAddress) >> 12;

    Entry = (PhysicalPageNumber << 12) | PAGE_PRESENT;

    if (Writeable != FALSE) {

        Entry |= PAGE_WRITEABLE;
    }

    if (Cacheable == FALSE) {

        Entry |= PAGE_CACHEDISABLE;

    } else if (WriteThrough != FALSE) {

        Entry |= PAGE_WRITETHROUGH;
    }

    PtBase[PtIndex] = Entry;

    //
    
    //

    BlMmSetCr3(BlMmBootCr3);

    return;
}

VOID
BlMmMapVirtualRange(
    PVOID VirtualAddress,
    PVOID PhysicalAddress,
    ULONG_PTR Size,
    BOOLEAN Writeable,
    BOOLEAN Cacheable,
    BOOLEAN WriteThrough
    )


//

//

//

//

//

//

//

//

//

//
//--

{
    ULONG_PTR PhysicalNext;
    ULONG_PTR VirtualLimit;
    ULONG_PTR VirtualNext;

    VirtualNext = (ULONG_PTR) VirtualAddress;
    VirtualLimit = VirtualNext + Size;

    VirtualNext &= (~((ULONG_PTR) 0xFFF));
    VirtualLimit = ROUND_UP_TO_PAGES(VirtualLimit);

    PhysicalNext = (ULONG_PTR) PhysicalAddress;
    PhysicalNext &= (~((ULONG_PTR) 0xFFF));

    while (VirtualNext < VirtualLimit) {

        BlMmMapVirtualPage((PVOID) VirtualNext,
                           (PVOID) PhysicalNext,
                           Writeable,
                           Cacheable,
                           WriteThrough);

        VirtualNext += PAGE_SIZE;
        PhysicalNext += PAGE_SIZE;
    }

    return;
}

VOID
BlMmInitializeCodeSegment(
    PCODE_SEGMENT CodeSegment
    )


//

//

//

//

//
//--

{
    BlRtlZeroMemory(CodeSegment, sizeof(CODE_SEGMENT));

    CodeSegment->Accessed = 1;
    CodeSegment->Readable = 1;
    CodeSegment->Code = 1;
    CodeSegment->S = 1;
    CodeSegment->Present = 1;
    CodeSegment->Long = 1;

    return;
}

VOID
BlMmInitializeDataSegment(
    PDATA_SEGMENT DataSegment,
    UINT32 Base,
    UINT32 Limit
    )


//

//

//

//

//

//

//
//--

{
    BlRtlZeroMemory(DataSegment, sizeof(DATA_SEGMENT));

    DataSegment->Accessed = 1;
    DataSegment->Writable = 1;
    DataSegment->S = 1;
    DataSegment->Present = 1;
    DataSegment->Big = 1;

    DataSegment->Base_23_0 = Base & 0xFFFFFF;
    DataSegment->Base_31_24 = Base >> 24;

    if (Limit <= 0xFFFFF) {

        DataSegment->Limit_15_0 = Limit & 0xFFFF;
        DataSegment->Limit_19_16 = (Limit >> 16) & 0xF;

    } else {

        DataSegment->Granularity = 1;
        DataSegment->Limit_15_0 = (Limit >> 12) & 0xFFFF;
        DataSegment->Limit_19_16 = (Limit >> 28) & 0xF;
    }

    return;
}

VOID
BlMmInitializeSystemSegment(
    PSYSTEM_SEGMENT SystemSegment,
    UINT32 Type,
    ULONG_PTR Base,
    UINT32 Limit
    )


//

//

//

//

//

//

//

//
//--

{
    BlRtlZeroMemory(SystemSegment, sizeof(SYSTEM_SEGMENT));

    SystemSegment->Type = (Type & 0xF);
    SystemSegment->Present = 1;

    SystemSegment->Base_23_0 = Base & 0xFFFFFF;
    SystemSegment->Base_31_24 = (Base >> 24) & 0xFF;

#if defined(BOOT_X64)

    SystemSegment->Base_63_32 = Base >> 32;

#endif

    if (Limit <= 0xFFFFF) {

        SystemSegment->Limit_15_0 = Limit & 0xFFFF;
        SystemSegment->Limit_19_16 = (Limit >> 16) & 0xF;

    } else {

        SystemSegment->Granularity = 1;
        SystemSegment->Limit_15_0 = (Limit >> 12) & 0xFFFF;
        SystemSegment->Limit_19_16 = (Limit >> 28) & 0xF;
    }

    return;
}

#if !defined(BOOT_PXE)
VOID
BlMmEnableA20Gate(
    VOID
    )


//

//

//
//--

{
    BL_KEYBOARD_WRITE_OUTPUT_PORT(BL_KEYBOARD_A20_ENABLE);

    BL_KEYBOARD_WRITE_COMMAND(BL_KEYBOARD_COMMAND_PULSE_OUTPUT_PORT);

    return;
}
#endif

PVOID
BlMmGetExtendedBiosDataArea(
    VOID
    )


//

//

//

//

//
//--

{
    UINT16 Segment;

    Segment = *((PUINT16) (ULONG_PTR) 0x40E);

    return (PVOID) (((ULONG_PTR) Segment) << 4);
}

VOID
BlMmInitializeSystem(
    VOID
    )


//

//

//
//--

{
    UINT64 Delta;
    UINT32 Index;
    PBL_MM_PHYSICAL_REGION PhysicalRegion;
    PBL_SMAP_ENTRY SmapEntry;

#if !defined(BOOT_PXE)
    //
    
    //

    BlMmEnableA20Gate();
#endif

    //
    
    //

    BlMmExtendedBiosDataArea = BlMmGetExtendedBiosDataArea();

    //
    
    //

    BlMmLegacyCr3 = BlMmGetCr3();

    //
    
    //

    BlMmGetGdtr(&BlMmInitialGdtr);

    //
    
    //

    BlSmapInitialize();

    //
    
    //

    BlRtlInitializeListHead(&BlMmPhysicalRegionList);

    BlRtlInitializeListHead(&BlMmPhysicalRegionLookaside.FreeList);

    for (Index = 0; Index < (sizeof(BlMmPhysicalRegionLookaside.StaticArray) / sizeof(BlMmPhysicalRegionLookaside.StaticArray[0])); Index += 1) {

        BlRtlInsertTailList(&BlMmPhysicalRegionLookaside.FreeList, &BlMmPhysicalRegionLookaside.StaticArray[Index].Entry);
    }

    //
    
    //

    BlMmInitializePageTables();

    //
    
    //

    BlMmCreatePhysicalRegion(0,
                             BL_MM_BIOS_SIZE,
                             BL_MM_PHYSICAL_REGION_BIOS);

    //
    
    //

    for (Index = 0; Index < BlSystemMemoryMap.EntryCount; Index += 1) {

        SmapEntry = &BlSystemMemoryMap.Entry[Index];

        //
        
        //

        if ((SmapEntry->Type == BL_SMAP_AVAILABLE) &&
            (SmapEntry->Base >= BL_MM_BIOS_SIZE) &&
            (SmapEntry->Base < 0x80000000UI64)
            ) {

            if ((SmapEntry->Base % PAGE_SIZE) != 0) {

                Delta = PAGE_SIZE - (SmapEntry->Base % PAGE_SIZE);
                SmapEntry->Base += Delta;
                SmapEntry->Size -= Delta;
            }

            SmapEntry->Size &= (~(0xFFFUI64));

            if ((SmapEntry->Base + SmapEntry->Size) > 0x80000000UI64) {

                SmapEntry->Size = 0x80000000UI64 - SmapEntry->Base;
            }

            if (SmapEntry->Size > 0) {

                BlMmCreatePhysicalRegion(SmapEntry->Base,
                                         SmapEntry->Size,
                                         BL_MM_PHYSICAL_REGION_FREE);
            }
        }
    }

    //
    
    //

    BlPoolInitialize();

    //
    
    //

    for (Index = 0; Index < 256; Index += 1) {

        PhysicalRegion = (PBL_MM_PHYSICAL_REGION)
            BlPoolAllocateBlock(sizeof(BL_MM_PHYSICAL_REGION));

        BlRtlInsertTailList(&BlMmPhysicalRegionLookaside.FreeList, &PhysicalRegion->Entry);
    }

    return;
}
