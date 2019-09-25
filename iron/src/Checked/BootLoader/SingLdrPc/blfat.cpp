
//

//

//

//

//

//
//--

#include "bl.h"

//

//

#pragma pack(1)

#define MBR_BOOTABLE                    0x80

typedef struct _MBR_PARTITION {
    UINT8 Status;
    UINT8 FirstSectorCHS[3];
    UINT8 Type;
    UINT8 LastSectorCHS[3];
    UINT32 FirstSector;
    UINT32 NumberOfSectors;
} MBR_PARTITION, *PMBR_PARTITION;

C_ASSERT(sizeof(MBR_PARTITION) == 16);

#define MBR_SIGNATURE                   0xAA55

typedef struct _MBR {
    UINT8 BootCode[446];
    MBR_PARTITION Partition[4];
    UINT16 Signature;
} MBR, *PMBR;

C_ASSERT(sizeof(MBR) == 512);

#pragma pack()

//

//

#define FAT_SECTOR_SIZE                 512
#define FAT_FIRST_DATA_CLUSTER          2

#define FAT16_CLUSTER_MASK              0xFFFF
#define FAT16_LINK_TERMINATOR           0xFFFF

#define FAT32_CLUSTER_MASK              0x0FFFFFFF
#define FAT32_LINK_TERMINATOR           0x0FFFFFFF


#pragma pack(1)

typedef struct __declspec(align(FAT_SECTOR_SIZE)) _FAT_SECTOR {
    UINT8 Data[FAT_SECTOR_SIZE];
} FAT_SECTOR, *PFAT_SECTOR;

typedef struct _FAT16_BOOT_SECTOR {
    UINT8 JumpInstruction[3];
    UINT8 OemName[8];
    UINT16 BytesPerSector;
    UINT8 SectorsPerCluster;
    UINT16 NumberOfReservedSectors;
    UINT8 NumberOfFATs;
    UINT16 NumberOfRootDirectoryEntries;
    UINT16 TotalSectorCount16;
    UINT8 Media;
    UINT16 SectorsPerFAT;
    UINT16 SectorsPerTrack;
    UINT16 NumberOfHeads;
    UINT32 NumberOfHiddenSectors;
    UINT32 TotalSectorCount32;
    UINT8 DriveNumber;
    UINT8 Reserved1;
    UINT8 ExtendedBootSignature;
    UINT32 VolumeSerialNumber;
    UINT8 VolumeLabel[11];
    UINT8 FileSystemType[8];
    UINT8 BootCode[448];
    UINT16 Signature;
} FAT16_BOOT_SECTOR, *PFAT16_BOOT_SECTOR;

C_ASSERT(sizeof(FAT16_BOOT_SECTOR) == FAT_SECTOR_SIZE);

typedef struct _FAT32_BOOT_SECTOR {
    UINT8 JumpInstruction[3];
    UINT8 OemName[8];
    UINT16 BytesPerSector;
    UINT8 SectorsPerCluster;
    UINT16 NumberOfReservedSectors;
    UINT8 NumberOfFATs;
    UINT16 NumberOfRootDirectoryEntries;
    UINT16 TotalSectorCount16;
    UINT8 Media;
    UINT16 SectorsPerFAT16;
    UINT16 SectorsPerTrack;
    UINT16 NumberOfHeads;
    UINT32 NumberOfHiddenSectors;
    UINT32 TotalSectorCount32;
    UINT32 SectorsPerFAT32;
    UINT16 Flags;
    UINT16 FileSystemVersion;
    UINT32 RootDirectoryFirstCluster;
    UINT16 FileSystemInfoSector;
    UINT16 BackupBootSector;
    UINT8 Reserved[12];
    UINT8 DriveNumber;
    UINT8 Reserved1;
    UINT8 ExtendedBootSignature;
    UINT32 VolumeSerialNumber;
    UINT8 VolumeLabel[11];
    UINT8 FileSystemType[8];
    UINT8 BootCode[420];
    UINT16 Signature;
} FAT32_BOOT_SECTOR, *PFAT32_BOOT_SECTOR;

C_ASSERT(sizeof(FAT32_BOOT_SECTOR) == FAT_SECTOR_SIZE);

typedef struct _FAT_BOOT_SECTOR {
    union {
        FAT16_BOOT_SECTOR Fat16;
        FAT32_BOOT_SECTOR Fat32;
    } u1;
} FAT_BOOT_SECTOR, *PFAT_BOOT_SECTOR;

C_ASSERT(sizeof(FAT_BOOT_SECTOR) == FAT_SECTOR_SIZE);

#define FAT_DIRECTORY_ENTRY_FREE        0xE5
#define FAT_DIRECTORY_ENTRY_LAST        0x00

#define FAT_ATTRIBUTE_READ_ONLY         0x01
#define FAT_ATTRIBUTE_HIDDEN            0x02
#define FAT_ATTRIBUTE_SYSTEM            0x04
#define FAT_ATTRIBUTE_VOLUME_ID         0x08
#define FAT_ATTRIBUTE_DIRECTORY         0x10
#define FAT_ATTRIBUTE_ARCHIVE           0x20
#define FAT_ATTRIBUTE_LONG_NAME         (FAT_ATTRIBUTE_READ_ONLY | FAT_ATTRIBUTE_HIDDEN | FAT_ATTRIBUTE_SYSTEM | FAT_ATTRIBUTE_VOLUME_ID)
#define FAT_ATTRIBUTE_MASK              0x3F

#define FAT_LONG_NAME_TERMINATOR        0x40
#define FAT_LONG_NAME_ORDER_MASK        0x3F

typedef struct _FAT_DIRECTORY_ENTRY {
    union {
        struct {
            UINT8 Name[11];
            UINT8 Attribute;
            UINT8 ReservedForNT;
            UINT8 CreationTime[3];
            UINT8 CreationDate[2];
            UINT8 LastAccessDate[2];
            UINT16 FirstClusterHigh;
            UINT8 ModificationTime[2];
            UINT8 ModificationDate[2];
            UINT16 FirstClusterLow;
            UINT32 Size;
        } Short;
        struct {
            UINT8 Order;
            WCHAR NameW1_5[5];
            UINT8 Attribute;
            UINT8 Type;
            UINT8 Checksum;
            WCHAR NameW6_11[6];
            UINT16 Zero;
            WCHAR NameW12_13[2];
        } Long;
    } u1;
} FAT_DIRECTORY_ENTRY, *PFAT_DIRECTORY_ENTRY;

C_ASSERT(sizeof(FAT_DIRECTORY_ENTRY) == 32);

#define FAT_MAX_PATH                    255

typedef struct _FAT_NAME {
    UINT8 ShortName[13];
    UINT8 LongName[FAT_MAX_PATH + 1];
} FAT_NAME, *PFAT_NAME;

#pragma pack()


FAT_BOOT_SECTOR BlFatBootSector;
UINT32 BlFatBytesPerCluster;
UINT32 BlFatDataStart;
UINT8 BlFatDriveId;
INT13_DRIVE_PARAMETERS BlFatDriveParameters;
UINT32 BlFatLinkTerminator;
MBR BlFatMbr;
UINT32 BlFatNumberOfDataClusters;
UINT32 BlFatNumberOfRootDirectoryEntries;
UINT32 BlFatPartitionId;
UINT32 BlFatPartitionStart;
UINT32 BlFatPartitionSize;
PFAT_DIRECTORY_ENTRY BlFatRootDirectory;
UINT32 BlFatRootStart;
UINT32 BlFatSectorsPerCluster;
UINT32 BlFatTableStart;
FAT_SECTOR BlFatTemporaryBlock[64];
UINT16 BlFatTemporaryBlockCount = sizeof(BlFatTemporaryBlock) / sizeof(BlFatTemporaryBlock[0]);
UINT32 BlFatTotalSectorCount;

#define FAT_IS_DATA_CLUSTER(X)          (((X) >= FAT_FIRST_DATA_CLUSTER) && (((X) - FAT_FIRST_DATA_CLUSTER) < BlFatNumberOfDataClusters))
#define FAT_DATA_CLUSTER_TO_SECTOR(X)   (BlFatDataStart + (((X) - 2) * BlFatSectorsPerCluster))
#define FAT_IS_TERMINATOR(X)            (((UINT32) (X)) == BlFatLinkTerminator)
#define BlFatHalt()                     BlFatHaltInternal(__LINE__)

BOOLEAN
(*BlFatGetNextCluster)(
    UINT32 Cluster,
    PUINT32 NextCluster
    );

VOID
BlFatHaltInternal(
    UINT32 Line
    )


//

//

//
//--

{
    BlRtlPrintf("FAT: Error reading disk image!\n");
    BlRtlHaltInternal(__FILE__, Line);
}

BOOLEAN
BlFatReadSector(
    UINT32 FirstSector,
    UINT32 NumberOfSectors,
    PFAT_SECTOR Buffer
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
    UINT16 StepSize;

    BLASSERT_PTR(FirstSector < BlFatTotalSectorCount, FirstSector);

    BLASSERT(NumberOfSectors > 0);

    BLASSERT(FirstSector + NumberOfSectors > FirstSector);

    BLASSERT((FirstSector + NumberOfSectors) < BlFatTotalSectorCount);

    while (NumberOfSectors > 0) {

        if (NumberOfSectors < BlFatTemporaryBlockCount) {

            StepSize = (UINT16) NumberOfSectors;

        } else {

            StepSize = BlFatTemporaryBlockCount;
        }

        if (BlRtlReadDrive(BlFatDriveId,
                           BlFatPartitionStart + FirstSector,
                           StepSize,
                           BlFatTemporaryBlock) == FALSE) {

#if FAT_VERBOSE

            BlRtlPrintf("FAT: I/O error reading sector %u on drive 0x%02x!\n",
                        BlFatPartitionStart + FirstSector,
                        BlFatDriveId);

#endif

            return FALSE;
        }

        BlRtlCopyMemory(Buffer,
                        BlFatTemporaryBlock,
                        StepSize * FAT_SECTOR_SIZE);

        FirstSector += StepSize;
        NumberOfSectors -= StepSize;
        Buffer += StepSize;
    }

    return TRUE;
}

BOOLEAN
BlFatDirectoryEntryToName(
    PFAT_DIRECTORY_ENTRY ShortEntry,
    PFAT_NAME Name,
    PFAT_DIRECTORY_ENTRY TableStart
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
    UINT8 Character;
    PFAT_DIRECTORY_ENTRY Entry;
    UINT8 LongNameComponentIndex;
    UINT32 SourceIndex;
    UINT32 TargetIndex;

    if ((ShortEntry->u1.Short.Attribute & FAT_ATTRIBUTE_MASK) == FAT_ATTRIBUTE_LONG_NAME) {

        return FALSE;
    }

    //
    
    //

    TargetIndex = 0;

    for (SourceIndex = 0; SourceIndex < 8; SourceIndex += 1) {

        Character = ShortEntry->u1.Short.Name[SourceIndex];

        if (Character == ' ') {

            if (SourceIndex == 0) {

                return FALSE;
            }

            break;
        }

        if (Character == '.') {

            return FALSE;
        }

        Name->ShortName[TargetIndex] = Character;
        TargetIndex += 1;
    }

    if (ShortEntry->u1.Short.Name[8] != ' ') {

        Name->ShortName[TargetIndex] = '.';
        TargetIndex += 1;

        for (SourceIndex = 8; SourceIndex < 11; SourceIndex += 1) {

            Character = ShortEntry->u1.Short.Name[SourceIndex];

            if (Character == ' ') {

                break;
            }

            if (Character == '.') {

                return FALSE;
            }

            Name->ShortName[TargetIndex] = Character;
            TargetIndex += 1;
        }
    }

    Name->ShortName[TargetIndex] = 0;

    //
    
    
    //

    Name->LongName[0] = 0;

    Entry = ShortEntry - 1;

    if (Entry < TableStart) {

        return TRUE;
    }

    if ((Entry->u1.Short.Attribute & FAT_ATTRIBUTE_MASK) != FAT_ATTRIBUTE_LONG_NAME) {

        return TRUE;
    }

    LongNameComponentIndex = 1;
    TargetIndex = 0;

    for (;;) {

        if (TargetIndex == FAT_MAX_PATH) {

            return FALSE;
        }

        if (Entry < TableStart) {

            return FALSE;
        }

        if ((Entry->u1.Long.Order & FAT_LONG_NAME_ORDER_MASK) != LongNameComponentIndex) {

            return FALSE;
        }

#define ADD_CHARACTER(C)                                \
                                                        \
        if (TargetIndex == FAT_MAX_PATH) {              \
                                                        \
            return FALSE;                               \
        }                                               \
                                                        \
        if (((C) != 0) && ((C) != 0xFFFF)) {            \
                                                        \
            Name->LongName[TargetIndex] = (UINT8) (C);  \
            TargetIndex += 1;                           \
        }

        ADD_CHARACTER(Entry->u1.Long.NameW1_5[0]);
        ADD_CHARACTER(Entry->u1.Long.NameW1_5[1]);
        ADD_CHARACTER(Entry->u1.Long.NameW1_5[2]);
        ADD_CHARACTER(Entry->u1.Long.NameW1_5[3]);
        ADD_CHARACTER(Entry->u1.Long.NameW1_5[4]);
        ADD_CHARACTER(Entry->u1.Long.NameW6_11[0]);
        ADD_CHARACTER(Entry->u1.Long.NameW6_11[1]);
        ADD_CHARACTER(Entry->u1.Long.NameW6_11[2]);
        ADD_CHARACTER(Entry->u1.Long.NameW6_11[3]);
        ADD_CHARACTER(Entry->u1.Long.NameW6_11[4]);
        ADD_CHARACTER(Entry->u1.Long.NameW6_11[5]);
        ADD_CHARACTER(Entry->u1.Long.NameW12_13[0]);
        ADD_CHARACTER(Entry->u1.Long.NameW12_13[1]);

#undef ADD_CHARACTER

        if ((Entry->u1.Long.Order & FAT_LONG_NAME_TERMINATOR)) {

            break;
        }

        Entry -= 1;
        LongNameComponentIndex += 1;
    }

    Name->LongName[TargetIndex] = 0;

    return TRUE;
}

PFAT_DIRECTORY_ENTRY
BlFatFindDirectoryTableEntry(
    PFAT_DIRECTORY_ENTRY Table,
    UINT32 NumberOfEntries,
    PCSTR Name
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
    PFAT_DIRECTORY_ENTRY Entry;
    FAT_NAME EntryName;
    PFAT_DIRECTORY_ENTRY Limit;

    BLASSERT(Name[0] != 0);

    Limit = Table + NumberOfEntries;

    for (Entry = Table; Entry != Limit; Entry += 1) {

        if (Entry->u1.Short.Name[0] == FAT_DIRECTORY_ENTRY_FREE) {

            continue;
        }

        if (Entry->u1.Short.Name[0] == FAT_DIRECTORY_ENTRY_LAST) {

            break;
        }

        if (Entry->u1.Short.Name[0] == '.') {

            continue;
        }

        if ((Entry->u1.Short.Attribute & FAT_ATTRIBUTE_MASK) == FAT_ATTRIBUTE_VOLUME_ID) {

            continue;
        }

        if (BlFatDirectoryEntryToName(Entry,
                                      &EntryName,
                                      Table) != FALSE) {

            if ((BlRtlEqualStringI(Name, (PCSTR) EntryName.ShortName) != FALSE) ||
                (BlRtlEqualStringI(Name, (PCSTR) EntryName.LongName) != FALSE)) {

                return Entry;
            }
        }
    }

    return NULL;
}

BOOLEAN
BlFatGetLengthClusterChain(
    UINT32 Cluster,
    PUINT32 Length
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
    *Length = 0;

    do {

        if (FAT_IS_DATA_CLUSTER(Cluster) == FALSE) {

            return FALSE;
        }

        if (BlFatGetNextCluster(Cluster, &Cluster) == FALSE) {

            return FALSE;
        }

        *Length += 1;

    } while (Cluster != BlFatLinkTerminator);

    return TRUE;
}

BOOLEAN
BlFatReadClusterChain(
    UINT32 Cluster,
    UINT32 BytesToRead,
    PVOID Buffer
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
    PVOID ClusterData;
    PUINT8 Next;
    UINT32 Sector;

    BLASSERT_PTR(FAT_IS_DATA_CLUSTER(Cluster) != FALSE, Cluster);

    BLASSERT(BytesToRead > 0);

    Next = (PUINT8) Buffer;

    for (;;) {

        //
        
        //

        if (FAT_IS_DATA_CLUSTER(Cluster) == FALSE) {

#if FAT_VERBOSE

            BlRtlPrintf("FAT: ReadClusterChain: Cluster %u is out of range!\n", Cluster);

#endif

            return FALSE;
        }

        //
        
        //

        Sector = FAT_DATA_CLUSTER_TO_SECTOR(Cluster);

        //
        
        
        
        //

        if (BytesToRead < BlFatBytesPerCluster) {

            ClusterData = BlPoolAllocateBlock(BlFatBytesPerCluster);

            if (BlFatReadSector(Sector,
                                ROUND_UP_TO_POWER2(BytesToRead, FAT_SECTOR_SIZE) / FAT_SECTOR_SIZE,
                                (PFAT_SECTOR) ClusterData) == FALSE) {

                BlPoolFreeBlock(ClusterData);

                return FALSE;
            }

            BlRtlCopyMemory(Next,
                            ClusterData,
                            BytesToRead);

            BlPoolFreeBlock(ClusterData);

            return TRUE;
        }

        //
        
        //

        if (BlFatReadSector(Sector,
                            BlFatSectorsPerCluster,
                            (PFAT_SECTOR) Next) == FALSE) {

            return FALSE;
        }

        BytesToRead -= BlFatBytesPerCluster;
        Next += BlFatBytesPerCluster;

        if (BytesToRead == 0) {

            return TRUE;
        }

        //
        
        //

        if (BlFatGetNextCluster(Cluster, &Cluster) == FALSE) {

            return FALSE;
        }
    }
}

BOOLEAN
BlFatFindFileEntry(
    PCSTR Path,
    PFAT_DIRECTORY_ENTRY FileEntry
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
    UINT32 DirectoryCluster;
    UINT32 DirectoryClusterCount;
    UINT32 Depth;
    FAT_DIRECTORY_ENTRY Entry;
    PFAT_DIRECTORY_ENTRY Match;
    PCSTR Next;
    PFAT_DIRECTORY_ENTRY Table;
    UINT32 TableSize;
    UINT8 Token[FAT_MAX_PATH];
    UINT32 TokenIndex;

    if ((Path[0] == 0) ||
        (Path[0] == '/') ||
        (BlRtlStringLength(Path) >= FAT_MAX_PATH)) {

        return FALSE;
    }

    Next = Path;
    Depth = 0;

    SATISFY_OVERZEALOUS_COMPILER(BlRtlZeroMemory(&Entry, sizeof(Entry)));

    for (;;) {

        if (*Next == 0) {

            if ((Entry.u1.Short.Attribute & FAT_ATTRIBUTE_DIRECTORY) != 0) {

#if FAT_VERBOSE

                BlRtlPrintf("FAT: FindFileEntry: %s is a directory!\n", Path);

#endif

                return FALSE;
            }

            *FileEntry = Entry;

            return TRUE;
        }

        //
        
        //

        if (*Next == '/') {

#if FAT_VERBOSE

            BlRtlPrintf("FAT: FindFileEntry: %s is a malformed path!\n", Path);

#endif

            return FALSE;
        }

        //
        
        //

        TokenIndex = 0;

        for (;;) {

            if (*Next == 0) {

                break;
            }

            if (*Next == '/') {

                Next += 1;

                break;
            }

            Token[TokenIndex] = *Next;
            TokenIndex += 1;
            Next += 1;
        }

        BLASSERT(TokenIndex > 0);

        Token[TokenIndex] = 0;

        if (Depth == 0) {

            Table = BlFatRootDirectory;
            TableSize = BlFatNumberOfRootDirectoryEntries;

        } else {

            DirectoryCluster = Entry.u1.Short.FirstClusterLow;

            if (BlFatGetLengthClusterChain(DirectoryCluster, &DirectoryClusterCount) == FALSE) {

                return FALSE;
            }

            Table = (PFAT_DIRECTORY_ENTRY)
                BlPoolAllocateBlock(DirectoryClusterCount * BlFatBytesPerCluster);

            if (BlFatReadClusterChain(DirectoryCluster,
                                      DirectoryClusterCount * BlFatBytesPerCluster,
                                      Table) == FALSE) {

                BlPoolFreeBlock(Table);

                return FALSE;
            }

            TableSize = (DirectoryClusterCount * BlFatBytesPerCluster) / sizeof(FAT_DIRECTORY_ENTRY);
        }

        //
        
        //

        Match = BlFatFindDirectoryTableEntry(Table,
                                             TableSize,
                                             (PCSTR) Token);

        if (Match == NULL) {

#if FAT_VERBOSE

            BlRtlPrintf("FAT: FindFileEntry: Unable to find directory entry for token %s.\n", Token);

#endif

            if (Table != BlFatRootDirectory) {

                BlPoolFreeBlock(Table);
            }

            return FALSE;
        }

        Entry = *Match;

        if (Table != BlFatRootDirectory) {

            BlPoolFreeBlock(Table);
        }

        Depth += 1;
    }
}

BOOLEAN
BlFatGetFileSize(
    PCSTR Path,
    PUINT32 FileSize
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
    FAT_DIRECTORY_ENTRY Entry;

    if (BlFatFindFileEntry(Path, &Entry) == FALSE) {

        return FALSE;
    }

    *FileSize = Entry.u1.Short.Size;

    return TRUE;
}

BOOLEAN
BlFatReadFile(
    PCSTR Path,
    PVOID Buffer,
    UINT32 NumberOfBytes
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
    FAT_DIRECTORY_ENTRY Entry;
    BOOLEAN Result;

    if (BlFatFindFileEntry(Path, &Entry) == FALSE) {

        return FALSE;
    }

    if (NumberOfBytes > Entry.u1.Short.Size) {

        return FALSE;
    }

    Result = BlFatReadClusterChain(Entry.u1.Short.FirstClusterLow,
                                   NumberOfBytes,
                                   Buffer);

    return Result;
}

BOOLEAN
BlFat16GetNextCluster(
    UINT32 Cluster,
    PUINT32 NextCluster
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
    UINT32 Offset;
    UINT32 Sector;
    FAT_SECTOR TablePage;

    if (FAT_IS_DATA_CLUSTER(Cluster) == FALSE) {

#if FAT_VERBOSE

        BlRtlPrintf("FAT: Fat16GetNextCluster: Cluster %u is out of range!\n", Cluster);

#endif

        return FALSE;
    }

    Sector = BlFatTableStart + (Cluster / 256);
    Offset = Cluster % 256;

    if (BlFatReadSector(Sector, 1, &TablePage) == FALSE) {

        return FALSE;
    }

    *NextCluster = (UINT32) (((PUINT16) &TablePage)[Offset]);

    return TRUE;
}

VOID
BlFat16Initialize(
    VOID
    )


//

//

//
//--

{
    PFAT16_BOOT_SECTOR BootSector;

    BootSector = &BlFatBootSector.u1.Fat16;

    BLASSERT(BlFatMbr.Partition[BlFatPartitionId].Type == MBR_FAT16LBA);

    //
    
    //

    if (BlRtlReadDrive(BlFatDriveId,
                       BlFatPartitionStart,
                       1,
                       BootSector) == FALSE) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Error reading boot sector!\n");
#endif
        BlFatHalt();
    }

    //
    
    //

    if (BootSector->BytesPerSector != FAT_SECTOR_SIZE) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Unsupported sector size (%u)!\n", BootSector->BytesPerSector);
#endif
        BlFatHalt();
    }

    BlFatSectorsPerCluster = BootSector->SectorsPerCluster;

    if (BlFatSectorsPerCluster == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: SectorsPerCluster == 0!\n");
#endif
        BlFatHalt();
    }

    BlFatBytesPerCluster = BlFatSectorsPerCluster * FAT_SECTOR_SIZE;

    if (BootSector->TotalSectorCount32 > 0) {

        BlFatTotalSectorCount = BootSector->TotalSectorCount32;

    } else {

        BlFatTotalSectorCount = BootSector->TotalSectorCount16;
    }

    if (BlFatTotalSectorCount > BlFatPartitionSize) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Boot sector claims more sectors than MBR!\n");
#endif
        BlFatHalt();
    }

    if (BootSector->NumberOfFATs == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: NumberOfFATs == 0!\n");
#endif
        BlFatHalt();
    }

    if (BootSector->SectorsPerFAT == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: SectorsPerFAT == 0!\n");
#endif
        BlFatHalt();
    }

    BlFatNumberOfRootDirectoryEntries = BootSector->NumberOfRootDirectoryEntries;

    if ((BlFatNumberOfRootDirectoryEntries == 0) ||
        ((BlFatNumberOfRootDirectoryEntries % 64) != 0)) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Invalid number of root directory entries (%u)!\n", BlFatNumberOfRootDirectoryEntries);
#endif
        BlFatHalt();
    }

    BlFatTableStart = BootSector->NumberOfReservedSectors;

    if (BlFatTotalSectorCount < BlFatTableStart) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: TotalSectorCount < TableStart!\n");
#endif
        BlFatHalt();
    }

    BlFatRootStart = BlFatTableStart + (BootSector->NumberOfFATs * BootSector->SectorsPerFAT);

    if (BlFatTotalSectorCount < BlFatRootStart) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: TotalSectorCount < RootStart!\n");
#endif
        BlFatHalt();
    }

    BlFatDataStart = BlFatRootStart + (ROUND_UP_TO_POWER2(BlFatNumberOfRootDirectoryEntries * sizeof(FAT_DIRECTORY_ENTRY), FAT_SECTOR_SIZE) / FAT_SECTOR_SIZE);

    if (BlFatTotalSectorCount < BlFatDataStart) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: TotalSectorCount < DataStart!\n");
#endif
        BlFatHalt();
    }

    BlFatNumberOfDataClusters = (BlFatTotalSectorCount - BlFatDataStart) / BlFatSectorsPerCluster;

    if (BlFatNumberOfDataClusters == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: NumberOfDataClusters == 0!\n");
#endif
        BlFatHalt();
    }

    BlFatLinkTerminator = FAT16_LINK_TERMINATOR;
    BlFatGetNextCluster = BlFat16GetNextCluster;

    //
    
    //

    BlFatRootDirectory = (PFAT_DIRECTORY_ENTRY) BlPoolAllocateBlock((BlFatDataStart - BlFatRootStart) * FAT_SECTOR_SIZE);

    if (BlFatReadSector(BlFatRootStart,
                        BlFatDataStart - BlFatRootStart,
                        (PFAT_SECTOR) BlFatRootDirectory) == FALSE) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Error reading root directory!\n");
#endif
        BlFatHalt();
    }

    BLASSERT(FAT_IS_DATA_CLUSTER(FAT16_LINK_TERMINATOR) == FALSE);

    return;
}

BOOLEAN
BlFat32GetNextCluster(
    UINT32 Cluster,
    PUINT32 NextCluster
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
    UINT32 Offset;
    UINT32 Sector;
    FAT_SECTOR TablePage;

    if (FAT_IS_DATA_CLUSTER(Cluster) == FALSE) {

#if FAT_VERBOSE

        BlRtlPrintf("FAT: Fat32GetNextCluster: Cluster %u is out of range!\n", Cluster);

#endif

        return FALSE;
    }

    Sector = BlFatTableStart + (Cluster / 128);
    Offset = Cluster % 128;

    if (BlFatReadSector(Sector, 1, &TablePage) == FALSE) {

        return FALSE;
    }

    *NextCluster = ((PUINT32) &TablePage)[Offset];

    return TRUE;
}

VOID
BlFat32Initialize(
    VOID
    )


//

//

//
//--

{
    PFAT32_BOOT_SECTOR BootSector;
    UINT32 RootDirectoryChainLength;

    BootSector = &BlFatBootSector.u1.Fat32;

    BLASSERT(BlFatMbr.Partition[BlFatPartitionId].Type == MBR_FAT32LBA);

    //
    
    //

    if (BlRtlReadDrive(BlFatDriveId,
                       BlFatPartitionStart,
                       1,
                       BootSector) == FALSE) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Error reading boot sector!\n");
#endif
        BlFatHalt();
    }

    //
    
    //

    if (BootSector->BytesPerSector != FAT_SECTOR_SIZE) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Unsupported sector size (%u)!\n", BootSector->BytesPerSector);
#endif
        BlFatHalt();
    }

    BlFatSectorsPerCluster = BootSector->SectorsPerCluster;

    if (BlFatSectorsPerCluster == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: SectorsPerCluster == 0!\n");
#endif
        BlFatHalt();
    }

    BlFatBytesPerCluster = BlFatSectorsPerCluster * FAT_SECTOR_SIZE;

    if (BootSector->TotalSectorCount32 > 0) {

        BlFatTotalSectorCount = BootSector->TotalSectorCount32;

    } else {

        BlFatTotalSectorCount = BootSector->TotalSectorCount16;
    }

    if (BlFatTotalSectorCount > BlFatPartitionSize) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Boot sector claims more sectors than MBR!\n");
#endif
        BlFatHalt();
    }

    if (BootSector->NumberOfFATs == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: NumberOfFATs == 0!\n");
#endif
        BlFatHalt();
    }

    if (BootSector->SectorsPerFAT32 == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: SectorsPerFAT == 0!\n");
#endif
        BlFatHalt();
    }

    if (BootSector->NumberOfRootDirectoryEntries != 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: BootSector->NumberOfRootDirectoryEntries != 0!\n");
#endif
        BlFatHalt();
    }

    BlFatTableStart = BootSector->NumberOfReservedSectors;

    if (BlFatTotalSectorCount < BlFatTableStart) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: TotalSectorCount < TableStart!\n");
#endif
        BlFatHalt();
    }

    BlFatDataStart = BlFatTableStart + (BootSector->NumberOfFATs * BootSector->SectorsPerFAT32);

    if (BlFatTotalSectorCount < BlFatDataStart) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: TotalSectorCount < DataStart!\n");
#endif
        BlFatHalt();
    }

    BlFatNumberOfDataClusters = (BlFatTotalSectorCount - BlFatDataStart) / BlFatSectorsPerCluster;

    if (BlFatNumberOfDataClusters == 0) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: NumberOfDataClusters == 0!\n");
#endif
        BlFatHalt();
    }

    BlFatLinkTerminator = FAT32_LINK_TERMINATOR;
    BlFatGetNextCluster = BlFat32GetNextCluster;

    //
    
    //

    if (BlFatGetLengthClusterChain(BootSector->RootDirectoryFirstCluster, &RootDirectoryChainLength) == FALSE) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Error querying chain length of root directory!\n");
#endif
        BlFatHalt();
    }

    BlFatRootDirectory = (PFAT_DIRECTORY_ENTRY) BlPoolAllocateBlock(RootDirectoryChainLength * BlFatBytesPerCluster);

    if (BlFatReadClusterChain(BootSector->RootDirectoryFirstCluster,
                              RootDirectoryChainLength * BlFatBytesPerCluster,
                              BlFatRootDirectory) == FALSE) {

#if FAT_VERBOSE
        BlRtlPrintf("FAT: Error reading root directory!\n");
#endif
        BlFatHalt();
    }

    BlFatNumberOfRootDirectoryEntries = (RootDirectoryChainLength * BlFatBytesPerCluster) / sizeof(FAT_DIRECTORY_ENTRY);


    BLASSERT(FAT_IS_DATA_CLUSTER(FAT32_LINK_TERMINATOR) == FALSE);

    return;
}

VOID
BlFatInitialize(
    UINT8 DriveId,
    UINT8 FatType
    )


//

//

//

//

//

//
//--

{
    UINT32 Index;

    BLASSERT((FatType == MBR_FAT16LBA) || (FatType == MBR_FAT32LBA));

    if (BlRtlGetDriveParameters(DriveId, &BlFatDriveParameters) == FALSE) {

        BlRtlPrintf("FAT: Can't get drive info 0x%02x!\n", DriveId);
        BlRtlHalt();
    }

    if (BlFatDriveParameters.BytesPerSector != FAT_SECTOR_SIZE) {

        BlRtlPrintf("FAT: Unexpected bytes per sector (%u)!\n", BlFatDriveParameters.BytesPerSector);
        BlRtlHalt();
    }

    if (BlRtlReadDrive(DriveId, 0, 1, &BlFatMbr) == FALSE) {

        BlRtlPrintf("FAT: Error reading MBR!\n");
        BlRtlHalt();
    }

    if (BlFatMbr.Signature != MBR_SIGNATURE) {

        BlRtlPrintf("FAT: No MBR signature!\n");
    }

    BlFatPartitionId = (UINT32) -1;

    for (Index = 0; Index <= 4; Index += 1) {

        if (FatType == BlFatMbr.Partition[Index].Type) {

            switch (BlFatMbr.Partition[Index].Type) {

                case MBR_FAT16LBA: {

                    BlFatDriveId = DriveId;
                    BlFatPartitionId = Index;
                    BlFatPartitionStart = BlFatMbr.Partition[Index].FirstSector;
                    BlFatPartitionSize = BlFatMbr.Partition[Index].NumberOfSectors;

                    BlFat16Initialize();

                    break;
                }

                case MBR_FAT32LBA: {

                    BlFatDriveId = DriveId;
                    BlFatPartitionId = Index;
                    BlFatPartitionStart = BlFatMbr.Partition[Index].FirstSector;
                    BlFatPartitionSize = BlFatMbr.Partition[Index].NumberOfSectors;

                    BlFat32Initialize();

                    break;
                }
            }
        }
    }

    if (BlFatPartitionId == (UINT32) -1) {

        BlRtlPrintf("FAT: No %s partitions!\n", FatType == MBR_FAT16LBA ? "FAT16" : "FAT32");

        BlRtlHalt();
    }

    BlFsGetFileSize = BlFatGetFileSize;
    BlFsReadFile = BlFatReadFile;

    return;
}
