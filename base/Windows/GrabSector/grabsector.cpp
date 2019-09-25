////////////////////////////////////////////////////////////////////////////
//
// utility to read/write bootsectors
//
// Copyright Microsoft Corporation
//

#define UNICODE
#define _UNICODE
#define _WIN32_WINNT 0x500

#include <winlean.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

// do a raw read from pwzDisk to pbBuffer of dwBytes bytes, starting at dwOffset
int ReadRaw(PCWSTR pwzDisk, PBYTE pbBuffer, DWORD dwOffset, DWORD dwBytes)
{
    DWORD cbRead;
    LARGE_INTEGER liPos;
    HANDLE hDisk = CreateFile(pwzDisk,                  // drive to open
                              GENERIC_READ,             // no access to the drive
                              FILE_SHARE_READ |         // share mode
                              FILE_SHARE_WRITE,
                              NULL,                     // default security attributes
                              OPEN_EXISTING,            // disposition
                              FILE_FLAG_NO_BUFFERING,   // attributes
                              NULL);                    // do not copy file attributes

    if (hDisk == INVALID_HANDLE_VALUE) // cannot open the drive
    {
        printf("CreateFile failed: %d\n", GetLastError());
        return 1;
    }

    liPos.QuadPart = dwOffset;
    SetFilePointerEx(hDisk, liPos, NULL, FILE_BEGIN);

    if (!ReadFile(hDisk, pbBuffer, dwBytes, &cbRead, NULL)) {
        printf("ReadFile failed: %d\n", GetLastError());
        return 1;
    }
    CloseHandle(hDisk);
    return 0;
}

// print a buffer
void DisplayBuffer(PBYTE pbBuffer, DWORD dwOffset, DWORD dwBytes)
{
    static const int MaxLineWidth = 16;

    for (DWORD i = 0; i < dwBytes; i += MaxLineWidth){
        printf("%08x: ", dwOffset + i);

        DWORD dwLineWidth = dwBytes - i;
        if (dwLineWidth > MaxLineWidth) {
            dwLineWidth = MaxLineWidth;
        }

        DWORD j;
        for (j = 0; j < dwLineWidth; j++) {
            printf("%02x ", pbBuffer[dwOffset + i + j]);
        }
        for (; j < MaxLineWidth + 1; j++) {
            printf("   ");
        }
        for (j = 0; j < dwLineWidth; j++) {
            BYTE c = pbBuffer[dwOffset + i + j];
            if (c < 31 || c > 126) {
                c = '.';
            }
            printf("%c", c);
        }
        printf("\n");
    }
}

// Write a file - this forces create, and is thus inappropriate for direct disk access
int WriteRawCreate(PCWSTR pwzFile, PBYTE pbBuffer, DWORD dwOffset, DWORD dwBytes)
{
    DWORD cbRead;

    HANDLE hFile = CreateFile(pwzFile,                  // drive to open
                              GENERIC_WRITE | GENERIC_READ,
                              NULL,
                              NULL,                     // default security attributes
                              CREATE_ALWAYS,            // disposition
                              FILE_FLAG_NO_BUFFERING,   // attributes
                              NULL);                    // do not copy file attributes

    if (hFile == INVALID_HANDLE_VALUE)
    {
        printf("CreateFile failed: %d\n", GetLastError());
        return 1;
    }

    if (!WriteFile(hFile, pbBuffer, dwBytes, &cbRead, NULL)) {
        printf("WriteFile failed: %d\n", GetLastError());
        return 1;
    }
    return 0;
}

// exact same as above, except with OPEN_EXISTING, so that it is appropriate
// for writing a bootsector direct to a disk
int WriteRaw(PCWSTR pwzFile, PBYTE pbBuffer, DWORD dwOffset, DWORD dwBytes)
{
    DWORD cbRead;

    HANDLE hFile = CreateFile(pwzFile,                  // drive to open
                              GENERIC_WRITE | GENERIC_READ,
                              NULL,
                              NULL,                     // default security attributes
                              OPEN_EXISTING,            // disposition
                              FILE_FLAG_NO_BUFFERING,   // attributes
                              NULL);                    // do not copy file attributes

    if (hFile == INVALID_HANDLE_VALUE)
    {
        printf("CreateFile failed: %d\n", GetLastError());
        return 1;
    }

    if (!WriteFile(hFile, pbBuffer, dwBytes, &cbRead, NULL)) {
        printf("WriteFile failed: %d\n", GetLastError());
        return 1;
    }
    return 0;
}

static inline bool IsPowerOfTwo(DWORD dwValue)
{
    return ((dwValue - 1) & dwValue) == 0;
}

static inline WORD GetLE16(PBYTE pbBuffer, DWORD dwOffset)
{
    return (WORD)pbBuffer[dwOffset] + (((WORD)pbBuffer[dwOffset + 1]) << 8);
}

static inline DWORD GetLE32(PBYTE pbBuffer, DWORD dwOffset)
{
    return ((DWORD)pbBuffer[dwOffset] +
            (((DWORD)pbBuffer[dwOffset + 1]) << 8) +
            (((DWORD)pbBuffer[dwOffset + 2]) << 16) +
            (((DWORD)pbBuffer[dwOffset + 3]) << 24));
}

static int GetFatVersion(PBYTE pbBuffer, DWORD dwBytes)
{
    if (!IsPowerOfTwo(dwBytes) || dwBytes < 512 ||
        GetLE16(pbBuffer, 510) != 0xaa55) {
        return 0;
    }

    // These strings mean *nothing* with regard to actual FAT
    // type - they are just valid signatures.
    if (strncmp((const char*)(pbBuffer + 52), "FAT      ", 8) &&
        strncmp((const char*)(pbBuffer + 52), "FAT12    ", 8) &&
        strncmp((const char*)(pbBuffer + 52), "FAT16    ", 8) &&
        strncmp((const char*)(pbBuffer + 82), "FAT32    ", 8)) {
        return 0;
    }

    // Calculate number of clusters to determine FAT type per
    // page 14 of FAT spec.
    DWORD dwBytesPerSector      = GetLE16(pbBuffer, 11);
    DWORD dwSectorsPerCluster   = (DWORD)pbBuffer[13];
    DWORD dwReservedSectorCount = GetLE16(pbBuffer, 14);
    DWORD dwNumberOfFats        = (DWORD)pbBuffer[16];
    DWORD dwRootEntryCount      = GetLE16(pbBuffer, 17);

    DWORD dwRootDirSectors =
        ((dwRootEntryCount * 32) + (dwBytesPerSector - 1)) / dwBytesPerSector;

    DWORD dwFatSize      = 0;
    DWORD dwTotalSectors = 0;

    DWORD dwFatSize16 = GetLE16(pbBuffer, 22);
    if (dwFatSize16 == 0) {
        dwFatSize = GetLE32(pbBuffer, 36);
    }
    else {
        dwFatSize = dwFatSize16;
    }

    DWORD dwTotalSectors16 = GetLE16(pbBuffer, 19);
    if (dwTotalSectors16 == 0) {
        dwTotalSectors = GetLE32(pbBuffer, 32);
    }
    else {
        dwTotalSectors = dwTotalSectors16;
    }

    DWORD dwDataSectors = (dwTotalSectors -
                           (dwReservedSectorCount +
                            dwNumberOfFats * dwFatSize +
                            dwRootDirSectors)
                          );

    DWORD dwCountOfClusters = dwDataSectors / dwSectorsPerCluster;

    if (dwCountOfClusters < 4085) {
        return 12;
    }
    else if (dwCountOfClusters < 65525) {
        return 16;
    }
    else {
        return 32;
    }
}

// this copies the BPB from the oldbuffer to the newbuffer
// so we don't trash the BPB when we write the new buffer
BOOL MergeSectors(PBYTE pbOldBuffer,
                  PBYTE pbBuffer,
                  DWORD dwBytes,
                  BOOL fCheckFatSanity)
{
    if (fCheckFatSanity) {
        DWORD dwOldFat = GetFatVersion(pbOldBuffer, dwBytes);
        DWORD dwNewFat = GetFatVersion(pbBuffer, dwBytes);
        if (dwOldFat != dwNewFat) {
            fprintf(stderr,
                    "New boot sectors FAT version FAT differs (%d != %d).\n",
                    dwNewFat, dwOldFat);
            // We'll call it a pint then, shall we :-)
            return FALSE;
        }
    }

    // copy the BPB and BS from the old sector into the new
    int preservebytes = pbBuffer[1] + 2;

    for (int i = 3; i < preservebytes; i++) {
        pbBuffer[i] = pbOldBuffer[i];
    }
    return TRUE;
}

int __cdecl wmain(int argc, WCHAR **argv)
{
    BOOL  fNeedHelp       = FALSE;
    BOOL  fRead           = FALSE;
    BOOL  fWrite          = FALSE;
    BOOL  fDisplay        = FALSE;
    BOOL  fNtldr          = FALSE;
    BOOL  fCheckFat       = FALSE;
    PBYTE pbBuffer;
    PBYTE pbOldBuffer;
    WCHAR wzPartition[64] = L"";
    WCHAR wzFile[64] = L"";
    WCHAR wzFile2[64] = L"";

    if (argc==1){
        fNeedHelp = TRUE;
    }
    else{
        // first check the first param
        if (argv[1][0] == '-' || argv[1][0] == '/'){
            switch(argv[1][1]){
                case 'd':
                case 'D':
                    fDisplay = TRUE;
                    break;
                case 'n':
                case 'N':
                    fNtldr = TRUE;
                    break;
                case 'r':
                case 'R':
                    fRead = TRUE;
                    break;
                case 'w':
                case 'W':
                    fWrite    = TRUE;
                    fCheckFat = TRUE;
                    break;
                case 'x':
                case 'X':
                    fWrite    = TRUE;
                    fCheckFat = FALSE;
                    break;
                default:
                    fNeedHelp = TRUE;
                    break;
            }
        }
        else{
            fNeedHelp = TRUE;
        }
    }

    // verify parameter counts
    if ((fDisplay && argc !=3) || (fRead && argc !=4) || (fWrite && argc !=4) || (fNtldr && argc !=5)){
        fNeedHelp = TRUE;
    }

    if (fNeedHelp) {
        printf(
               "Usage:\n"
               "    grabsector [options] {drive letter:} {file1} {file2}\n"
               "Options:\n"
               "    /d     --  Display bootsector from drive.\n"
               "    /n     --  Create NTLDR-compatible bootsector file2 from drive and file1.\n"
               "    /r     --  Read drive's bootsector, write to file1.\n"
               "    /w     --  Write drive's bootsector from file1 to drive.\n"
               "    /x     --  Write drive's bootsector from file1 to drive (no sanity check).\n"
               "    /?     --  Display this help screen.\n"
               "Advanced:\n"
               "    To access the MBR directly, use PHYSICALDRIVE0 as the drive name.\n"
               "Examples:\n"
               "    grabsector /d c:\n"
               "    grabsector /r c: bootsec.old \n"
               "    grabsector /w c: bootsec.new \n"
               "    grabsector /n c: bootsec.new bootsec.NT \n"
               "    grabsector /d PHYSICALDRIVE0 \n"
              );
        return 1;
    }
    else{
        pbBuffer = (PBYTE)VirtualAlloc(NULL, 512, MEM_COMMIT, PAGE_READWRITE);
        if (pbBuffer == NULL) {
            printf("VirtualAlloc failed: %d\n", GetLastError());
            return 1;
        }

        wsprintf(wzPartition, L"\\\\.\\%ls", argv[2]);
        if (fRead || fWrite || fNtldr)
            wsprintf(wzFile, L"%ls", argv[3]);
    }

    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_HIGHEST);
    printf("Disk: %ls\n", wzPartition);
    printf("File: %ls\n", wzFile);
    if (fDisplay) {
        if(ReadRaw(wzPartition, pbBuffer, 0, 512)==0) {
            DisplayBuffer(pbBuffer, 0, 512);
        }
    }
    if (fRead){
        if (ReadRaw(wzPartition, pbBuffer, 0, 512)==0)
            WriteRawCreate(wzFile, pbBuffer, 0, 512);
    }
    if (fWrite){
        // set up a buffer for the old bootsector
        pbOldBuffer = (PBYTE)VirtualAlloc(NULL, 512, MEM_COMMIT, PAGE_READWRITE);
        if (pbOldBuffer == NULL) {
            printf("VirtualAlloc failed: %d\n", GetLastError());
            return 1;
        }
        // get the old bootsector
        if(ReadRaw(wzPartition, pbOldBuffer, 0, 512)!=0)
            return -1;
        // open the file
        if (ReadRaw(wzFile, pbBuffer, 0, 512)!=0)
            return -1;
        // merge the file with the bootsector
        if (MergeSectors(pbOldBuffer, pbBuffer, 512, fCheckFat)) {
            WriteRaw(wzPartition, pbBuffer, 0, 512);
        }
    }
    if (fNtldr){
        // get the second filename
        wsprintf(wzFile2, L"%ls", argv[4]);
        // set up a buffer for the old bootsector
        pbOldBuffer = (PBYTE)VirtualAlloc(NULL, 512, MEM_COMMIT, PAGE_READWRITE);
        if (pbOldBuffer == NULL) {
            printf("VirtualAlloc failed: %d\n", GetLastError());
            return 1;
        }
        // get the old bootsector
        if(ReadRaw(wzPartition, pbOldBuffer, 0, 512)!=0)
            return -1;
        // open the input file
        if (ReadRaw(wzFile, pbBuffer, 0, 512)!=0)
            return -1;
        // merge the file with the bootsector
        if (MergeSectors(pbOldBuffer, pbBuffer, 512, fCheckFat)) {
            WriteRawCreate(wzFile2, pbBuffer, 0, 512);
        }
    }
    return 0;
}
