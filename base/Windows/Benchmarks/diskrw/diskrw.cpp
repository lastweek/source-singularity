////////////////////////////////////////////////////////////////////////////
//
// Boot Service
//
// Copyright Microsoft Corporation
//
#define UNICODE
#define _UNICODE
#define _WIN32_WINNT 0x500

#include <winlean.h>
#include <winioctl.h>
#include "wincrypt.h"
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>

#include "srandom.hpp"

#define ARRAYOF(x)      (sizeof(x)/sizeof(x[0]))
#define ASSERT(a)       assert(a)

//////////////////////////////////////////////////////////////////////////////
//

static SRandom g_Rng;
static DWORD64 g_MaxBlock;
static DWORD   g_BlockBytes;

static void ResetOffsetRNG(DWORD64 diskBytes, DWORD blockBytes)
{
    g_Rng.reset();
    assert(blockBytes != 0);
    g_MaxBlock   = diskBytes / blockBytes;
    g_BlockBytes = blockBytes;
}

static DWORD64 GetRandomOffset()
{
    static_assert(SRandom::Maximum == 0x7fffffff);
    DWORD64 offset = 0;
    for (int i = 0; i < 64; i += 30) {
        offset ^= (DWORD64)(g_Rng.next() << i);
    }
    offset &= 0x7fffffffffffffffi64;
    offset %= g_MaxBlock;
    assert (offset >= 0 && offset < g_MaxBlock);
    return offset * g_BlockBytes;
}

//////////////////////////////////////////////////////////////////////////////
//

DWORD64 GetDiskSize(HANDLE hDisk)
{
    DWORD junk;                   // discard results
    DISK_GEOMETRY dg;

    ZeroMemory(&dg, sizeof(dg));

    if (!DeviceIoControl(hDisk,  // device to be queried
                         IOCTL_DISK_GET_DRIVE_GEOMETRY,  // operation to perform
                         NULL, 0, // no input buffer
                         &dg, sizeof(dg),     // output buffer
                         &junk,                 // # bytes returned
                         NULL)) {
        printf("DeviceIoControl failed: %d\n", GetLastError());
        return 0;
    }

    return dg.Cylinders.QuadPart * (ULONG)dg.TracksPerCylinder *
        (ULONG)dg.SectorsPerTrack * (ULONG)dg.BytesPerSector;
}

DWORD64 GetPartitionSize(HANDLE hDisk)
{
    DWORD junk;                   // discard results
    PARTITION_INFORMATION_EX pi;

    ZeroMemory(&pi, sizeof(pi));

    if (!DeviceIoControl(hDisk,  // device to be queried
                         IOCTL_DISK_GET_PARTITION_INFO_EX,  // operation to perform
                         NULL, 0, // no input buffer
                         &pi, sizeof(pi),     // output buffer
                         &junk,                 // # bytes returned
                         NULL)) {
        printf("DeviceIoControl failed: %d\n", GetLastError());
        return 0;
    }

    return pi.PartitionLength.QuadPart;
}

int DiskReadTest(PCWSTR pwzDisk,
                 DWORD  dwBlockSize,
                 DWORD  dwBlockCount,
                 DWORD  dwLimit,
                 BOOL   fRandom,
                 BOOL   fWriteThrough)
{
    PBYTE pbBuffer = (PBYTE)VirtualAlloc(NULL, 0x100000, MEM_COMMIT, PAGE_READWRITE);
    if (pbBuffer == NULL) {
        printf("VirtualAlloc failed: %d\n", GetLastError());
        return 1;
    }

    DWORD dwAttributes = FILE_FLAG_NO_BUFFERING;
    if (fWriteThrough)
    {
        dwAttributes |= FILE_FLAG_WRITE_THROUGH;
    }

    HANDLE hDisk = CreateFile(pwzDisk,  // drive to open
                              GENERIC_READ,      // no access to the drive
                              FILE_SHARE_READ | // share mode
                              FILE_SHARE_WRITE,
                              NULL,             // default security attributes
                              OPEN_EXISTING,    // disposition
                              dwAttributes,
                              NULL);            // do not copy file attributes

    if (hDisk == INVALID_HANDLE_VALUE) // cannot open the drive
    {
        printf("CreateFile failed: %d\n", GetLastError());
        return 1;
    }

    DWORD64 dwDisk = GetPartitionSize(hDisk);
    // DWORD64 dwDisk = GetDiskSize(hDisk);
    if (dwLimit != 0) {
        dwDisk = dwLimit * 1024i64 * 1024i64;
    }
    DWORD64 dwTotal = dwBlockCount * dwBlockSize;

    printf("# Type:    %s Read\n", fRandom ? "Random" : "Sequential");
    printf("# Disk:    %10I64d MB\n", dwDisk / (1024 * 1024));
    printf("# Limit:   %10d MB\n", dwLimit);
    printf("# Work:    %10.2f MB\n", (float)dwTotal / (1024 * 1024));
    printf("# Ops:     %10d\n", dwTotal / dwBlockSize);

    DWORD dwOps = 0;
    LARGE_INTEGER before;
    QueryPerformanceCounter(&before);

    LARGE_INTEGER liPos;

    if (fRandom) {
        ResetOffsetRNG(dwDisk, dwBlockSize);
        liPos.QuadPart = GetRandomOffset();
        while (dwOps++ < dwBlockCount) {
            if (SetFilePointerEx(hDisk, liPos, NULL, FILE_BEGIN) == FALSE) {
                printf("SetFilePointerEx failed: %d\n", GetLastError());
                return 1;
            }
            liPos.QuadPart = GetRandomOffset();

            DWORD cbRead = 0;
            if (!ReadFile(hDisk, pbBuffer, dwBlockSize, &cbRead, NULL)) {
                printf("ReadFile failed: %d\n", GetLastError());
                return 1;
            }
        }
    }
    else {
        liPos.QuadPart = 0;
        while (dwOps++ < dwBlockCount) {
            if (SetFilePointerEx(hDisk, liPos, NULL, FILE_BEGIN) == FALSE) {
                printf("SetFilePointerEx failed: %d\n", GetLastError());
                return 1;
            }
            liPos.QuadPart += dwBlockSize;

            DWORD cbRead;
            if (!ReadFile(hDisk, pbBuffer, dwBlockSize, &cbRead, NULL)) {
                printf("ReadFile failed: %d\n", GetLastError());
                return 1;
            }
        }
    }

    LARGE_INTEGER after;
    QueryPerformanceCounter(&after);
    LARGE_INTEGER frequency;
    QueryPerformanceFrequency(&frequency);

    CloseHandle(hDisk);

    after.QuadPart -= before.QuadPart;
    //printf("Delta : %18I64d\n", after.QuadPart);
    //printf("Freque: %18I64d\n", frequency.QuadPart);

    double elapsed = (double)after.QuadPart / (double)frequency.QuadPart;
    printf("%cR.%d ", fRandom ? 'R' : 'S', dwBlockSize);
    printf("Mbps %10.3f Ops/Sec: %10.3f Elapsed %10.3f Check 0x%I64x\n",
           ((double)dwTotal) / (1024 * 1024 * elapsed),
           (double)dwOps / elapsed,
           elapsed, liPos.QuadPart);

    return 0;
}

int DiskWriteTest(PCWSTR pwzDisk,
                  DWORD  dwBlockSize,
                  DWORD  dwBlockCount,
                  DWORD  dwLimit,
                  BOOL   fRandom,
                  BOOL   fWriteThrough)
{
    PBYTE pbBuffer = (PBYTE)VirtualAlloc(NULL, 0x100000, MEM_COMMIT, PAGE_READWRITE);
    if (pbBuffer == NULL) {
        printf("VirtualAlloc failed: %d\n", GetLastError());
        return 1;
    }

    DWORD dwAttributes = FILE_FLAG_NO_BUFFERING;
    if (fWriteThrough)
    {
        dwAttributes |= FILE_FLAG_WRITE_THROUGH;
    }

    HANDLE hDisk = CreateFile(pwzDisk,  // drive to open
                              GENERIC_WRITE | GENERIC_READ,
                              0,
                              NULL,             // default security attributes
                              OPEN_EXISTING,    // disposition
                              dwAttributes,
                              NULL);            // do not copy file attributes

    if (hDisk == INVALID_HANDLE_VALUE) // cannot open the drive
    {
        printf("CreateFile failed: %d\n", GetLastError());
        return 1;
    }

    DWORD64 dwDisk = GetPartitionSize(hDisk);
    if (dwLimit != 0) {
        dwDisk = dwLimit * 1024i64 * 1024i64;
    }
    DWORD64 dwTotal = dwBlockCount * dwBlockSize;

    printf("# Type:    %s Write\n", fRandom ? "Random" : "Sequential");
    printf("# Disk:    %10I64d MB\n", dwDisk / (1024 * 1024));
    printf("# Work:    %10.2f MB\n", (float)dwTotal / (1024 * 1024));
    printf("# Ops:     %10d\n", dwTotal / dwBlockSize);

    DWORD dwOps = 0;
    LARGE_INTEGER before;
    QueryPerformanceCounter(&before);

    LARGE_INTEGER liPos;

    if (fRandom) {
        ResetOffsetRNG(dwDisk, dwBlockSize);
        liPos.QuadPart = GetRandomOffset();
        while (dwOps++ < dwBlockCount) {
            if (SetFilePointerEx(hDisk, liPos, NULL, FILE_BEGIN) == FALSE) {
                printf("SetFilePointerEx failed: %d\n", GetLastError());
                return 1;
            }
            liPos.QuadPart = GetRandomOffset();

            DWORD cbRead = 0;
            if (!WriteFile(hDisk, pbBuffer, dwBlockSize, &cbRead, NULL)) {
                printf("WriteFile failed: %d\n", GetLastError());
                return 1;
            }
        }
    }
    else {
        liPos.QuadPart = 0;
        while (dwOps++ < dwBlockCount) {
            if (SetFilePointerEx(hDisk, liPos, NULL, FILE_BEGIN) == FALSE) {
                printf("SetFilePointerEx failed: %d\n", GetLastError());
                return 1;
            }
            liPos.QuadPart += dwBlockSize;

            DWORD cbRead;
            if (!WriteFile(hDisk, pbBuffer, dwBlockSize, &cbRead, NULL)) {
                printf("WriteFile failed: %d\n", GetLastError());
                return 1;
            }
        }
    }

    LARGE_INTEGER after;
    QueryPerformanceCounter(&after);
    LARGE_INTEGER frequency;
    QueryPerformanceFrequency(&frequency);

    CloseHandle(hDisk);

    after.QuadPart -= before.QuadPart;
    //printf("Delta : %18I64d\n", after.QuadPart);
    //printf("Freque: %18I64d\n", frequency.QuadPart);

    double elapsed = (double)after.QuadPart / (double)frequency.QuadPart;
    printf("%cW.%d ", fRandom ? 'R' : 'S', dwBlockSize);
    printf("Mbps: %10.3f Ops/Sec: %10.3f Elapsed: %10.3f Check: 0x%I64x\n",
           ((double)dwTotal) / (1024 * 1024 * elapsed),
           (double)dwOps / elapsed, elapsed, liPos.QuadPart);

    return 0;
}

//////////////////////////////////////////////////////////////////////////////
//

int __cdecl wmain(int argc, WCHAR **argv)
{
    BOOL  fNeedHelp       = FALSE;
    BOOL  fRead           = FALSE;
    BOOL  fWrite          = FALSE;
    DWORD dwBlock         = 512;
    DWORD dwMegabytes     = 0;
    DWORD dwBlockCount    = 0;
    BOOL  fRandom         = FALSE;
    BOOL  fWriteThrough   = TRUE;
    DWORD dwLimit         = 0;
    WCHAR wzPartition[64] = L"";

    for (int arg = 1; arg < argc && !fNeedHelp; arg++) {
        if (argv[arg][0] == '-' || argv[arg][0] == '/') {
            WCHAR *argn = argv[arg]+1;                   // Argument name
            WCHAR *argp = argn;                          // Argument parameter

            while (*argp && *argp != ':') {
                argp++;
            }
            if (*argp == ':')
                *argp++ = '\0';

            switch (argn[0]) {

              case '?':                                 // Help
                fNeedHelp = TRUE;
                break;

              case 'b':                                 // Block size
              case 'B':
                dwBlock = (DWORD)_wtoi(argp);
                break;

              case 'l':                                 // Disk Limit Megabytes
              case 'L':
                dwLimit = (DWORD)_wtoi(argp);
                break;

              case 'm':                                 // Megabytes of Data
              case 'M':
                dwMegabytes = (DWORD)_wtoi(argp);
                break;

              case 'n':                                 // Number of blocks
              case 'N':
                dwBlockCount = (DWORD)_wtoi(argp);
                break;

              case 'r':                                 // Read
              case 'R':
                fRead = TRUE;
                break;

              case 'w':                                 // Write
              case 'W':
                fWrite = TRUE;
                break;

              case 'x':                                 // Xtremely Random
              case 'X':
                fRandom = TRUE;
                break;

              case 'z':
              case 'Z':
                fWriteThrough = FALSE;
                break;

              default:
                printf("Unknown argument: %ls\n", argv[arg]);
                fNeedHelp = TRUE;
                break;
            }
        }
        else {
            wsprintf(wzPartition, L"\\\\.\\%ls", argv[arg]);
        }
    }

    if (dwBlock < 512 || dwBlock & (dwBlock - 1)) {
        fprintf(stderr, "Block size needs to be a power of 2 greater than or equal to 512.\n");
        fNeedHelp = true;
    }

    if ((dwBlockCount == 0 && dwMegabytes == 0) ||
        (dwBlockCount != 0 && dwMegabytes != 0)) {
        fprintf(stderr, "Need to specify either number of blocks or number of megabytes for I/O.\n");
        fNeedHelp = true;
    }

    if (dwMegabytes > 0) {
        DWORD64 tmp = (dwMegabytes * 1048576i64) / dwBlock;
        dwBlockCount = (DWORD) tmp;
    }

    if (argc == 1) {
        fNeedHelp = TRUE;
    }

    if (fNeedHelp) {
        printf(
               "Usage:\n"
               "    diskrw [options] {drive letter:}\n"
               "Options:\n"
               "    /b:N       -- Block size (in bytes).\n"
               "    /l:M       -- Limit (defaults to full partition) in megabytes.\n"
               "    /m:M       -- Megabytes to read or write.\n"
               "    /n:N       -- Number of blocks to read or write.\n"

               "    /x         -- Random, otherwise, defaults to sequential.\n"
               "    /z         -- No write through, defaults to write through.\n"
               "    /r         -- Read.\n"
               "    /w         -- Write.\n"
               "    /?         -- Display this help screen.\n"
               "Example:\n"
               "    diskrw /r /x /b:512 c:\n"
              );
        return 1;
    }

    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_HIGHEST);
    printf("# Disk: %ls\n", wzPartition);
    if (fRead) {
        DiskReadTest(wzPartition, dwBlock, dwBlockCount, dwLimit, fRandom, fWriteThrough);
    }
    else if (fWrite){
        DiskWriteTest(wzPartition, dwBlock, dwBlockCount, dwLimit, fRandom, fWriteThrough);
    }
    return 0;
}
//
///////////////////////////////////////////////////////////////// End of File.
