//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:       smashbin.cpp
//
//  Contents:   Smashes two binary files together, with a given offset
//              Between them padded
//

#define UNICODE
#define _UNICODE

#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <winlean.h>
#include <assert.h>

//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//
typedef signed int INT;
typedef signed char INT8, *LPINT8;
typedef signed short INT16, *LPINT16;
typedef unsigned int UINT;
typedef unsigned char UINT8, *LPUINT8;
typedef unsigned short UINT16, *LPUINT16;


BOOL DoPad(HANDLE hOutput, DWORD padSize)
{
    const DWORD nBufferBytes = 0x10000;
    BYTE bPadBuffer[nBufferBytes];
    DWORD nWritten = 0;

    memset(&bPadBuffer, 0, nBufferBytes);

    while (padSize > nBufferBytes) {
        if (0 == WriteFile(hOutput, bPadBuffer, nBufferBytes, &nWritten, NULL)) {
            fprintf(stderr, "Pad file failed.\n");
            return FALSE;
        }
        assert(nWritten == nBufferBytes);
        padSize -= nBufferBytes;
    }

    if (padSize > 0) {
        if (0 == WriteFile(hOutput, bPadBuffer, padSize, &nWritten, NULL)) {
            fprintf(stderr, "Pad file failed.\n");
            return FALSE;
        }
        assert(nWritten == padSize);
    }
    return TRUE;
}


BOOL DoCopy(HANDLE hInput, HANDLE hOutput, DWORD * totalWritten)
{
    const DWORD nBufferBytes = 0x10000;
    BYTE  bBuffer[nBufferBytes];

    DWORD nRead = 0;
    do {
        if (0 == ReadFile(hInput, bBuffer, nBufferBytes, &nRead, NULL)) {
            fprintf(stderr, "ReadFile failed.\n");
            return FALSE;
        }

        DWORD nWritten = 0;
        if (0 == WriteFile(hOutput, bBuffer, nRead, &nWritten, NULL)) {
            fprintf(stderr, "WriteFile failed.\n");
            return FALSE;
        }
        assert(nWritten == nRead);
        (*totalWritten) += nWritten;
    } while (nRead != 0);

    return true;
}


BOOL SmashBins(DWORD offset, PCWSTR bin1, PCWSTR bin2, PCWSTR dest)
{
    BOOL bSuccess = TRUE;
    DWORD totalWritten = 0;

    // open output file
    HANDLE hOutput = CreateFile(dest,
                                GENERIC_WRITE,
                                0,
                                NULL,
                                CREATE_ALWAYS,
                                0,
                                NULL);

    if (hOutput == INVALID_HANDLE_VALUE) {
        fprintf(stderr, "Could not open output file: %ls\n", dest);
        return false;
    }

    // open input 1
    HANDLE hInput1 = CreateFile(bin1,
                                GENERIC_READ,
                                0,
                                NULL,
                                OPEN_EXISTING,
                                0,
                                NULL);
    if (hInput1 == INVALID_HANDLE_VALUE) {
        fprintf(stderr, "Could not open image file: %ls\n", bin1);
        return FALSE;
    }

    bSuccess = DoCopy(hInput1, hOutput, &totalWritten);

    CloseHandle(hInput1);
    if (!bSuccess) {
        CloseHandle(hOutput);
        return bSuccess;
    } else if (totalWritten > offset) {
        CloseHandle(hOutput);
        fprintf(stderr, "First image is larger than offset %d > %d\n",
                totalWritten, offset);
        return FALSE;
    }

    wprintf(L"00000000..%08x: File %s\n", totalWritten, bin1);

    bSuccess = DoPad(hOutput, offset - totalWritten);

    if (!bSuccess) {
        CloseHandle(hOutput);
        return bSuccess;
    }

    wprintf(L"%08x..%08x: Padding\n", totalWritten, offset);
    totalWritten += (offset - totalWritten);

    // open input 2
    HANDLE hInput2 = CreateFile(bin2,
                                GENERIC_READ,
                                0,
                                NULL,
                                OPEN_EXISTING,
                                0,
                                NULL);
    if (hInput1 == INVALID_HANDLE_VALUE) {
        fprintf(stderr, "Could not open image file: %ls\n", bin2);
        return FALSE;
    }

    bSuccess = DoCopy(hInput2, hOutput, &totalWritten);

    wprintf(L"%08x..%08x: File %s\n", offset, totalWritten, bin2);

    CloseHandle(hInput2);
    CloseHandle(hOutput);

    return bSuccess;
}


int __cdecl wmain(int argc, WCHAR **argv)
{
    BOOL fNeedHelp = FALSE;
    DWORD offset = 0;

    int arg;
    for (arg = 1; arg < argc && !fNeedHelp; arg++) {
        if (argv[arg][0] != '-' && argv[arg][0] != '/') {
            break;

        }

        WCHAR *argn = argv[arg]+1;                   // Argument name
        WCHAR *argp = argn;                          // Argument parameter

        while (*argp && *argp != ':') {
            argp++;
        }

        if (*argp == ':') {
            *argp++ = '\0';
        }

        switch (argn[0]) {

             case 'o':                                     // Offset
                int scanfRet;
                arg++;
                if(argv[arg][0] == '0' && argv[arg][1] == 'x')
                {
                    // hex number
                    scanfRet = swscanf(argv[arg], L"%x", &offset);
                } else {
                    // base 10 number
                    scanfRet = swscanf(argv[arg], L"%d", &offset);
                }
                if(EOF == scanfRet)
                {
                    fNeedHelp = TRUE;
                }
                break;
            case '?':                                   // Help
                fNeedHelp = TRUE;
                break;

            default:
                printf("Unknown argument: %ls\n", argv[arg]);
                fNeedHelp = TRUE;
                break;
        }
    }

    if (fNeedHelp || argc - arg != 3) {
        printf(
               "Usage:\n"
               "    mkbin [options] <binary 1> <binary 2> <output>\n"
               "Options:\n"
               "    /o <size>         -- Offset of second binary file\n"
               "    /?                -- Display this help screen.\n"
               "Summary:\n"
               "    Smashes two binaries together, with padding between binaries to provide given offset.\n"
              );
        return 1;
    }

    return SmashBins(offset, argv[arg], argv[arg + 1], argv[arg + 2]) ? 0 : 1;
}

//
///////////////////////////////////////////////////////////////// End of File.

