//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:       mkbin.cpp
//
//  Contents:   Strips PE header from a single sectioned PE binary.
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

BOOL DoCopy(HANDLE hInput, HANDLE hOutput)
{
    const DWORD nBufferBytes = 0x10000;
    BYTE  bBuffer[nBufferBytes];

    DWORD nRead = 0;
    do {
        if (0 == ReadFile(hInput, bBuffer, nBufferBytes, &nRead, NULL)) {
            fprintf(stderr, "ReadFile failed.");
            return FALSE;
        }

        DWORD nWritten = 0;
        if (0 == WriteFile(hOutput, bBuffer, nRead, &nWritten, NULL)) {
            fprintf(stderr, "WriteFile failed.");
            return FALSE;
        }
        assert(nWritten == nRead);
    } while (nRead == nBufferBytes);

    return true;
}

BOOL StripPE(PCWSTR pwzImage, PCWSTR pwzOutImage)
{
    HANDLE hInput = CreateFile(pwzImage,
                               GENERIC_READ,
                               0,
                               NULL,
                               OPEN_EXISTING,
                               0,
                               NULL);
    if (hInput == INVALID_HANDLE_VALUE) {
        fprintf(stderr, "Could not open image file: %ls\n", pwzImage);
        return FALSE;
    }

    ULONG cbInFileData = GetFileSize(hInput, NULL);
    if (cbInFileData == 0xffffffff) {
        CloseHandle(hInput);
        return FALSE;
    }

    DWORD dwRead = 0;

    // Read the DOS header.
    //
    IMAGE_DOS_HEADER     idh;
    IMAGE_NT_HEADERS     inh;
    IMAGE_SECTION_HEADER ish;

    if (!ReadFile(hInput, &idh, sizeof(idh), &dwRead, NULL) || dwRead != sizeof(idh)) {
      failed:
        fprintf(stderr, "Invalid image: %ls\n", pwzImage);
        CloseHandle(hInput);
        return FALSE;
    }

    if (idh.e_magic != IMAGE_DOS_SIGNATURE) {
        goto failed;
    }

    // Read in the PE image header
    //
    if (SetFilePointer(hInput, idh.e_lfanew, NULL, FILE_BEGIN) != idh.e_lfanew) {
        goto failed;
    }
    else if (ReadFile(hInput, &inh, sizeof(inh), &dwRead, NULL) == INVALID_SET_FILE_POINTER) {
        goto failed;
    }
    else if (inh.Signature != IMAGE_NT_SIGNATURE) {
        goto failed;
    }
    else if (inh.FileHeader.Machine != IMAGE_FILE_MACHINE_THUMB) {
        fprintf(stderr, "mkbin: machine: %04x!\n");
        goto failed;
    }
    else if (!ReadFile(hInput, &ish, sizeof(ish), &dwRead, NULL) || dwRead != sizeof(ish)) {
        goto failed;
    }
    else if (SetFilePointer(hInput, ish.PointerToRawData, NULL, FILE_BEGIN) == INVALID_SET_FILE_POINTER) {
        goto failed;
    }

    // Open output file
    HANDLE hOutput = CreateFile(pwzOutImage,
                                GENERIC_WRITE,
                                0,
                                NULL,
                                CREATE_ALWAYS,
                                0,
                                NULL);
    if (hOutput == INVALID_HANDLE_VALUE) {
        fprintf(stderr, "Could not open output file: %ls\n", pwzOutImage);
        return FALSE;
    }

    BOOL bSuccess = TRUE;
    bSuccess = DoCopy(hInput, hOutput);

    CloseHandle(hInput);
    CloseHandle(hOutput);
    return bSuccess;
}

int __cdecl wmain(int argc, WCHAR **argv)
{
    BOOL fNeedHelp = FALSE;

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
            case '?':                                 // Help
                fNeedHelp = TRUE;
                break;

            default:
                printf("Unknown argument: %ls\n", argv[arg]);
                fNeedHelp = TRUE;
                break;
        }
    }

    if (fNeedHelp || argc - arg != 2) {
        printf(
               "Usage:\n"
               "    mkbin [options] <input> <output>\n"
               "Options:\n"
               "    /?                -- Display this help screen.\n"
               "Summary:\n"
               "    Strip PE header from single sectioned PE binary for an XScale flash image.\n"
              );
        return 1;
    }

    return StripPE(argv[arg], argv[arg + 1]) ? 0 : 1;
}

//
///////////////////////////////////////////////////////////////// End of File.
