//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:       mkcore.cpp
//
//  Contents:   Creates a core file from one or more PE image by physically
//              aligning and allocating all of the sections.
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

UINT32 to_arm(UINT32 value)
{
    return (((value & 0xff000000) >> 24) |
            ((value & 0x00ff0000) >>  8) |
            ((value & 0x0000ff00) <<  8) |
            ((value & 0x000000ff) << 24));
}

BOOL MakeRaw(PCWSTR pwzImage)
{
    HANDLE hFile = CreateFile(pwzImage,
                              GENERIC_READ | GENERIC_WRITE,
                              0,
                              NULL,
                              OPEN_EXISTING,
                              0,
                              NULL);
    if (hFile == INVALID_HANDLE_VALUE) {
        fprintf(stderr, "Could not open image file: %ls\n", pwzImage);
        return FALSE;
    }

    ULONG cbInFileData = GetFileSize(hFile, NULL);
    if (cbInFileData == 0xffffffff) {
        CloseHandle(hFile);
        return FALSE;
    }

    DWORD dwRead = 0;

    // Read the DOS header.
    //
    IMAGE_DOS_HEADER idh;
    IMAGE_NT_HEADERS inh;

    if (!ReadFile(hFile, &idh, sizeof(idh), &dwRead, NULL) || dwRead != sizeof(idh)) {
      failed:
        fprintf(stderr, "Invalid image: %ls\n", pwzImage);
        CloseHandle(hFile);
        return FALSE;
    }

    if (idh.e_magic != IMAGE_DOS_SIGNATURE) {
        goto failed;
    }

    // Read in the PE image header
    //
    if (SetFilePointer(hFile, idh.e_lfanew, NULL, FILE_BEGIN) != idh.e_lfanew) {
        goto failed;
    }
    if (!ReadFile(hFile, &inh, sizeof(inh), &dwRead, NULL) || dwRead != sizeof(inh)) {
        goto failed;
    }
    if (inh.Signature != IMAGE_NT_SIGNATURE) {
        goto failed;
    }
    if (inh.FileHeader.Machine != IMAGE_FILE_MACHINE_ARM &&
        inh.FileHeader.Machine != IMAGE_FILE_MACHINE_THUMB) {
        fprintf(stderr, "mkarmraw: machine: %04x!\n");
    }

    if (SetFilePointer(hFile, 0, NULL, FILE_BEGIN) != 0) {
        goto failed;
    }

    // To make a raw binary (i.e. one that starts with valid ARM instructions),
    // we need to insert a branch to the PE entry point.  However, we want
    // the file to still look like a valid PE binary, so it needs to start with
    // the ascii value "MZ".  So, we place an innocent orr instruction, which
    // coincidentally has "MZ" as its first two bytes, at the start of the file
    // followed by a branch to the entry point.
    //
    UINT32 offset = inh.OptionalHeader.AddressOfEntryPoint - 12;
    UINT32 val = 0x63855a4d;              // orrvs r5, r5, #0x4d, 20.  aka MZ nop
    if (!WriteFile(hFile, &val, sizeof(val), &dwRead, NULL) || dwRead != sizeof(val)) {
        goto failed;
    }
    val = 0xea000000 | (offset >> 2);   // ea = B offset
    if (!WriteFile(hFile, &val, sizeof(val), &dwRead, NULL) || dwRead != sizeof(val)) {
        goto failed;
    }

    CloseHandle(hFile);
    return TRUE;
}

int __cdecl wmain(int argc, WCHAR **argv)
{
    BOOL fNeedHelp = FALSE;

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

              default:
                printf("Unknown argument: %ls\n", argv[arg]);
                fNeedHelp = TRUE;
                break;
            }
        }
        else {
            if (!MakeRaw(argv[arg])) {
                return 1;
            }
        }
    }

    if (argc == 1) {
        fNeedHelp = TRUE;
    }

    if (fNeedHelp) {
        printf(
               "Usage:\n"
               "    mkarmraw [options] images...\n"
               "Options:\n"
               "    /?                -- Display this help screen.\n"
               "Summary:\n"
               "    Converts a 512-byte aligned PE image into a raw ARM boot file.\n"
              );
    }

    return 0;
}

//
///////////////////////////////////////////////////////////////// End of File.
