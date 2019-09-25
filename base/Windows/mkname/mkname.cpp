//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research
//  Copyright (C) Microsoft Corporation
//
//  Contents:   Copy a PE image to a new file and embeds its name in it.
//              Created from mkcore.
//
#define UNICODE
#define _UNICODE

#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <winlean.h>
#include <assert.h>

//////////////////////////////////////////////////////////////////////////////
//
static BOOL s_fVerbose = FALSE;

typedef signed int INT;
typedef signed char INT8, *LPINT8;
typedef signed short INT16, *LPINT16;
typedef unsigned int UINT;
typedef unsigned char UINT8, *LPUINT8;
typedef unsigned short UINT16, *LPUINT16;

#define arrayof(a)      (sizeof(a)/sizeof(a[0]))

//////////////////////////////////////////////////////////////////////////////
//
static inline UINT Max(UINT a, UINT b)
{
    return a > b ? a : b;
}

static inline UINT Min(UINT a, UINT b)
{
    return a < b ? a : b;
}

static inline UINT Align(UINT nValue, UINT nPowerOf2)
{
    return (nValue + nPowerOf2 - 1) & ~(nPowerOf2 - 1);
}

DWORD RvaToFileOffset(DWORD nRva, UINT nSecs, PIMAGE_SECTION_HEADER pSecs)
{
    DWORD n;
    for (n = 0; n < nSecs; n++) {
        DWORD vaStart = pSecs[n].VirtualAddress;
        DWORD vaEnd = vaStart + pSecs[n].SizeOfRawData;

        if (nRva >= vaStart && nRva < vaEnd) {
            return pSecs[n].PointerToRawData + nRva - pSecs[n].VirtualAddress;
        }
    }
    return 0;
}

BOOL error(PCSTR pwzError)
{
    fprintf(stderr, "%s\n", pwzError);
    fclose(stderr);
    return FALSE;
}

void Dump(PBYTE pbData, ULONG cbData)
{
    for (ULONG n = 0; n < cbData; n += 16) {
        printf("        ");
        for (ULONG o = n; o < n + 16; o++) {
            if (o >= cbData) {
                printf("  ");
            }
            else {
                printf("%02x", pbData[o]);
            }
            if (o % 4 == 3) {
                printf(" ");
            }
        }
        printf(" ");
        for (ULONG o = n; o < n + 16; o++) {
            if (o >= cbData) {
                printf("  ");
            }
            else {
                if (pbData[o] >= ' ' && pbData[o] < 127) {
                    printf("%c", pbData[o]);
                }
                else {
                    printf(".");
                }
            }
        }
        printf("\n");
    }
}

//////////////////////////////////////////////////////////////////// CFileMap.
//
class CFileMap
{
  public:
    CFileMap()
    {
        m_pbData = NULL;
        m_cbData = 0;
    }

    ~CFileMap()
    {
        Close();
    }

  public:
    BOOL    Load(PCWSTR pwzFile);
    PBYTE   Seek(UINT32 cbPos);
    UINT32  Size();
    VOID    Close();

  protected:
    PBYTE   m_pbData;
    UINT32  m_cbData;
};

VOID CFileMap::Close()
{
    if (m_pbData) {
        UnmapViewOfFile(m_pbData);
        m_pbData = NULL;
    }
    m_cbData = 0;
}

UINT32 CFileMap::Size()
{
    return m_cbData;
}

PBYTE CFileMap::Seek(UINT32 cbPos)
{
    if (m_pbData && cbPos <= m_cbData) {
        return m_pbData + cbPos;
    }
    return NULL;
}

BOOL CFileMap::Load(PCWSTR pwzFile)
{
    Close();

    HANDLE hFile = CreateFile(pwzFile,
                              GENERIC_READ,
                              FILE_SHARE_READ,
                              NULL,
                              OPEN_EXISTING,
                              0,
                              NULL);
    if (hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }

    ULONG cbInFileData = GetFileSize(hFile, NULL);
    if (cbInFileData == 0xffffffff) {
        CloseHandle(hFile);
        return FALSE;
    }

    HANDLE hInFileMap = CreateFileMapping(hFile, NULL, PAGE_READONLY, 0, 0, NULL);
    CloseHandle(hFile);
    if (hInFileMap == NULL) {
        return FALSE;
    }

    m_pbData = (PBYTE)MapViewOfFile(hInFileMap, FILE_MAP_COPY, 0, 0, 0);
    CloseHandle(hInFileMap);
    if (m_pbData == NULL) {
        return FALSE;
    }
    m_cbData = cbInFileData;
    return TRUE;
}

//////////////////////////////////////////////////////////////////// CFileOut.
//
class CFileOut
{
  public:
    CFileOut();
    ~CFileOut();

  public:
    BOOL    Create(PCWSTR pwzFile);

    BOOL    Seek(UINT32 cbPos);
    BOOL    Write(PBYTE pbData, UINT32 cbData);
    BOOL    Read(PBYTE pbData, UINT32 cbData);
    BOOL    Zero(UINT32 cbData);
    BOOL    Delete();
    UINT32  Size();

    UINT32  Checksum();

    VOID    Close();

  protected:
    HANDLE  m_hFile;
    WCHAR   m_wzFile[MAX_PATH];
    UINT32  m_cbPos;
};

CFileOut::CFileOut()
{
    m_hFile = INVALID_HANDLE_VALUE;
    m_wzFile[0] = '\0';
    m_cbPos = 0;
}

CFileOut::~CFileOut()
{
    Close();
}

VOID CFileOut::Close()
{
    if (m_hFile != INVALID_HANDLE_VALUE) {
        CloseHandle(m_hFile);
        m_hFile = INVALID_HANDLE_VALUE;
    }
}

BOOL CFileOut::Seek(UINT32 cbPos)
{
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }
    if (SetFilePointer(m_hFile, cbPos, NULL, FILE_BEGIN) != cbPos) {
        return FALSE;
    }
    m_cbPos = cbPos;
    return TRUE;
}

BOOL CFileOut::Write(PBYTE pbData, UINT32 cbData)
{
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }

    DWORD dwWrote = 0;
    if (!WriteFile(m_hFile, pbData, cbData, &dwWrote, NULL) || dwWrote != cbData) {
        return FALSE;
    }
    m_cbPos += cbData;
    return TRUE;
}

BOOL CFileOut::Zero(UINT32 cbData)
{
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }

    UINT zero_size = cbData < 65536 ? cbData : 65536;
    PBYTE buf = new BYTE [zero_size];
    assert(buf);

    if (!buf) {
        return FALSE;
    }

    ZeroMemory(buf, zero_size);

    for (; cbData > 0; cbData -= zero_size) {
        if (zero_size > cbData) {
            zero_size = cbData;
        }
        if (!Write(buf, zero_size)) {
            delete[] buf;
            return FALSE;
        }
    }
    delete[] buf;
    buf = NULL;

    return TRUE;
}

BOOL CFileOut::Delete()
{
    if (m_hFile != INVALID_HANDLE_VALUE) {
        Close();
        return DeleteFile(m_wzFile);
    }
    return FALSE;
}

UINT32 CFileOut::Size()
{
    return SetFilePointer(m_hFile, 0, NULL, FILE_END);
}

BOOL CFileOut::Read(PBYTE pbData, UINT32 cbData)
{
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }

    DWORD dwRead = 0;
    if (!ReadFile(m_hFile, pbData, cbData, &dwRead, NULL) || dwRead != cbData) {
        return FALSE;
    }
    m_cbPos += cbData;
    return TRUE;
}

BOOL CFileOut::Create(PCWSTR pwzFile)
{
    Close();
    m_wzFile[0] = '\0';
    m_hFile = CreateFile(pwzFile,
                         GENERIC_READ | GENERIC_WRITE,
                         0, NULL, CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }
    wcscpy(m_wzFile, pwzFile);
    m_cbPos = 0;
    return TRUE;
}


UINT32 CFileOut::Checksum()
{
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }

    PBYTE buf = new BYTE [65536];
    assert(buf);

    if (!buf) {
        return ~0u;
    }

    UINT32 size = Size();
    UINT32 sum = 0;

    if (!Seek(0)) {
        assert(!"Couldn't seek.");
        delete[] buf;
        return ~0u;
    }

    for (UINT32 pos = 0; pos < size;) {
        UINT32 read = size - pos < 65536 ? size - pos : 65536;

        if (!Read(buf, read)) {
            printf("Pos: %d/%d\n", pos, m_cbPos);
            printf("Len: %d\n", size);
            __asm int 3;
            assert(!"Couldn't read.");
            delete[] buf;
            return ~0u;
        }

        UINT32 *pBeg = (UINT32*)(buf);
        UINT32 *pEnd = (UINT32*)(buf + read);

        while (pBeg < pEnd) {
            sum += *pBeg++;
        }

        pos += read;
    }

    delete[] buf;
    buf = NULL;

    return sum;
}

BOOL UpdateInPlace(PWCHAR pwzFile)
{
    BOOL fGood = FALSE;
    HANDLE hFile = CreateFile(pwzFile, GENERIC_WRITE | GENERIC_READ,
                              0, NULL, OPEN_EXISTING, 0, NULL);
    if (hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }

    PWCHAR pwzName = pwzFile;
    PWCHAR pwz;

    if ((pwz = wcsrchr(pwzName, ':')) != NULL) {
        pwzName = pwz + 1;
    }
    if ((pwz = wcsrchr(pwzName, '\\')) != NULL) {
        pwzName = pwz + 1;
    }
    _wcslwr(pwzName);

    CHAR rbBlock[512];
    DWORD dwDone = 0;
    if (ReadFile(hFile, rbBlock, sizeof(rbBlock), &dwDone, NULL) &&
        dwDone == sizeof(rbBlock) &&
        rbBlock[0] == 'M' &&
        rbBlock[1] == 'Z') {

        memset(rbBlock + 64, 0, 64);
        wcscpy((PWCHAR)(rbBlock + 68), pwzName);

        if (SetFilePointer(hFile, 0, NULL, FILE_BEGIN) == 0) {
            dwDone = 0;
            if (WriteFile(hFile, rbBlock, sizeof(rbBlock), &dwDone, NULL) &&
                dwDone == sizeof(rbBlock)) {
                fGood = TRUE;
            }
        }
    }

    CloseHandle(hFile);
    return fGood;
}

int __cdecl wmain(int argc, WCHAR **argv)
{
    BOOL fNeedHelp = FALSE;
    BOOL fGood = FALSE;
    BOOL fUpdateInPlace = FALSE;
    CFileOut output;
    CFileMap input;
    PWCHAR pwzOutput = NULL;

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

              case 'u':                                 // Update in place.
              case 'U':
                fUpdateInPlace = TRUE;
                break;

              case 'o':                                 // Output file.
              case 'O':
                output.Close();
                pwzOutput = argp;
                if (!output.Create(pwzOutput)) {
                    fprintf(stderr, "Could not open output file: %ls\n", pwzOutput);
                    pwzOutput = NULL;
                    break;
                }
                printf("%ls:\n", pwzOutput);
                break;

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
            if (fUpdateInPlace) {
                if (!UpdateInPlace(argv[arg])) {
                    fprintf(stderr, "Couldn't update file: %ls\n", argv[arg]);
                    break;
                }
                continue;
            }

            if (pwzOutput == NULL) {
                fprintf(stderr, "Must specify output file before input files.\n");
                fNeedHelp = TRUE;
                break;
            }

            if (!input.Load(argv[arg])) {
                fprintf(stderr, "Couldn't open input file: %ls\n", argv[arg]);
                output.Delete();
                break;
            }

            PWCHAR pwzName = argv[arg];
            PWCHAR pwz;

            if ((pwz = wcsrchr(pwzName, ':')) != NULL) {
                pwzName = pwz + 1;
            }
            if ((pwz = wcsrchr(pwzName, '\\')) != NULL) {
                pwzName = pwz + 1;
            }
            _wcslwr(pwzName);

            PBYTE pbData = input.Seek(0);
            UINT32 cbData = input.Size();

            output.Seek(0);
            output.Write(pbData, cbData);
            output.Seek(64);
            output.Zero(64);
            output.Seek(68);
            output.Write((PBYTE)pwzName, (wcslen(pwzName) + 1) * sizeof(WCHAR));

            output.Close();
            pwzOutput = NULL;
            fGood = TRUE;
        }
    }
    if (!fGood) {
        output.Delete();
    }

    if (argc == 1) {
        fNeedHelp = TRUE;
    }

    if (fNeedHelp) {
        printf(
               "Usage:\n"
               "    mkname [options] images...\n"
               "Options:\n"
               "    /o:out_file   -- Specify output file.\n"
               "    /u            -- Update input files in place.\n"
               "    /?            -- Display this help screen.\n"
               "Summary:\n"
               "    Copies the file and writes its name into the DOS section of header.\n");
    }

    return 0;
}

//
///////////////////////////////////////////////////////////////// End of File.
