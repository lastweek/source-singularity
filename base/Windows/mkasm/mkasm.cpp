//////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research
//  Copyright (C) Microsoft Corporation
//
//  File:       mkasm.cpp
//
//  Contents:   Converts binary files into .asm or .cs files.
//
#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <winlean.h>
#include <assert.h>

//////////////////////////////////////////////////////////////////////////////
//
enum {
    TARGET_BASE     = 0x60000,
    TARGET_RANGE    = 0x10000,
};

BOOL fAsm = TRUE;
BOOL fCpp = FALSE;
BOOL fManaged = FALSE;
BOOL fCompress = FALSE;
BOOL fList = FALSE;
BOOL fAllow64 = FALSE;

CHAR szByteByteVTable[] = "?_vtable@ClassVector_ClassVector_uint8@@2UClass_System_VTable@@A";
// struct Class_System_VTable ClassVector_ClassVector_uint8::_vtable

CHAR szByteByteSuffix[] = "@@2PAUClassVector_ClassVector_uint8@@A";
// ?c_Content@Class_Microsoft_Singularity_Shell_Slides@@2PAUClassVector_ClassVector_uint8@@A
// struct ClassVector_ClassVector_uint8 * Class_Microsoft_Singularity_Shell_Slides::c_Content

CHAR szByteVTable[] = "?_vtable@ClassVector_uint8@@2UClass_System_VTable@@A";
// struct Class_System_VTable ClassVector_uint8::_vtable

CHAR szByteSuffix[] = "@@2PAUClassVector_uint8@@A";
// ?c_Content@Class_Microsoft_Singularity_Shell_Slides@@2PAUClassVector_ClassVector_uint8@@A
// struct ClassVector_ClassVector_uint8 * Class_Microsoft_Singularity_Shell_Slides::c_Content


//////////////////////////////////////////////////////////////////////////////
class CFileInfo
{
  public:
    CFileInfo()
    {
        m_pszFile = NULL;
        m_pNext = NULL;
        m_cbInput = 0;
        m_cbOutput = 0;
    }

    BOOL SetFileName(PCSTR pszFile)
    {
        m_pszFile = pszFile;
        return TRUE;
    }

    BOOL SetFileAndSize()
    {
        HANDLE hFile = CreateFile(m_pszFile,
                                  GENERIC_READ,
                                  FILE_SHARE_READ,
                                  NULL,
                                  OPEN_EXISTING,
                                  0,
                                  NULL);
        if (hFile == INVALID_HANDLE_VALUE) {
            return FALSE;
        }

        m_cbInput = GetFileSize(hFile, NULL);
        CloseHandle(hFile);

        if (m_cbInput == 0xffffffff) {
            m_cbInput = 0;
            return FALSE;
        }

        m_cbOutput = m_cbInput;
        return TRUE;
    }

    BOOL SetOutputSize(UINT32 cbOutput)
    {
        m_cbOutput = cbOutput;
        return TRUE;
    }

    CFileInfo * m_pNext;
    PCSTR       m_pszFile;
    UINT32      m_cbInput;
    UINT32      m_cbOutput;
};

//////////////////////////////////////////////////////////////////// CFileMap.
//
class CFileMap
{
  public:
    CFileMap();
    ~CFileMap();

  public:
    BOOL    Load(PCSTR pszFile);
    PBYTE   Seek(UINT32 cbPos);
    UINT32  Size();
    VOID    Close();

  protected:
    PBYTE   m_pbData;
    UINT32  m_cbData;
};

CFileMap::CFileMap()
{
    m_pbData = NULL;
    m_cbData = 0;
}

CFileMap::~CFileMap()
{
    Close();
}

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

BOOL CFileMap::Load(PCSTR pszFile)
{
    Close();

    HANDLE hFile = CreateFile(pszFile,
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
    BOOL    Create(PCSTR pszFile);
    BOOL    IsOpen();

    BOOL    Write(PBYTE pbData, UINT32 cbData);
    BOOL    Print(PCSTR pszMsg, ...);
    BOOL    VPrint(PCSTR pszMsg, va_list args);
    BOOL    Delete();

    VOID    Close();

  protected:
    HANDLE  m_hFile;
    CHAR    m_szFile[MAX_PATH];
    CHAR    m_szBuffer[4096];
    INT     m_cbBuffer;
};

CFileOut::CFileOut()
{
    m_hFile = INVALID_HANDLE_VALUE;
    m_szFile[0] = '\0';
    m_cbBuffer = 0;
}

CFileOut::~CFileOut()
{
    Close();
}

VOID CFileOut::Close()
{
    if (m_hFile != INVALID_HANDLE_VALUE) {
        if (m_cbBuffer) {
            Write((PBYTE)m_szBuffer, m_cbBuffer);
            m_cbBuffer = 0;
        }
        CloseHandle(m_hFile);
        m_hFile = INVALID_HANDLE_VALUE;
    }
}

BOOL CFileOut::IsOpen()
{
    return (m_hFile != INVALID_HANDLE_VALUE);
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
    return TRUE;
}

BOOL CFileOut::VPrint(PCSTR pszMsg, va_list args)
{
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }

    INT cbUsed = m_cbBuffer;
    INT cbData;

    cbData = _vsnprintf(m_szBuffer + cbUsed, sizeof(m_szBuffer)-cbUsed-1, pszMsg, args);
    m_cbBuffer += cbData;

    if (m_szBuffer[m_cbBuffer - 1] == '\n' ||
        m_szBuffer[m_cbBuffer - 1] == '\r') {

        cbData = m_cbBuffer;
        m_cbBuffer = 0;
        return Write((PBYTE)m_szBuffer, cbData);
    }
    return TRUE;
}

BOOL CFileOut::Print(PCSTR pszMsg, ...)
{
    BOOL f;

    va_list args;
    va_start(args, pszMsg);
    f = VPrint(pszMsg, args);
    va_end(args);

    return f;
}

BOOL CFileOut::Delete()
{
    if (m_hFile != INVALID_HANDLE_VALUE) {
        Close();
        return DeleteFile(m_szFile);
    }
    return FALSE;
}

BOOL CFileOut::Create(PCSTR pszFile)
{
    Close();
    m_szFile[0] = '\0';
    m_hFile = CreateFile(pszFile,
                         GENERIC_WRITE,
                         0, NULL, CREATE_ALWAYS,
                         FILE_ATTRIBUTE_NORMAL | FILE_FLAG_SEQUENTIAL_SCAN, NULL);
    if (m_hFile == INVALID_HANDLE_VALUE) {
        return FALSE;
    }
    strcpy(m_szFile, pszFile);
    m_cbBuffer = 0;
    return TRUE;
}
//
//////////////////////////////////////////////////////////////////////////////

class COutput
{
    protected:
    UINT m_nOffset;
    CFileOut *m_pfOutput;

    public:
    COutput(CFileOut *pfOutput)
    {
        m_pfOutput = pfOutput;
        m_nOffset = 0;
    }

    BOOL VPrint(PCSTR pszMsg, va_list args)
    {
        return m_pfOutput->VPrint(pszMsg, args);
    }

    BOOL Print(PCSTR pszMsg, ...)
    {
        BOOL f;

        va_list args;
        va_start(args, pszMsg);
        f = m_pfOutput->VPrint(pszMsg, args);
        va_end(args);

        return f;
    }

    virtual void Dump(PBYTE pbData, UINT cbData) = 0;

    virtual void Finish()
    {
        if ((m_nOffset % 16) != 0) {
            m_pfOutput->Print("\n");
        }
        m_nOffset = 0;
    }

    UINT Size()
    {
        return m_nOffset;
    }
};

class CAsmOutput : public COutput
{
    public:
    CAsmOutput(CFileOut *pfOutput)
        : COutput(pfOutput)
    {
    }

    void Dump(PBYTE pbData, UINT cbData)
    {
        PBYTE pbEnd = pbData + cbData;

        for (; pbData < pbEnd; pbData++, m_nOffset++) {
            switch (m_nOffset % 16) {
              case 0:
                Print("        uint8   %03xh", *pbData);
                break;
              default:
                Print(",%03xh", *pbData);
                break;
              case 15:
                Print(",%03xh\n", *pbData);
                break;
            }
        }
    }
};

class CSharpOutput : public COutput
{
    public:
    CSharpOutput(CFileOut *pfOutput)
        : COutput(pfOutput)
    {
    }

    void Dump(PBYTE pbData, UINT cbData)
    {
        PBYTE pbEnd = pbData + cbData;

        for (; pbData < pbEnd; pbData++, m_nOffset++) {
            switch (m_nOffset % 16) {
              case 0:
                Print("            0x%02x,", *pbData);
                break;
              default:
                Print("0x%02x,", *pbData);
                break;
              case 15:
                Print("0x%02x,\n", *pbData);
                break;
            }
        }
    }
};

//////////////////////////////////////////////////////////////////////////////
//
UINT DumpBmp(const char *pszFile, COutput *output, PBYTE pbData, UINT cbData)
{
#pragma pack(2)
    struct BITMAPFILEHEADER {
        UINT16  bfType;
        UINT32  bfSize;
        UINT16  bfReserved1;
        UINT16  bfReserved2;
        UINT32  bfOffBits;
    };

    struct BITMAPINFOHEADER {
        UINT32  biSize;
        UINT32  biWidth;
        UINT32  biHeight;
        UINT16  biPlanes;
        UINT16  biBitCount;
        UINT32  biCompression;
        UINT32  biSizeImage;
        UINT32  biXPelsPerMeter;
        UINT32  biYPelsPerMeter;
        UINT32  biClrUsed;
        UINT32  biClrImportant;
    };
#pragma pack()

    BITMAPFILEHEADER *pbmf = (BITMAPFILEHEADER *)pbData;
    BITMAPINFOHEADER *pbmi = (BITMAPINFOHEADER *)(pbmf + 1);

    if (pbmf->bfType != 'MB') {
        fprintf(stderr, "Can't convert non-BMP files to BMP compression.\n");
        return 0;
    }

    UINT cbDumped = 0;
    INT16 nValue;
    UINT cbScanLine = (((pbmi->biWidth * pbmi->biBitCount) + 31) & ~31) / 8;
    PBYTE pbLine = pbData + pbmf->bfOffBits;
    //PBYTE pbOut = pbData + pbmf->bfOffBits;

    pbmi->biCompression |= 0xff000000;
    if (output != NULL) {
        output->Dump(pbData, pbmf->bfOffBits);
    }
    cbDumped += pbmf->bfOffBits;

    for (UINT i = 0; i < pbmi->biHeight; i++) {
        PBYTE pbIn = pbLine;
        PBYTE pbRaw = pbIn;
        PBYTE pbEnd = pbLine + cbScanLine;

        while (pbIn < pbEnd) {
            if (pbIn + 6 < pbEnd &&
                pbIn[3] == pbIn[0] &&
                pbIn[4] == pbIn[1] &&
                pbIn[5] == pbIn[2]) {

                PBYTE pbBase = pbIn;
                pbIn += 3;

                while (pbIn + 3 <= pbEnd &&
                       pbIn[0] == pbBase[0] &&
                       pbIn[1] == pbBase[1] &&
                       pbIn[2] == pbBase[2]) {

                    pbIn += 3;
                }

                if (pbBase > pbRaw) {
                    nValue = (INT16)(pbBase - pbRaw);
                    if (output != NULL) {
                        output->Dump((PBYTE)&nValue, sizeof(nValue));
                        output->Dump(pbRaw, pbBase - pbRaw);
                    }
                    cbDumped += sizeof(nValue);
                    cbDumped += pbBase - pbRaw;
                }

                nValue = (INT16)(-((pbIn - pbBase) / 3));
                if (output != NULL) {
                    output->Dump((PBYTE)&nValue, sizeof(nValue));
                    output->Dump(pbBase, 3);
                }
                cbDumped += sizeof(nValue);
                cbDumped += 3;

                pbRaw = pbIn;
            }
            else {
                pbIn++;
            }
        }

        if (pbEnd > pbRaw) {
            nValue = (INT16)(pbEnd - pbRaw);
            if (output != NULL) {
                output->Dump((PBYTE)&nValue, sizeof(nValue));
                output->Dump(pbRaw, pbEnd - pbRaw);
            }
            cbDumped += sizeof(nValue);
            cbDumped += pbEnd - pbRaw;
        }

        pbLine += cbScanLine;
    }

    if (output != NULL) {
        printf("    %s from %8d to %8d bytes\n", pszFile, cbData, cbDumped);
        if (output->Size() != cbDumped) {
            fprintf(stderr, "Failure in compression: %d reported, %d written\n",
                    cbDumped, output->Size());
        }
        output->Finish();
    }

    return cbDumped;
}

char *find_contents64(CFileMap *pfFile,
                    PIMAGE_NT_HEADERS64 ppe,
                    UINT32 *pcbEntry,
                    UINT32 *pcbBase,
                    UINT32 *pcbSize,
                    PBYTE *ppbData)
{
    PIMAGE_SECTION_HEADER psec;

    fprintf(stderr,"Processing a 64-bit image.\n");

    psec = IMAGE_FIRST_SECTION(ppe);

    if (ppe->FileHeader.NumberOfSections != 1) {
        fprintf(stderr, "Warning: More than one section (.pdata)\n");
    }

    if (ppe->OptionalHeader.SizeOfInitializedData != 0) {
        fprintf(stderr, "Image has initialized data outside of text section.\n");
    }

    if (ppe->OptionalHeader.SizeOfUninitializedData != 0) {
        return "Image has uninitialized data outside of text section.";
    }

    if (psec->PointerToRawData == 0) {
        return "Image has no text content.";
    }

    if (pfFile->Seek(psec->PointerToRawData) == NULL) {
        return "Image text section is invalid.";
    }

    *pcbEntry =(UINT32) ppe->OptionalHeader.ImageBase + ppe->OptionalHeader.AddressOfEntryPoint;
    *pcbBase = (UINT32) ppe->OptionalHeader.ImageBase;
    *pcbSize = ppe->OptionalHeader.SizeOfImage;
    *ppbData = pfFile->Seek(0);

    return NULL;
}
char *find_contents32(CFileMap *pfFile,
                    PIMAGE_NT_HEADERS ppe,
                    UINT32 *pcbEntry,
                    UINT32 *pcbBase,
                    UINT32 *pcbSize,
                    PBYTE *ppbData)
{
    PIMAGE_SECTION_HEADER psec;

    psec = IMAGE_FIRST_SECTION(ppe);

    if (ppe->FileHeader.NumberOfSections != 1) {
        return "Image has more than one sections.";
    }

    if (ppe->OptionalHeader.SizeOfInitializedData != 0) {
        return "Image has initialized data outside of text section.";
    }

    if (ppe->OptionalHeader.SizeOfUninitializedData != 0) {
        return "Image has uninitialized data outside of text section.";
    }

    if (psec->PointerToRawData == 0) {
        return "Image has no text content.";
    }

    if (pfFile->Seek(psec->PointerToRawData) == NULL) {
        return "Image text section is invalid.";
    }

    *pcbEntry = ppe->OptionalHeader.ImageBase + ppe->OptionalHeader.AddressOfEntryPoint;
    *pcbBase = ppe->OptionalHeader.ImageBase;
    *pcbSize = ppe->OptionalHeader.SizeOfImage;
    *ppbData = pfFile->Seek(0);

    return NULL;
}

char *find_contents(CFileMap *pfFile,
                    UINT32 *pcbEntry,
                    UINT32 *pcbBase,
                    UINT32 *pcbSize,
                    PBYTE *ppbData)
{
    PIMAGE_DOS_HEADER pdos;
    PIMAGE_NT_HEADERS ppe;
    //PIMAGE_NT_HEADERS64 ppe64;

    *pcbEntry = 0;
    *pcbBase = 0;
    *pcbSize = 0;
    *ppbData = NULL;

    // Read in the PE image header
    //
    pdos = (PIMAGE_DOS_HEADER)pfFile->Seek(0);
    if (pdos == NULL || pdos->e_magic != IMAGE_DOS_SIGNATURE) {
        return "Image doesn't have MZ signature.";
    }

    ppe = (PIMAGE_NT_HEADERS)pfFile->Seek(pdos->e_lfanew);
    if (ppe == NULL || ppe->Signature != IMAGE_NT_SIGNATURE) {
        return "Image doesn't have PE signature.";
    }

    if (ppe->FileHeader.Machine == IMAGE_FILE_MACHINE_AMD64) {
        if (fAllow64) {
            return find_contents64(pfFile, (PIMAGE_NT_HEADERS64) ppe, pcbEntry, pcbBase, pcbSize, ppbData);
        }
        else {
            return "Image is 64-bit. Use /64 option";
        }
    }
    else return find_contents32(pfFile, ppe, pcbEntry, pcbBase, pcbSize, ppbData);
}

BOOL dump_pe(COutput *pOutput, CFileMap *pInput, PCSTR pszRoot)
{
    UINT32 cbEntry = 0;
    UINT32 cbBase = 0;
    UINT32 cbSize = 0;
    PBYTE pbData = NULL;

    char *error = find_contents(pInput, &cbEntry, &cbBase, &cbSize, &pbData);
    if (error != NULL) {
        fprintf(stderr, "Failed: %s\n", error);
        return FALSE;
    }

    if (cbEntry < cbBase || cbEntry >= cbBase + cbSize) {
        fprintf(stderr, "Failed: Image entry point is not in text section.");
        return FALSE;
    }

    if (cbBase < TARGET_BASE || cbBase > TARGET_BASE + TARGET_RANGE) {
        fprintf(stderr, "Failed: Image is not based at 0x%x.\n", TARGET_BASE);
        return FALSE;
    }

    printf("Total text section:  %d bytes\n", cbSize);

    // Write .asm data.
    //
    pOutput->Print("%s_ent  EQU  0%08xh\n", pszRoot, cbEntry);
    pOutput->Print("%s_dst  EQU  0%08xh\n", pszRoot, cbBase);
    pOutput->Print("%s_siz  EQU  0%08xh\n", pszRoot, cbSize);
    pOutput->Print("%s_dat  ", pszRoot);
    pOutput->Dump(pbData, cbSize);
    pOutput->Finish();
    pOutput->Print("\n");

    return TRUE;
}

BOOL blob_to_asm(COutput *pOutput, CFileMap *pInput)
{
    // Copy the rest of the image.
    //
    pOutput->Dump(pInput->Seek(0), pInput->Size());
    pOutput->Finish();
    return TRUE;
}

int CompareName(PCSTR psz1, PCSTR psz2)
{
    for (;;) {
        CHAR c1 = *psz1;
        CHAR c2 = *psz2;
        if (c1 >= 'A' && c1 <= 'Z') {
            c1 = c1 - 'A' + 'a';
        }
        if (c2 >= 'A' && c2 <= 'Z') {
            c2 = c2 - 'A' + 'a';
        }

        if ((c1 >= '0' && c1 <= '9') && (c2 >= '0' && c2 <= '9')) {
            for (c1 = 0; *psz1 >= '0' && *psz1 <= '9'; psz1++) {
                c1 = c1 * 10 + (*psz1 - '0');
            }
            psz1--;
            for (c2 = 0; *psz2 >= '0' && *psz2 <= '9'; psz2++) {
                c2 = c2 * 10 + (*psz2 - '0');
            }
            psz2--;

        }
        if (c1 != c2) {
            return c1 - c2;
        }
        if (c1 == 0 && c2 == 0) {
            return 0;
        }
        psz1++;
        psz2++;
    }
}

PCHAR AppendToName(PCHAR pszDst, PCSTR pszSrc)
{
    while (*pszSrc) {
        if (*pszSrc == '.') {
            *pszDst++ = '_';
            pszSrc++;
        }
        else {
            *pszDst++ = *pszSrc++;
        }
    }
    return pszDst;
}

void AsmName(PCHAR pszAsmName, PCSTR pszNamespace, PCSTR pszClass, PCSTR pszField)
{
    pszAsmName = AppendToName(pszAsmName, "?c_");
    pszAsmName = AppendToName(pszAsmName, pszField);
    pszAsmName = AppendToName(pszAsmName, "@Class_");
    pszAsmName = AppendToName(pszAsmName, pszNamespace);
    pszAsmName = AppendToName(pszAsmName, "_");
    pszAsmName = AppendToName(pszAsmName, pszClass);
    *pszAsmName = '\0';
}

void CppClassName(PCHAR pszCppClassName, PCSTR pszNamespace, PCSTR pszClass)
{
    pszCppClassName = AppendToName(pszCppClassName, "Class_");
    pszCppClassName = AppendToName(pszCppClassName, pszNamespace);
    pszCppClassName = AppendToName(pszCppClassName, "_");
    pszCppClassName = AppendToName(pszCppClassName, pszClass);
    *pszCppClassName = '\0';
}

int __cdecl main(int argc, char **argv)
{
    BOOL fNeedHelp = FALSE;
    BOOL fFlattenPE = TRUE;
    PCSTR pszRoot = "asm";
    CFileOut cfOutput;
    CFileInfo rFiles[512];
    CFileInfo *pFiles = NULL;
    UINT cFiles = 0;
    CHAR szField[256] = "";
    CHAR szClass[512] = "";
    CHAR szNamespace[512] = "";
    CHAR szAsmName[1024];
    CHAR szCppClassName[1024];

    for (int arg = 1; arg < argc; arg++) {
        if (argv[arg][0] == '-' || argv[arg][0] == '/') {
            char *argn = argv[arg]+1;                   // Argument name
            char *argp = argn;                          // Argument parameter

            while (*argp && *argp != ':')
                argp++;
            if (*argp == ':')
                *argp++ = '\0';

            switch (argn[0]) {

              case 'a':                                 // ASM Format
              case 'A':
                fAsm = TRUE;
                break;

              case 'b':                                 // Binary Blob
              case 'B':
                fFlattenPE = FALSE;
                fManaged = TRUE;
                break;

              case 'c':                                 // C# Class
              case 'C':
                strcpy(szClass, argp);
                fManaged = TRUE;
                break;

              case 'f':                                 // C# Field
              case 'F':
                strcpy(szField, argp);
                fManaged = TRUE;
                break;

              case 'l':                                 // List of files
              case 'L':
                fManaged = TRUE;
                fList = TRUE;
                break;

              case 'm':                                 // C# Format
              case 'M':
                fAsm = FALSE;
                break;

              case 'n':                                 // C# Namespace
              case 'N':
                strcpy(szNamespace, argp);
                fManaged = TRUE;
                break;

              case 'o':                                 // Output file.
              case 'O':
                if (!cfOutput.Create(argp)) {
                    fprintf(stderr, "Could not open output file: %s\n", argp);
                }
                break;

              case 'p':                                 // Cpp Format
              case 'P':
                fCpp = TRUE;
                fAsm = FALSE;
                break;

              case 'r':                                 // Set Label Root
              case 'R':
                pszRoot = argp;
                break;

              case 'x':                                 // Compress BMP
              case 'X':                                 //
                fCompress = TRUE;
                fManaged = TRUE;
                break;

              case '6':                                 // 64-bit PE
                fAllow64 = TRUE;
                break;

              case 'h':                                 // Help
              case 'H':
              case '?':
                fNeedHelp = TRUE;
                break;

              default:
                printf("Unknown argument: %s\n", argv[arg]);
                fNeedHelp = TRUE;
                break;
            }
        }
        else {
            // Save the input files away in sorted linked list.
            CFileInfo *pNew = &rFiles[cFiles++];
            CFileInfo **ppHead = &pFiles;

            pNew->SetFileName(argv[arg]);
            while (*ppHead != NULL && CompareName(pNew->m_pszFile, (*ppHead)->m_pszFile) > 0) {
                ppHead = &(*ppHead)->m_pNext;
            }
            pNew->m_pNext = *ppHead;
            *ppHead = pNew;
        }
    }

    if (argc == 1) {
        fNeedHelp = TRUE;
    }

    if (!fNeedHelp && !cfOutput.IsOpen()) {
        fprintf(stderr, "No output file specified.\n");
        fNeedHelp = TRUE;
    }

    if (!fNeedHelp && pFiles == NULL) {
        fprintf(stderr, "No output file specified.\n");
        fNeedHelp = TRUE;
    }

    if (!fNeedHelp && fManaged &&
        (szField[0] == '\0' || szClass[0] == '\0')) {
        fprintf(stderr, "No field or class name specified for target.\n");
        fNeedHelp = TRUE;
    }

    if (fNeedHelp) {
        printf(
               "Usage:\n"
               "    mkasm /o:output [options] inputs\n"
               "Options:\n"
               "    /o:output     -- Specify output file.\n"
               "    /r:root       -- Set root label [defaults to `asm'].\n"
               "    /b            -- Treat file as binary blob (not PE file).\n"
               "    /a            -- Output ASM format (default for PE).\n"
               "    /m            -- Output C# format (default for blob).\n"
               "    /c:class      -- Set C# class.\n"
               "    /n:namespace  -- Set C# namespace.\n"
               "    /f:field      -- Set C# field.\n"
               "    /x            -- Use bizarre compression for BMP files.\n"
               "    /l            -- Output contents in an array (list).\n"
               "    /64           -- manipulate 64-bit PE files."
               "    /h or /?      -- Display this help screen.\n"
               "Summary:\n"
               "    Copies the contents of the input files into the output file\n"
               "    in .asm format.  Specific conversions exists for PE and BMP files.\n"
              );
        return 2;
    }

    //////////////////////////////////////////////////////////////////////////
    //
    //  At this point, we have input file(s), output file, and set of desired
    //  conversions.  Time to process the output.
    //

    BOOL fAbort = false;
    COutput *pOutput = NULL;
    CAsmOutput asmOutput(&cfOutput);
    CSharpOutput sharpOutput(&cfOutput);

    AsmName(szAsmName, szNamespace, szClass, szField);
    CppClassName(szCppClassName, szNamespace, szClass);

    if (fAsm) {
        pOutput = &asmOutput;
    }
    else {
        pOutput = &sharpOutput;
    }

    ULONG cbFiles = 0;
    UINT cFile = 0;
    for (CFileInfo *pFile = pFiles; pFile != NULL; pFile = pFile->m_pNext) {
        if (!pFile->SetFileAndSize()) {
            fprintf(stderr, "Unable to open %s, error = %d\n",
                    pFile->m_pszFile,
                    GetLastError());
            goto abort;
        }
        if (fCompress) {
            CFileMap cfInput;
            printf(".");

            if (!cfInput.Load(pFile->m_pszFile)) {
                fprintf(stderr, "Could not open input file: %s\n", pFile->m_pszFile);
                goto abort;
            }
            pFile->SetOutputSize(DumpBmp(pFile->m_pszFile, NULL, cfInput.Seek(0), cfInput.Size()));
            cfInput.Close();
        }

        cFile++;
        cbFiles += pFile->m_cbOutput;
    }

    //public: static struct ClassVector_ClassVector_uint8 *
    //            Class_Microsoft_Singularity_Shell_Slides::c_Content;

    //" (?c_Content@Class_Microsoft_Singularity_Shell_Slides@@2PAUClassVector_ClassVector_uint8@@A
    if (!fFlattenPE) {
        if (fAsm) {
            cfOutput.Print("externdef %s:NEAR\n", szByteVTable);

            if (fList) {
                cfOutput.Print("externdef %s:NEAR\n", szByteByteVTable);
            }
            else {
                cfOutput.Print("align 4\n");
                cfOutput.Print("        BARTOK_OBJECT_HEADER {} \n");
                cfOutput.Print("%s%s_0 UINT32  %s\n",
                               szAsmName, szByteSuffix, szByteVTable);
                cfOutput.Print("        UINT32  %d\n", cbFiles);
            }
        }
        else if (fCpp) {
            if (fList) {
                cFile = 0;
                for (CFileInfo *pFile = pFiles; pFile != NULL; pFile = pFile->m_pNext) {
                    cfOutput.Print("struct Vector_%s_%s_0_%d {\n",
                                   szCppClassName, szField, cFile);
                    cfOutput.Print("    uintptr                             headerwords[HDRWORDCOUNT];\n");
                    cfOutput.Print("    union {\n");
                    cfOutput.Print("        struct {\n");
                    cfOutput.Print("            Class_System_VTable *       vtable;\n");
                    cfOutput.Print("            uint32                      length;\n");
                    cfOutput.Print("            uint8                       data[%d];\n",
                                   pFile->m_cbOutput);
                    cfOutput.Print("        };\n");
                    cfOutput.Print("        ClassVector_uint8   object;\n");
                    cfOutput.Print("    };\n");
                    cfOutput.Print("};\n");

                    cFile++;
                }

                cfOutput.Print("struct Vector_%s_%s_0 {\n",
                               szCppClassName, szField);
                cfOutput.Print("    uintptr                             headerwords[HDRWORDCOUNT];\n");
                cfOutput.Print("    union {\n");
                cfOutput.Print("        struct {\n");
                cfOutput.Print("            Class_System_VTable *       vtable;\n");
                cfOutput.Print("            uint32                      length;\n");
                cfOutput.Print("            ClassVector_uint8 *         data[%d];\n", cFiles);
                cfOutput.Print("        };\n");
                cfOutput.Print("        ClassVector_ClassVector_uint8   object;\n");
                cfOutput.Print("    };\n");
                cfOutput.Print("};\n");

                cfOutput.Print("struct %s {\n", szCppClassName);
                cfOutput.Print("  private:\n");
                for (UINT i = 0; i < cFiles; i++) {
                    cfOutput.Print("    static Vector_%s_%s_0_%d c_%s_0_%d;\n",
                                   szCppClassName, szField, i,
                                   szField, i);
                }
                cfOutput.Print("    static Vector_%s_%s_0 c_%s_0;\n",
                               szCppClassName, szField, szField);
                cfOutput.Print("  public:\n");
                cfOutput.Print("    static ClassVector_ClassVector_uint8 * c_%s;\n", szField);
                cfOutput.Print("};\n");
                cfOutput.Print("\n");
                cfOutput.Print("ClassVector_ClassVector_uint8 * %s::c_%s = &%s::c_%s_0.object;\n",
                               szCppClassName, szField,
                               szCppClassName, szField);
                cfOutput.Print("\n");
                cfOutput.Print("Vector_%s_%s_0 %s::c_%s_0 = {\n",
                               szCppClassName, szField,
                               szCppClassName, szField);
                cfOutput.Print("    {},\n");
                cfOutput.Print("    (Class_System_VTable *)&ClassVector_ClassVector_uint8::_vtable,\n");
                cfOutput.Print("    %d,\n", cFiles);
                cfOutput.Print("    {\n");
                for (UINT i = 0; i < cFiles; i++) {
                    cfOutput.Print("        &%s::c_%s_0_%d.object,\n",
                                   szCppClassName, szField, i);
                }
                cfOutput.Print("    },\n");
                cfOutput.Print("};\n");
                cfOutput.Print("\n");
            }
            else {
                cfOutput.Print("struct Vector_%s_%s_0 {\n",
                               szCppClassName, szField);
                cfOutput.Print("    uintptr                             headerwords[HDRWORDCOUNT];\n");
                cfOutput.Print("    union { \n");
                cfOutput.Print("        struct {\n");
                cfOutput.Print("            Class_System_VTable *       vtable;\n");
                cfOutput.Print("            uint32                      length;\n");
                cfOutput.Print("            uint8                       data[%d];\n",
                               cbFiles);
                cfOutput.Print("        };\n");
                cfOutput.Print("        ClassVector_uint8   object;\n");
                cfOutput.Print("    };\n");
                cfOutput.Print("};\n");

                cfOutput.Print("struct %s {\n", szCppClassName);
                cfOutput.Print("  private:\n");
                cfOutput.Print("    static Vector_%s_%s_0 c_%s_0;\n",
                               szCppClassName, szField, szField);
                cfOutput.Print("  public:\n");
                cfOutput.Print("    static ClassVector_uint8 * c_%s;\n", szField);
                cfOutput.Print("};\n");
                cfOutput.Print("\n");
                cfOutput.Print("ClassVector_uint8 * %s::c_%s = &%s::c_%s_0.object;\n",
                               szCppClassName, szField,
                               szCppClassName, szField);
                cfOutput.Print("\n");
                cfOutput.Print("Vector_%s_%s_0 %s::c_%s_0 = {\n",
                               szCppClassName, szField,
                               szCppClassName, szField);
                cfOutput.Print("    {},\n");
                cfOutput.Print("    (Class_System_VTable *)&ClassVector_uint8::_vtable,\n");
                cfOutput.Print("    %d,\n", cbFiles);
                cfOutput.Print("    {\n");
            }
        }
        else {
            if (szNamespace) {
                cfOutput.Print("namespace %s {\n", szNamespace);
            }

            cfOutput.Print("    public class %s {\n", szClass);
            if (fList) {
                cfOutput.Print("        public static readonly byte[][] %s = {\n", szField);
            }
            else {
                cfOutput.Print("        public static readonly byte[] %s = {\n", szField);
            }
        }
    }

    cFile = 0;
    for (CFileInfo *pFile = pFiles; pFile != NULL; pFile = pFile->m_pNext) {
        CFileMap cfInput;
        printf(".");

        if (!cfInput.Load(pFile->m_pszFile)) {
            fprintf(stderr, "Could not open input file: %s\n", pFile->m_pszFile);
            goto abort;
        }

        if (fFlattenPE) {
            // Flatten PE file
            if (!dump_pe(pOutput, &cfInput, pszRoot)) {
                goto abort;
            }
        }
        else {
            if (fAsm) {
                if (fList) {
                    cfOutput.Print("\n");
                    cfOutput.Print("align 4\n");
                    cfOutput.Print("        BARTOK_OBJECT_HEADER {} \n");
                    cfOutput.Print("%s%s_0_%d UINT32  %s\n",
                                   szAsmName,
                                   szByteSuffix,
                                   cFile,
                                   szByteVTable);
                    cfOutput.Print("        UINT32  %d\n", cfInput.Size());
                }
            }
            else if (fCpp) {
                if (fList) {
                    cfOutput.Print("Vector_%s_%s_0_%d %s::c_%s_0_%d = {\n",
                                   szCppClassName, szField, cFile,
                                   szCppClassName, szField, cFile);
                    cfOutput.Print("    {},\n");
                    cfOutput.Print("    (Class_System_VTable *)&ClassVector_uint8::_vtable,\n");
                    cfOutput.Print("    %d,\n", cfInput.Size());
                    cfOutput.Print("    {\n");
                }
            }
            else {
                if (fList) {
                    cfOutput.Print("        new byte[] {\n");
                }
            }

            if (fCompress) {
                if (!DumpBmp(pFile->m_pszFile, pOutput, cfInput.Seek(0), cfInput.Size())) {
                    goto abort;
                }
            }
            else {
                pOutput->Dump(cfInput.Seek(0), cfInput.Size());
                pOutput->Finish();
            }

            if (fAsm) {
            }
            else if (fCpp) {
                if (fList) {
                    cfOutput.Print("    },\n");
                    cfOutput.Print("};\n");
                    cfOutput.Print("\n");
                }
            }
            else {
                if (fList) {
                    cfOutput.Print("        },\n");
                }
            }
        }

        cfInput.Close();
        cFile++;
    }

    if (!fFlattenPE) {
        if (fAsm) {
            if (fList) {
                // create list array at end.
                cfOutput.Print("\n");
                cfOutput.Print("align 4\n");
                cfOutput.Print("        BARTOK_OBJECT_HEADER {} \n");
                cfOutput.Print("public %s%s\n",
                               szAsmName,
                               szByteByteSuffix);
                cfOutput.Print("%s%s_0 UINT32  %s\n",
                               szAsmName,
                               szByteByteSuffix,
                               szByteByteVTable);
                cfOutput.Print("        UINT32  %d\n", cFiles);
                for (UINT i = 0; i < cFiles; i++) {
                    cfOutput.Print("        UINT32  %s%s_0_%d\n",
                                   szAsmName,
                                   szByteSuffix,
                                   i);
                }
                cfOutput.Print("\n");
                cfOutput.Print("align 4\n");
                cfOutput.Print("public %s%s\n",
                               szAsmName,
                               szByteByteSuffix);
                cfOutput.Print("%s%s UINT32  %s%s_0\n",
                               szAsmName,
                               szByteByteSuffix,
                               szAsmName,
                               szByteByteSuffix);
            }
            else {
                cfOutput.Print("\n");
                cfOutput.Print("align 4\n");
                cfOutput.Print("public %s%s\n",
                               szAsmName,
                               szByteSuffix);
                cfOutput.Print("%s%s UINT32  %s%s_0\n",
                               szAsmName,
                               szByteSuffix,
                               szAsmName,
                               szByteSuffix);
            }
        }
        else if (fCpp) {
            if (!fList) {
                cfOutput.Print("    },\n");
                cfOutput.Print("};\n");
                cfOutput.Print("\n");
            }
        }
        else
        {
            cfOutput.Print("        };\n");
            cfOutput.Print("    }\n");
            cfOutput.Print("}\n");
        }
    }

    if (fAbort) {
      abort:
        cfOutput.Delete();
        return 1;
    }
    cfOutput.Close();
    return 0;
}
//
///////////////////////////////////////////////////////////////// End of File.
