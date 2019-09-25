#include <windows.h>
#include <stdio.h>
#include <string.h>

typedef struct _BUFFER {
    PVOID Data;
    ULONG Size;
} BUFFER, *PBUFFER;

PBUFFER
FileRead(
    PCHAR Path
    )

{
    PBUFFER Buffer;
    ULONG BytesTransferred;
    HANDLE File;
    LARGE_INTEGER Size;

    File = CreateFile(Path,
                      GENERIC_READ,
                      FILE_SHARE_READ,
                      NULL,
                      OPEN_EXISTING,
                      0,
                      NULL);

    if (File == INVALID_HANDLE_VALUE) {

        printf("blgen: Error opening %s. [Error=%u]\n",
               Path,
               GetLastError());

        ExitProcess(GetLastError());
    }

    if (GetFileSizeEx(File, &Size) == FALSE) {

        printf("blgen: Error querying size of %s. [Error=%u]\n",
               Path,
               GetLastError());

        ExitProcess(GetLastError());
    }

    if (Size.HighPart != 0) {

        printf("blgen: File is too big!\n");
        ExitProcess(ERROR_NOT_ENOUGH_MEMORY);
    }

    Buffer = (PBUFFER) malloc(sizeof(Buffer));

    if (Buffer == NULL) {

        printf("blgen: Insufficient memory.\n");
        ExitProcess(ERROR_NOT_ENOUGH_MEMORY);
    }

    Buffer->Data = malloc(Size.LowPart);

    if (Buffer->Data == NULL) {

        printf("blgen: Insufficient memory.\n");
        ExitProcess(ERROR_NOT_ENOUGH_MEMORY);
    }

    Buffer->Size = Size.LowPart;

    if ((ReadFile(File,
                  Buffer->Data,
                  Buffer->Size,
                  &BytesTransferred,
                  NULL) == FALSE)

        ||

        (BytesTransferred != Buffer->Size)

        ) {

        printf("blgen: Error reading %s. [Error=%u]\n",
               Path,
               GetLastError());

        ExitProcess(GetLastError());
    }

    CloseHandle(File);

    return Buffer;
}

VOID
FileAppend(
    PCHAR Path,
    PVOID Buffer,
    ULONG Length
    )

{
    ULONG BytesTransferred;
    LARGE_INTEGER Distance;
    HANDLE File;

    File = CreateFile(Path,
                      GENERIC_READ | GENERIC_WRITE,
                      0,
                      NULL,
                      OPEN_ALWAYS,
                      FILE_ATTRIBUTE_NORMAL,
                      NULL);

    if (File == INVALID_HANDLE_VALUE) {

        printf("blgen: Error opening %s. [Error=%u]\n",
               Path,
               GetLastError());

        ExitProcess(GetLastError());
    }

    Distance.QuadPart = 0;

    if (SetFilePointerEx(File,
                         Distance,
                         NULL,
                         FILE_END) == FALSE) {

        printf("blgen: Error setting file pointer. [Error=%u]\n",
               GetLastError());

        ExitProcess(GetLastError());
    }

    if ((WriteFile(File,
                   Buffer,
                   Length,
                   &BytesTransferred,
                   NULL) == FALSE)

        ||

        (BytesTransferred != Length)) {

        printf("blgen: Error reading %s. [Error=%u]\n",
               Path,
               GetLastError());

        ExitProcess(GetLastError());
    }

    CloseHandle(File);

    return;
}

int
__cdecl
main(
    int argc,
    char **argv
    )

{
    PBUFFER COM;
    PBUFFER EXE;

    if (argc != 4) {

        printf("\n"
               "Boot Loader Generator (BLGEN)\n"
               "\n"
               "    Syntax:\n"
               "\n"
               "        blgen COM EXE Target\n"
               "\n");

        return 1;
    }

    COM = FileRead(argv[1]);
    EXE = FileRead(argv[2]);

    DeleteFile(argv[3]);

    FileAppend(argv[3], COM->Data, COM->Size);
    FileAppend(argv[3], EXE->Data, EXE->Size);

    return 0;
}
