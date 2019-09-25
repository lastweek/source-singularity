//
// CreateProcess.c - A benchmark program
//
// Copyright Microsoft Corporation.
// All rights reserved.
//

#include <winlean.h>
#include <stdio.h>

LARGE_INTEGER frequency;

#define GetCycleCount() __rdtsc()
ULONG64
__rdtsc(VOID);
#pragma intrinsic(__rdtsc)

void ErrorExit(char *function)
{
    VOID *message;
    DWORD error = GetLastError();

    FormatMessage(
        FORMAT_MESSAGE_ALLOCATE_BUFFER |
        FORMAT_MESSAGE_FROM_SYSTEM,
        NULL,
        error,
        MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),
        (LPTSTR) &message,
        0, NULL );

    printf("%s failed with error %d: %s", function, error, message);

    LocalFree(message);
    ExitProcess(error);
}

int GetChildStartTime(ULONG64* result)
{
    FILE* f = fopen("result.txt", "r");
    if (f != NULL)
    {
        char dummy[512];
        fgets(dummy, 512, f);
        fscanf(f, "%I64u", result);
        fclose (f);
        return 0;
    }
    ErrorExit("fopen");
    return -1;
}

void TimeProcess(char *imageName, BOOL fGetChildExecutionStart)
{
    BOOL result;
    STARTUPINFO startInfo;
    PROCESS_INFORMATION procInfo;
    ULONG64 baseline, created, started, exited, childup;

    //
    // The startup info can specify the window station, desktop, various
    // window parameters (title, position, etc) and standard handles for
    // the new process.
    //
    ZeroMemory(&startInfo, sizeof(startInfo));
    startInfo.cb = sizeof(startInfo);

    //
    // Time process creation.
    //
    baseline = GetCycleCount();

    result = CreateProcess(imageName,  // Application name to start.
                           imageName,  // Command line for new process.
                           NULL,  // ? child process can inherit this process.
                           NULL,  // ? child threads can inherit this process.
                           FALSE,  // Whether new process inherits our handles.
                           CREATE_SUSPENDED  // Process creation flags.
                           | DETACHED_PROCESS | CREATE_NO_WINDOW,
                           NULL,  // Environment.
                           NULL,  // Current directory.
                           &startInfo,  // Startup info.
                           &procInfo);  // Out: Process info.

    if (!result) {
        //
        // Failed to create process :-(
        //
        ErrorExit("CreateProcess");
    }

    //
    // Process creation was successful!
    //
    created = GetCycleCount();

    //
    // Time process start.
    //
    if (ResumeThread(procInfo.hThread) == -1) {
        ErrorExit("ResumeThread");
    }

    started = GetCycleCount();

    //
    // Time process execution.
    //
    WaitForSingleObject(procInfo.hProcess, INFINITE);
    exited = GetCycleCount();

    printf("\n\nTested process: %s\n", imageName);
    printf("Time to create process: %llu cycles\n",
           created - baseline);
    printf("Time to start process: %llu cycles\n",
           started - created);
    printf("Time to run process: %llu cycles\n",
           exited - started);
    printf("Total time: %llu cycles\n",
           exited - baseline);
    printf("CreateProcess started at %llu\n", baseline);

    if (fGetChildExecutionStart && GetChildStartTime(&childup) == 0)
    {
        printf("CreateProcess to first child instruction: %llu\n",
               childup - baseline);
    }
}

int __cdecl
main(int argc, char **argv)
{
    printf("\nProcess creation test\n\n");

    //
    // The frequency of the high-resolution performance counter cannot change
    // while the system is running.
    //
    if (QueryPerformanceFrequency(&frequency) == 0) {
        ErrorExit("QueryPerformanceFrequency");
    }
    printf("Performance Counter Frequency = %d counts/second\n\n", frequency);

    TimeProcess("MinProcess.exe", FALSE);
    TimeProcess("Child.exe", TRUE);
}
