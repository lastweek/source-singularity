//
// SingBench.c - A benchmark program
//
// Copyright Microsoft Corporation.
// All rights reserved.
//

#include <winlean.h>
#include <stdlib.h>
#include <stdio.h>

LARGE_INTEGER frequency;

int perfLoopCount = 10000;

HANDLE waitPerfEvent1, waitPerfEvent2;
ULONG64 startCount1, endCount1;
ULONG64 startCount2, endCount2;


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


//
// Read the processor's time stamp counter register
//
#define GetCycleCount() __rdtsc()
ULONG64
__rdtsc(VOID);
#pragma intrinsic(__rdtsc)


//
// Measure GetCycleCount call.
//
void DoGetCCPerf()
{
    ULONG64 before, after, elapsed;
    ULONG64 now;
    int loop;

    printf("\nMeasuring GetCycleCount call\n");

    before = GetCycleCount();

    for (loop = 0; loop < perfLoopCount; loop++) {
        now = GetCycleCount();
    }

    after = GetCycleCount();

    elapsed = after - before;
    printf("  Elapsed cycles = %d\n", elapsed);
    printf("  cycles/iteration = %d\n", elapsed / perfLoopCount);
}

//
// Measure ABI call.
//
void DoABIPerf()
{
    ULONG64 before, after, elapsed;
    int loop;

    DWORD dummy;

    printf("\nMeasuring ABI call using GetProcessId\n");

    before = GetCycleCount();

    for (loop = 0; loop < perfLoopCount; loop++) {
        dummy = GetProcessId(GetCurrentProcess());
    }

    after = GetCycleCount();

    elapsed = after - before;
    printf("  Elapsed cycles = %d\n", elapsed);
    printf("  cycles/iteration = %d\n", elapsed / perfLoopCount);
}


//
// Measure ABI call.
//
void DoABIPerf2()
{
    ULONG64 before, after, elapsed;
    int loop;

    LARGE_INTEGER dummy;

    printf("\nMeasuring ABI call using QueryPerformanceFrequency\n");

    before = GetCycleCount();

    for (loop = 0; loop < perfLoopCount; loop++) {
        (void)QueryPerformanceFrequency(&dummy);
    }

    after = GetCycleCount();

    elapsed = after - before;
    printf("  Elapsed cycles = %d\n", elapsed);
    printf("  cycles/iteration = %d\n", elapsed / perfLoopCount);
}

void DoABIPerf3()
{
    HANDLE hFile;
    LPCSTR lpFileName;

    char tempBuffer[TMP_MAX];

    ULONG64 before, after, elapsed;
    int loop;

    printf("\nMeasuring ABI call using SetFilePointer\n");

    lpFileName = tmpnam(tempBuffer);
    hFile = CreateFile(lpFileName, 0, FILE_SHARE_DELETE, NULL, CREATE_NEW,
                       FILE_ATTRIBUTE_TEMPORARY | FILE_FLAG_DELETE_ON_CLOSE,
                       NULL);

    if (hFile == INVALID_HANDLE_VALUE)
    {
        ErrorExit("CreateFile");
        return;
    }

    before = GetCycleCount();

    for (loop = 0; loop < perfLoopCount; loop++) {
        SetFilePointer(hFile, 0, NULL, FILE_BEGIN);
    }

    after = GetCycleCount();

    elapsed = after - before;
    printf("  Elapsed cycles = %d\n", elapsed);
    printf("  cycles/iteration = %d\n", elapsed / perfLoopCount);
}

void DoABIPerf4()
{
    HANDLE hFile;
    LPCSTR lpFileName;

    char tempBuffer[TMP_MAX];

    ULONG64 before, after, elapsed;
    int loop;

    printf("\nMeasuring ABI call using GetFilePointer\n");

    lpFileName = tmpnam(tempBuffer);
    hFile = CreateFile(lpFileName, 0, FILE_SHARE_DELETE, NULL, CREATE_NEW,
                       FILE_ATTRIBUTE_TEMPORARY | FILE_FLAG_DELETE_ON_CLOSE,
                       NULL);

    if (hFile == INVALID_HANDLE_VALUE)
    {
        ErrorExit("CreateFile");
        return;
    }

    before = GetCycleCount();

    for (loop = 0; loop < perfLoopCount; loop++) {
        // Returns file pointer position
        SetFilePointer(hFile, 0, NULL, FILE_CURRENT);
    }

    after = GetCycleCount();

    elapsed = after - before;
    printf("  Elapsed cycles = %d\n", elapsed);
    printf("  cycles/iteration = %d\n", elapsed / perfLoopCount);
}

static volatile int g_threads = 0;

typedef struct s_YieldStats
{
    ULONG64 start;
    ULONG64 end;
    UINT32  calls;
} YieldStats;

static DWORD WINAPI ThreadYieldTestMain(LPVOID lpParameter)
{
    YieldStats* stats = (YieldStats*)lpParameter;

    g_threads++;

    while (g_threads != 2)
    {
        Sleep(0);
    }

    stats->start = GetCycleCount();

    while (stats->calls++ < 10000)
    {
        Sleep(0);
    }

    stats->end = GetCycleCount();

    g_threads--;
    while (g_threads != 0)
    {
        Sleep(0);
    }
    return 0;
}

//
// Measure thread yield.
//
void DoYieldPerf()
{
    YieldStats stats1, stats2;
    HANDLE thread1;

    printf("\nYield performance\n");

    ZeroMemory(&stats1, sizeof(YieldStats));
    ZeroMemory(&stats2, sizeof(YieldStats));

    thread1 = CreateThread(NULL, 0, &ThreadYieldTestMain,
                           (LPVOID) &stats1, 0, NULL);
    if (thread1 == INVALID_HANDLE_VALUE)
    {
        ErrorExit("CreateThread(thread1)");
    }

    ThreadYieldTestMain((LPVOID) &stats2);

    CloseHandle(thread1);

    printf("Thread1 yield perf = %I64u / (2 * %u) = %I64u\n",
           stats1.end - stats1.start, stats1.calls,
           (stats1.end - stats1.start) / (2 * stats1.calls));

    printf("Thread2 yield perf = %I64u / (2 * %u) = %I64u\n",
           stats2.end - stats2.start, stats2.calls,
           (stats2.end - stats2.start) / (2 * stats2.calls));
}

//
// Part of DoWaitPerf.
//
DWORD WINAPI WaitPerfThread1(void *foo)
{
    int loop;

    startCount1 = GetCycleCount();
    for (loop = 0; loop < perfLoopCount; loop++) {
        SetEvent(waitPerfEvent2);
        WaitForSingleObject(waitPerfEvent1, INFINITE);
    }
    endCount1 = GetCycleCount();

    return 0;
}


//
// Another part of DoWaitPerf.
//
DWORD WINAPI WaitPerfThread2(void *foo)
{
    int loop;

    startCount2 = GetCycleCount();

    for (loop = 0; loop < perfLoopCount; loop++) {
        WaitForSingleObject(waitPerfEvent2, INFINITE);
        SetEvent(waitPerfEvent1);
    }
    SetEvent(waitPerfEvent1);

    endCount2 = GetCycleCount();

    return 0;
}

//
// Measure waiting/signaling of auto-reset events.
//
void DoWaitPerf()
{
    HANDLE thread1, thread2;

    //
    // Create the auto-reset events.
    //
    waitPerfEvent1 = CreateEvent(NULL, FALSE, FALSE, NULL);
    if (waitPerfEvent1 == NULL) {
        ErrorExit("CreateEvent");
    }
    waitPerfEvent2 = CreateEvent(NULL, FALSE, FALSE, NULL);
    if (waitPerfEvent2 == NULL) {
        ErrorExit("CreateEvent");
    }

    printf("\nStarting WaitTest threads\n");

    //
    // Create the threads.
    //
    thread1 = CreateThread(NULL, 0, WaitPerfThread1, NULL,
                           CREATE_SUSPENDED, NULL);
    if (thread1 == NULL) {
        ErrorExit("CreateThread");
    }
    thread2 = CreateThread(NULL, 0, WaitPerfThread2, NULL,
                           CREATE_SUSPENDED, NULL);
    if (thread2 == NULL) {
        ErrorExit("CreateThread");
    }

    //
    // Start the threads running.
    //
    if (ResumeThread(thread2) == -1) {
        ErrorExit("ResumeThread");
    }
    if (ResumeThread(thread1) == -1) {
        ErrorExit("ResumeThread");
    }

    //
    // Output results after both threads have finished.
    //
    printf("Waiting for threads...\n");
    WaitForSingleObject(thread2, INFINITE);
    printf("Thread 2 finished\n");
    printf("  Elapsed cycles = %d\n", endCount2 - startCount2);
    printf("  cycles/iteration = %d\n",
           (endCount2 - startCount2) / perfLoopCount);
    WaitForSingleObject(thread1, INFINITE);
    printf("Thread 1 finished\n");
    printf("  Elapsed cycles = %d\n", endCount1 - startCount1);
    printf("  cycles/iteration = %d\n",
           (endCount1 - startCount1) / perfLoopCount);


    (void)CloseHandle(waitPerfEvent1);
    (void)CloseHandle(waitPerfEvent2);
}


//
// Client process for DoPong.
//
void DoPing(bytes)
{
    HANDLE pipe;
    DWORD mode;
    char *buffer;
    int loop;
    int got, wrote;

    //
    // Allocate some buffer space.
    //
    buffer = malloc(bytes);

    //
    // Establish connection to server.
    //
    pipe = CreateFile("\\\\.\\pipe\\SingBench",
                      GENERIC_READ | GENERIC_WRITE,
                      0,
                      NULL,
                      OPEN_EXISTING,
                      0,
                      NULL);
    if (pipe == INVALID_HANDLE_VALUE) {
        ErrorExit("CreateFile");
    }

    //
    // We want message, not byte-stream mode.
    //
    mode = PIPE_READMODE_MESSAGE;
    if (!SetNamedPipeHandleState(pipe, &mode, NULL, NULL)) {
        ErrorExit("SetNamedPipeHandleState");
    }

    //
    // Time the exchange of messages.
    //
    for (loop = 0; loop < perfLoopCount; loop++) {
        //
        // Write the message to the server.
        //
        if (!WriteFile(pipe, buffer, bytes, &wrote, NULL) || wrote != bytes) {
            ErrorExit("WriteFile");
        }
        //
        // Read the message back.
        //
        if (!ReadFile(pipe, buffer, bytes, &got, NULL) || got != bytes) {
            ErrorExit("ReadFile");
        }
    }

    CloseHandle(pipe);
}


//
// Test sending messages back and forth between processes.
//
void DoPong(int bytes)
{
    char szCmdLine[256];
    char *buffer;
    HANDLE pipe;
    BOOL created, connected;
    STARTUPINFO startInfo;
    PROCESS_INFORMATION procInfo;
    ULONG64 before, after, delta;
    int loop;
    int got, wrote;

    printf("\nStarting ping-pong test with %d byte messages\n", bytes);

    //
    // Allocate some buffer space.
    //
    buffer = malloc(bytes);

    //
    // We use named pipes instead of anonymous pipes because anonymous
    // pipes are only one-way, while named pipes can be duplex.
    //
    // Named pipes can either be byte-stream or message-based.  We're
    // using message-based (closer match to Singularity Channels).
    // We also set our pipe to blocking mode.
    //
    pipe = CreateNamedPipe("\\\\.\\pipe\\SingBench",  // Pipe name.
        PIPE_ACCESS_DUPLEX,  // Bi-directional.
        PIPE_TYPE_MESSAGE | PIPE_READMODE_MESSAGE | PIPE_WAIT,  // Pipe mode.
        1,  // MaxInstances.
        bytes,  // OutBufferSize.
        bytes,  // InBufferSize.
        INFINITE,  // DefaultTimeOut.
        NULL);  // SecurityAttributes.
    if (pipe == INVALID_HANDLE_VALUE) {
        free(buffer);
        ErrorExit("CreateNamedPipe");
    }

    //
    // Spawn child (client) process.
    //
    sprintf(szCmdLine, "SingBench %d", bytes);
    printf("Launching child process: %s\n", szCmdLine);
    ZeroMemory(&startInfo, sizeof(startInfo));
    startInfo.cb = sizeof(startInfo);
    created = CreateProcess("SingBench.exe",  // Application name to start.
                            szCmdLine,  // Command line for new process.
                            NULL,  // ? child process can inherit this process.
                            NULL,  // ? child threads can inherit this process.
                            FALSE,  // New process inherits our handles?
                            0,  // Process creation flags.
                            NULL,  // Environment.
                            NULL,  // Current directory.
                            &startInfo,  // Startup info.
                            &procInfo);  // Out: Process info.
    if (!created) {
        //
        // Failed to create process.
        //
        free(buffer);
        ErrorExit("CreateProcess");
    }


    //
    // Wait for child to phone home (if it hasn't already).
    //
    connected = ConnectNamedPipe(pipe, NULL);
    if (!connected && GetLastError() != ERROR_PIPE_CONNECTED) {
        free(buffer);
        ErrorExit("ConnectNamedPipe");
    }

    //
    // Time the exchange of messages.
    //
    before = GetCycleCount();
    for (loop = 0; loop < perfLoopCount; loop++) {
        //
        // Read the message from the client.
        //
        if (!ReadFile(pipe, buffer, bytes, &got, NULL) || got != bytes) {
            ErrorExit("ReadFile");
        }
        //
        // Write the message back.
        //
        if (!WriteFile(pipe, buffer, bytes, &wrote, NULL) || wrote != bytes) {
            ErrorExit("WriteFile");
        }
    }
    after = GetCycleCount();
    delta = (after - before) / 2;

    FlushFileBuffers(pipe);
    DisconnectNamedPipe(pipe);
    CloseHandle(pipe);
    free(buffer);

    printf("Done playing ping-pong with %d byte messages\n", bytes);
    printf("  Elapsed cycles = %d\n", delta);
    printf("  cycles/iteration = %d\n", delta / perfLoopCount);
}


int __cdecl
main(int argc, char **argv)
{
    int i;

    if (argc > 1) {
        //
        // If called with an argument, we're the DoPong client.
        //
        DoPing(atoi(argv[1]));
        ExitProcess(0);
    }

    printf("\nSingBench\n\n");

    //
    // The frequency of the high-resolution performance counter cannot change
    // while the system is running.
    //
    if (QueryPerformanceFrequency(&frequency) == 0) {
        ErrorExit("QueryPerformanceFrequency");
    }
    printf("Performance Counter Frequency = %I64u counts/second\n", frequency);

    DoGetCCPerf();
    DoABIPerf();
    DoABIPerf2();
    DoABIPerf3();
    DoABIPerf4();
    DoYieldPerf();
    DoWaitPerf();

    for (i = 1; i <= 65536; i *= 2) {
        DoPong(i);
    }
}
