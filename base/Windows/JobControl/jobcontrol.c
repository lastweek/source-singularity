// ----------------------------------------------------------------------------
//
// Program: JobControl
//
// Purpose: Run multiple processes within a job object and/or manually kill
//          existing job objects.  See usage for more details.
//
// (C) Microsoft Corporation
//
// ----------------------------------------------------------------------------

#define _WIN32_WINNT 0x0500

#define YESWINDOWSTATION
#define YESSECURITY

#include <winlean.h>

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct _CONTROLLED_PROCESS {
    HANDLE Thread;
    HANDLE Process;
    DWORD  ProcessId;
    BOOL   ErrorExitFatal;
} CONTROLLED_PROCESS, *PCONTROLLED_PROCESS;

typedef struct _CONTROLLED_PROCESS_SET {
    DWORD               ProcessCount;
    DWORD               MaxProcessCount;
    PCONTROLLED_PROCESS Processes;
} CONTROLLED_PROCESS_SET, *PCONTROLLED_PROCESS_SET;

typedef struct _MONITOR_THREAD_ARGS {
    HANDLE                  hJob;
    PCONTROLLED_PROCESS_SET pSet;
    DWORD                   dwTimeoutSeconds;
    HANDLE                  hMonitoringStarted;
} MONITOR_THREAD_ARGS, *PMONITOR_THREAD_ARGS;

// ----------------------------------------------------------------------------

static const DWORD dwCompletionKey = 2;

// Global job handle needed for graceful shutdown by control
// event handler.
static HANDLE ghJob = NULL;

static BOOL gbVerbose = FALSE;

#define tprintf(x, ...) \
    do { \
        if (gbVerbose) printf(x, __VA_ARGS__); \
    } while (FALSE)

// ----------------------------------------------------------------------------

static BOOL WINAPI CtrlHandler(DWORD dwCtrlType)
{
    tprintf("Caught control event %I32u", dwCtrlType);
    switch (dwCtrlType) {
      case CTRL_C_EVENT:
      case CTRL_BREAK_EVENT:
        GenerateConsoleCtrlEvent(dwCtrlType, 0);
      default:
        break;
    }
    if (ghJob != NULL) {
        TerminateJobObject(ghJob, (UINT)-1);
    }
    ExitProcess((UINT)-2);
}

static void Usage()
{
    printf(
"Usage:\n" \
"jobcontrol <command> <jobname> [options]\n" \
"\n" \
"where command is one of create, kill, query.\n" \
"\n" \
"CREATE COMMAND\n" \
"--------------\n" \
"\n" \
"The \"create\" command creates a job object and runs any number\n" \
"of commands with it.  The command runs for as long as the\n" \
"specified commands are executing.\n" \
"\n" \
"The options available are:\n" \
"  /LimitJobTime <seconds>          - Set limit on elapsed job time.\n" \
"  /LimitJobUserTime <seconds>      - Set limit on elapsed job user mode time.\n" \
"  /LimitProcessUserTime <seconds>  - Set limit on per-process user mode time\n" \
"  /B                               - Print basic accounting information.\n" \
"  /C <command>                     - Run command in job.\n" \
"  /T <command>                     - Run command in job and terminate if\n" \
"                                     the command fails (exit code != 0).\n" \
"  /V                               - Run verbosely.\n" \
"\n" \
"Example:\n" \
"  jobcontrol create MyJob /LimitJobTime 10 /C \"cmd.exe\"\n" \
"\n" \
"KILL COMMAND\n" \
"------------\n" \
"\n" \
"The \"kill\" command terminates the processes within a job\n" \
"object.  There are no relevant options.\n" \
"\n" \
"Example:\n" \
"  jobcontrol kill MyJob\n" \
"\n"
"QUERY COMMAND\n" \
"-------------\n" \
"\n" \
"Determine if process is within a job already, exit 1 if so, 0 otherwise."
);
}

static void
ErrorReport(char *function)
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

    printf("jobcontrol: %s failed with error %d: %s",
           function, error, message);

    LocalFree(message);
}

static BOOL
ParseInt64(LPCSTR lpszValue, PINT64 pValue)
{
    PCHAR pszStop;

    errno = 0;
    *pValue = _strtoi64(lpszValue, &pszStop, 10);

    // Return no overflow and all characters parsed.
    return errno == 0 && *pszStop == '\0';
}

static BOOL
ParseUInt32(LPCSTR lpszValue, PUINT32 pValue)
{
    PCHAR pszStop;

    errno = 0;
    *pValue = strtoul(lpszValue, &pszStop, 10);

    // Return no overflow and all characters parsed.
    return errno == 0 && *pszStop == '\0';
}

// ----------------------------------------------------------------------------
// Interactivity check

static BOOL IsInteractive()
{
    static int isInteractive = -1;

    if (isInteractive < 0) {
        HANDLE hwinsta;
        if (NULL != (hwinsta = GetProcessWindowStation())) {
            USEROBJECTFLAGS uof;
            DWORD dwLengthNeeded;
            if (GetUserObjectInformation(hwinsta, UOI_FLAGS, &uof,
                                         sizeof(uof), &dwLengthNeeded) == 0) {
                ErrorReport("GetUserObjectInformation");
                ExitProcess((DWORD)-1);
            }
            isInteractive = (uof.dwFlags & WSF_VISIBLE) ? 1 : 0;
            tprintf("Process is interactive: %c\n",
                    isInteractive ? 't' : 'f');
        }
        else {
            ErrorReport("GetProcessWindowStation");
            ExitProcess((DWORD)-1);
        }
    }
    return isInteractive ? TRUE : FALSE;
}

// ----------------------------------------------------------------------------
// Process Set helpers

static PCONTROLLED_PROCESS_SET
AllocateProcessSet(DWORD dwMaxProcesses)
{
    size_t cbBytes = (sizeof(CONTROLLED_PROCESS_SET) +
                      dwMaxProcesses * sizeof(CONTROLLED_PROCESS));
    PCONTROLLED_PROCESS_SET pSet = (PCONTROLLED_PROCESS_SET)malloc(cbBytes);
    if (NULL != pSet) {
        pSet->ProcessCount    = 0;
        pSet->MaxProcessCount = dwMaxProcesses;
        pSet->Processes       = (PCONTROLLED_PROCESS)(pSet + 1);
    }
    return pSet;
}

static void
FreeProcessSet(PCONTROLLED_PROCESS_SET pSet)
{
    free(pSet);
    pSet = NULL;
}

static PCONTROLLED_PROCESS
FindProcessInSet(PCONTROLLED_PROCESS_SET pSet, DWORD dwProcessId)
{
    DWORD i;
    for (i = 0; i < pSet->ProcessCount; i++) {
        if (pSet->Processes[i].ProcessId == dwProcessId) {
            return &pSet->Processes[i];
        }
    }
    return NULL;
}

static void
AddProcessToSet(PCONTROLLED_PROCESS_SET pSet,
                HANDLE                  hThread,
                HANDLE                  hProcess,
                DWORD                   dwProcessId,
                BOOL                    bErrorExitFatal)
{
    PCONTROLLED_PROCESS pProcess;

    assert(FindProcessInSet(pSet, dwProcessId) == NULL);
    assert(pSet->ProcessCount < pSet->MaxProcessCount);

    pProcess = &pSet->Processes[pSet->ProcessCount];
    pProcess->Thread         = hThread;
    pProcess->Process        = hProcess;
    pProcess->ProcessId      = dwProcessId;
    pProcess->ErrorExitFatal = bErrorExitFatal;
    pSet->ProcessCount++;
}

static BOOL
RemoveProcessFromSet(PCONTROLLED_PROCESS_SET pSet, DWORD dwProcessId)
{
    DWORD i;
    for (i = 0; i < pSet->ProcessCount; i++) {
        if (pSet->Processes[i].ProcessId == dwProcessId) {
            tprintf("Removing process %u from process set\n", dwProcessId);
            if (pSet->ProcessCount > 1) {
                // Swap with last element so it's there for inspection
                CONTROLLED_PROCESS tmp = pSet->Processes[i];
                pSet->Processes[i] = pSet->Processes[pSet->ProcessCount - 1];
                pSet->Processes[pSet->ProcessCount - 1] = tmp;
            }
            pSet->ProcessCount--;
            return TRUE;
        }
    }
    return FALSE;
}

// ----------------------------------------------------------------------------

static BOOL
LimitJobUserTime(HANDLE hJob, DWORD dwLimitFlags, LPCSTR lpszValue)
{
    JOBOBJECT_BASIC_LIMIT_INFORMATION limits;
    __int64 timeout;

    ZeroMemory(&limits, sizeof(limits));

    if (ParseInt64(lpszValue, &timeout) == FALSE) {
        fprintf(stdout, "Bad user time limit value.");
        return FALSE;
    }
    tprintf("Limiting job time to %I64d seconds\n", timeout);
    timeout *= 1000 * 1000 * 10; // seconds to W32 kernel ticks
    tprintf("Limiting job time to %I64d ticks\n", timeout);

    if (dwLimitFlags == JOB_OBJECT_LIMIT_JOB_TIME) {
        CopyMemory(&limits.PerJobUserTimeLimit, &timeout, sizeof(timeout));
    }
    else if (dwLimitFlags == JOB_OBJECT_LIMIT_PROCESS_TIME) {
        CopyMemory(&limits.PerProcessUserTimeLimit, &timeout, sizeof(timeout));
    }
    else {
        fprintf(stdout, "Bad time limit target.\n");
        return FALSE;
    }
    limits.LimitFlags = dwLimitFlags;

    if (SetInformationJobObject(hJob, JobObjectBasicLimitInformation,
                                &limits, sizeof(limits)) == 0) {
        ErrorReport("SetInformationJobObject");
        return FALSE;
    }
    ErrorReport("SetInformationJobObject (no error)");

    return TRUE;
}

static BOOL
AddProcessToJob(HANDLE                  hJob,
                LPCSTR                  lpCommandLine,
                PCONTROLLED_PROCESS_SET pSet,
                DWORD                   bErrorExitFatal)
{
    PROCESS_INFORMATION pi;
    STARTUPINFO si;
    DWORD dwCreationFlags;

    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);

    dwCreationFlags = CREATE_SUSPENDED /* | CREATE_BREAKAWAY_FROM_JOB */;
    if (!IsInteractive()) {
        // If non-interactive we are presumably being run by a
        // process and do not want to interact with the desktop.
        // If we attempt to create a window, CreateProcess will
        // die with permission denied.
        dwCreationFlags |= CREATE_NO_WINDOW;
    }

    if (!CreateProcess(NULL, (LPSTR)lpCommandLine, NULL, NULL, FALSE,
                       dwCreationFlags, NULL, NULL, &si, &pi)) {
        fprintf(stdout, "Failed to create process: \"%s\"\n", lpCommandLine);
        ErrorReport("CreateProcess");
        return FALSE;
    }
    else if (!AssignProcessToJobObject(hJob, pi.hProcess)) {
        ErrorReport("AssignProcessToJobObject");
        TerminateProcess(pi.hProcess, (UINT)-1);
        return FALSE;
    }

    AddProcessToSet(pSet, pi.hThread, pi.hProcess, pi.dwProcessId,
                    bErrorExitFatal);

    tprintf("jobcontrol: Adding process (%u): %s\n",
            pi.dwProcessId, lpCommandLine);

    return TRUE;
}

static BOOL
CreateAndAssociateCompletionPort(HANDLE hJob, PHANDLE phIoPort)
{
    JOBOBJECT_ASSOCIATE_COMPLETION_PORT jacp;
    HANDLE hIoPort;
    DWORD  dwKey;

    *phIoPort = INVALID_HANDLE_VALUE;

    if (NULL == (hIoPort = CreateIoCompletionPort(INVALID_HANDLE_VALUE,
                                                  NULL, dwCompletionKey, 1))) {
        ErrorReport("CreateIoCompletionPort");
        return FALSE;
    }

    dwKey = dwCompletionKey;
    jacp.CompletionKey  = (PVOID)dwKey;
    jacp.CompletionPort = hIoPort;
    if (!SetInformationJobObject(hJob,
                                 JobObjectAssociateCompletionPortInformation,
                                 &jacp, sizeof(jacp))) {
        ErrorReport("SetInformationJobObject");
        CloseHandle(hIoPort);
        return FALSE;
    }
    *phIoPort = hIoPort;

    return TRUE;
}

static DWORD WINAPI MonitorJobThreadProc(LPVOID lpParams)
{
    PMONITOR_THREAD_ARGS pJobArgs = (PMONITOR_THREAD_ARGS)lpParams;
    HANDLE               hIoPort  = NULL;
    BOOL                 bStop    = FALSE;
    BOOL                 bFatalError = FALSE;

    time_t nowTime = 0i64;
    time_t endTime = _I64_MAX;

    if (!CreateAndAssociateCompletionPort(pJobArgs->hJob, &hIoPort)) {
        ExitThread((DWORD)-1);
    }

    if (pJobArgs->dwTimeoutSeconds > 0) {
        time(&nowTime);
        endTime = nowTime + pJobArgs->dwTimeoutSeconds;
    }

    tprintf("Watching job (supplied = %u, %I64d, %I64d, timeout = %I64d)\n",
            pJobArgs->dwTimeoutSeconds, endTime, nowTime, endTime - nowTime);

    SetEvent(pJobArgs->hMonitoringStarted);

    while (time(&nowTime) < endTime && !bStop) {
        DWORD        dwBytes     = 0;
        ULONG_PTR    key         = 0;
        LPOVERLAPPED pOverlapped = NULL;
        DWORD        waitMillis  = INFINITE;

        if (endTime - nowTime < INFINITE * 1000i64) {
            waitMillis = (DWORD)((endTime - nowTime) * 1000);
        }

        if (!GetQueuedCompletionStatus(hIoPort, &dwBytes, &key,
                                       &pOverlapped, waitMillis)) {
            continue;
        }
        assert (key == dwCompletionKey);

        switch (dwBytes) {
          case JOB_OBJECT_MSG_END_OF_JOB_TIME:
          case JOB_OBJECT_MSG_END_OF_PROCESS_TIME:
          case JOB_OBJECT_MSG_ACTIVE_PROCESS_LIMIT:
          case JOB_OBJECT_MSG_PROCESS_MEMORY_LIMIT:
          case JOB_OBJECT_MSG_JOB_MEMORY_LIMIT:
            break;
          case JOB_OBJECT_MSG_ACTIVE_PROCESS_ZERO:
            printf("jobcontrol: Requested process all stopped.");
            bStop = TRUE;
            break;
          case JOB_OBJECT_MSG_NEW_PROCESS:
              {
                  DWORD  dwProcessId = (DWORD)pOverlapped;
                  tprintf("Process start (%d)\n", dwProcessId);
              }
              break;
          case JOB_OBJECT_MSG_EXIT_PROCESS:
          case JOB_OBJECT_MSG_ABNORMAL_EXIT_PROCESS:
              {
                  DWORD  dwExitCode  = 0;
                  DWORD  dwProcessId = (DWORD)pOverlapped;
                  PCONTROLLED_PROCESS pProcess =
                      FindProcessInSet(pJobArgs->pSet, dwProcessId);
                  if (NULL != pProcess) {
                      if (!GetExitCodeProcess(pProcess->Process, &dwExitCode)) {
                          ErrorReport("GetExitCodeProcess");
                          fprintf(stdout, "jobcontrol: Unable to get exit code of process in job\n");
                          bStop       = TRUE;
                          bFatalError = TRUE;
                      }
                      else if (dwExitCode != 0 && pProcess->ErrorExitFatal) {
                          bStop       = TRUE;
                          bFatalError = TRUE;
                      }

                      tprintf("jobcontrol: Process %u exited (%u)\n",
                              dwProcessId, dwExitCode);

                      RemoveProcessFromSet(pJobArgs->pSet, dwProcessId);
                      if (pJobArgs->pSet->ProcessCount == 0) {
                          bStop = TRUE;
                      }
                  }
              }
              break;
          default:
            // Should never happen
            printf("jobcontrol: Unknown message type %08x", dwBytes);
            break;
        }
    }

    if (nowTime > endTime) {
        printf("jobcontrol: Timed out\n");
    }

    tprintf("- Watching job (supplied = %u, %I64d, %I64d, timeout = %I64d)\n",
            pJobArgs->dwTimeoutSeconds, endTime, nowTime, endTime - nowTime);


    tprintf("Watch done (fatal error = %d, stop = %d)\n", bFatalError, bStop);

    CloseHandle(hIoPort);

    ExitThread((bFatalError || !bStop) ? (DWORD)-1 : 0);
}

static BOOL
StartJobThreads(PCONTROLLED_PROCESS_SET pSet)
{
    DWORD i;
    for (i = 0; i < pSet->ProcessCount; i++) {
        tprintf("Starting process %d\n", pSet->Processes[i].ProcessId);
        ResumeThread(pSet->Processes[i].Thread);
        pSet->Processes[i].Thread = NULL;
    }
    return TRUE;
}

static void
CleanupJobHandles(PCONTROLLED_PROCESS_SET pSet)
{
    DWORD i;
    PCONTROLLED_PROCESS pProcess = pSet->Processes;
    for (i = 0; i < pSet->MaxProcessCount && pProcess->ProcessId != 0;
         i++, pProcess++) {
        CloseHandle(pProcess->Thread);
        CloseHandle(pProcess->Process);
    }
}

static DWORD
StartJobProcessesAndMonitor(HANDLE                  hJob,
                            PCONTROLLED_PROCESS_SET pSet,
                            DWORD                   dwTimeoutSeconds)
{
    HANDLE              hMonitorThread;
    DWORD               dwMonitorThreadExitCode;
    MONITOR_THREAD_ARGS monitorArgs;

    //
    // Fire up monitoring thread so process can track all activity
    //
    monitorArgs.hJob               = hJob;
    monitorArgs.pSet               = pSet;
    monitorArgs.dwTimeoutSeconds   = dwTimeoutSeconds;
    monitorArgs.hMonitoringStarted = CreateEvent(NULL, TRUE, FALSE, NULL);

    hMonitorThread = CreateThread(NULL, 0, MonitorJobThreadProc,
                                  &monitorArgs, 0, NULL);
    if (NULL == hMonitorThread) {
        CloseHandle(monitorArgs.hMonitoringStarted);
        ErrorReport("CreateThread");
        return (DWORD)-1;
    }

    //
    // Wait for monitoring thread to reach start point
    //
    WaitForSingleObject(monitorArgs.hMonitoringStarted, INFINITE);

    //
    // Resume process threads associated with job
    //
    StartJobThreads(pSet);

    //
    // Wait for monitoring thread to kick the bucket
    //
    WaitForSingleObject(hMonitorThread, INFINITE);

    GetExitCodeThread(hMonitorThread, &dwMonitorThreadExitCode);

    CloseHandle(hMonitorThread);
    CloseHandle(monitorArgs.hMonitoringStarted);

    CleanupJobHandles(pSet);

    return dwMonitorThreadExitCode;
}

static const char * StringSeconds(time_t tElapsed)
{
    static int snBuffer = 0;
    static char rcbBuffer[10][10];
    char *pszBuffer;
    int hours, minutes, seconds;

    snBuffer = (snBuffer + 1) % 10;
    pszBuffer = rcbBuffer[snBuffer];

    seconds = (int)tElapsed;

    hours    = seconds / 3600;
    seconds -= hours * 3600;
    minutes  = seconds / 60;
    seconds -= minutes * 60;

    sprintf(pszBuffer, "%02d:%02d:%02d", hours, minutes, seconds);
    return pszBuffer;
}

static const char * StringTicks(LARGE_INTEGER ticks)
{
    LONGLONG seconds = ticks.QuadPart;
    seconds /= 10000000;

    return StringSeconds((time_t)seconds);
}

static void DisplaySeconds(const char* title, time_t tElapsed)
{
    int hours, minutes, seconds;
    seconds = (int)tElapsed;

    hours    = seconds / 3600;
    seconds -= hours * 3600;
    minutes  = seconds / 60;
    seconds -= minutes * 60;

    printf("%s%02d:%02d:%02d\n", title, hours, minutes, seconds);
}

static void DisplayTicks(const char* title, LARGE_INTEGER ticks)
{
    LONGLONG seconds = ticks.QuadPart;
    seconds /= 10000000;

    DisplaySeconds(title, (time_t)seconds);
}

static void ShowBasicAccountingInformation(HANDLE hJob,
                                           time_t tStart,
                                           time_t tEnd)
{
    JOBOBJECT_BASIC_ACCOUNTING_INFORMATION jbai;

    if (QueryInformationJobObject(hJob,
                                  JobObjectBasicAccountingInformation,
                                  &jbai,
                                  sizeof(jbai),
                                  NULL)) {
        printf("Wall time elapsed: %s (User: %s, Kernel: %s)\n",
               StringSeconds(tEnd - tStart),
               StringTicks(jbai.TotalUserTime),
               StringTicks(jbai.TotalKernelTime));
        printf("Total processes:   %8u\n", jbai.TotalProcesses);
        printf("Page faults:       %8u\n", jbai.TotalPageFaultCount);
    }
}

// ----------------------------------------------------------------------------
// User Commands

static int
CreateJobAndRun(int argc, LPCSTR argv[])
{
    BOOL                    bSuccess             = FALSE;
    BOOL                    bShowBasicAccounting = FALSE;
    DWORD                   dwMaxJobTime         = 0;
    DWORD                   dwResult             = 0;
    PCONTROLLED_PROCESS_SET pSet                 = NULL;
    if (argc == 0) {
        fprintf(stdout, "Missing <jobname> and options\n");
        return -1;
    }

    tprintf("Creating job %s\n", argv[0]);

    if (NULL == (ghJob = CreateJobObject(NULL, argv[0]))) {
        ErrorReport("CreateJobObject");
        return -1;
    }

    argv++;
    argc--;

    pSet = AllocateProcessSet(argc); // overallocation

    bSuccess = TRUE;
    while (argc != 0 && bSuccess) {
        if (argc < 2) {
            fprintf(stdout, "Unexpected end of arguments\n");
            bSuccess = FALSE;
        }
        else if (!_strcmpi("/LimitJobUserTime", argv[0])) {
            bSuccess = LimitJobUserTime(ghJob, JOB_OBJECT_LIMIT_JOB_TIME,
                                        argv[1]);
        }
        else if (!_strcmpi("/LimitProcessUserTime", argv[0])) {
            bSuccess = LimitJobUserTime(ghJob,JOB_OBJECT_LIMIT_PROCESS_TIME,
                                        argv[1]);
        }
        else if (!_strcmpi("/LimitJobTime", argv[0])) {
            bSuccess = ParseUInt32(argv[1], (PUINT32)&dwMaxJobTime);
        }
        else if (!_strcmpi("/B", argv[0])) {
            bShowBasicAccounting = TRUE;
        }
        else if (!_strcmpi("/C", argv[0])) {
            bSuccess = AddProcessToJob(ghJob, argv[1], pSet, FALSE);
            argv += 1;
            argc -= 1;
        }
        else if (!_strcmpi("/T", argv[0])) {
            bSuccess = AddProcessToJob(ghJob, argv[1], pSet, TRUE);
            argv += 1;
            argc -= 1;
        }
        else if (!_strcmpi("/V", argv[0])) {
            gbVerbose = TRUE;
        }
        else {
            fprintf(stdout, "Unknown option \"%s\".\n", argv[0]);
            bSuccess = FALSE;
        }
        argv += 1;
        argc -= 1;
    }

    dwResult = (DWORD)-1;
    if (bSuccess && pSet->ProcessCount != 0) {
        time_t tStart;
        time_t tEnd;

        time(&tStart);
        dwResult = StartJobProcessesAndMonitor(ghJob, pSet, dwMaxJobTime);
        time(&tEnd);

        if (bShowBasicAccounting) {
            ShowBasicAccountingInformation(ghJob, tStart, tEnd);
        }
    }

    FreeProcessSet(pSet);
    TerminateJobObject(ghJob, (UINT)-1);


    CloseHandle(ghJob);

    return (int)dwResult;
}

static int
KillJob(int argc, LPCSTR argv[])
{
    HANDLE hJob;

    if (argc == 0) {
        fprintf(stdout, "Missing <jobname> argument\n");
        return -1;
    }
    else if (argc > 1) {
        fprintf(stdout, "Unknown arguments passed to kill request\n");
        Usage();
        return -1;
    }
    else if (NULL == (hJob = CreateJobObject(NULL, argv[0]))) {
        ErrorReport("CreateJobObject");
        return -1;
    }
    else if (0 == TerminateJobObject(hJob, (UINT)-1)) {
        ErrorReport("TerminateJobObject");
        return -1;
    }
    tprintf("Terminated %s", argv[0]);

    return 0;
}

// ----------------------------------------------------------------------------
// Main

int main(int argc, const char* argv[])
{
    BOOL bInJob;
    if (!IsProcessInJob(GetCurrentProcess(), NULL, &bInJob)) {
        ErrorReport("IsProcessInJob");
        return -1;
    }

    if (argc == 2) {
        // User is querying whether already in a job
        if (_strcmpi(argv[1], "query") == 0) {
            return bInJob ? 1 : 0;
        }
    }
    else if (argc >= 3) {
        if (_strcmpi(argv[1], "create") == 0) {
            // Can't create a job inside a job
            if (bInJob) {
                fprintf(stdout, "Warning: jobcontrol launched inside a job\n");
            }
            SetConsoleCtrlHandler(CtrlHandler, TRUE);
            return CreateJobAndRun(argc - 2, argv + 2);
        }
        else if (_strcmpi(argv[1], "kill") == 0) {
            SetConsoleCtrlHandler(CtrlHandler, TRUE);
            return KillJob(argc - 2, argv + 2);
        }
    }
    Usage();
    return -1;
}
