// ----------------------------------------------------------------------------
//
// Program: MutexWrap
//
// Purpose: This wrapper opens a named mutex and then runs a
//          user specified process holding the mutex.  The mutex is
//          relinquished when the program stops executing.
//
// (C) Microsoft Corporation
//
// ----------------------------------------------------------------------------

#define _WIN32_WINNT 0x0500

#include <winlean.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define ACQUIRE_TIMEOUT 1000
#define HOLD_TIMEOUT    1001

// #define VERBOSE

#ifdef VERBOSE
#define tprintf(x,...) printf(x, __VA_ARGS__)
#else
#define tprintf(x,...)
#endif

static HANDLE g_hMutex = NULL;

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

    if (NULL != g_hMutex) {
        ReleaseMutex(g_hMutex); // May not be acquired
        CloseHandle(g_hMutex);
    }

    ExitProcess((UINT)-2);
}

static BOOL
ParseDWord(LPCSTR lpszValue, PDWORD pValue)
{
    PCHAR pszStop;

    errno = 0;
    *pValue = strtoul(lpszValue, &pszStop, 10);

    // Return no overflow and all characters parsed.
    return errno == 0 && *pszStop == '\0';
}

static void Usage()
{
    printf(
"Usage:\n" \
"mutexwrap [options] <mutexname> <command>\n\n" \
"Runs <command> holding named mutex.  Waits up to specifiable timeout to \n" \
"acquire the mutex, and potentially timeouts command.\n\n" \
"The available options are:\n" \
"  /WaitTime <seconds>    - Set limit on time waited to acquire mutex.\n" \
"  /HoldTime <seconds>    - Set limit on time process runs for.\n" \
"The process returns 0 on success, %d on mutex acquisition failure, %d on\n" \
"process run time exceeded.\n\n" \
"Example:\n  mutexwrap /w 10 /h 10 MyMutex \"sleep.exe 500\"\n"
,
ACQUIRE_TIMEOUT, HOLD_TIMEOUT
);
}

static void
ErrorReport(char *function)
{
    VOID *message;
    DWORD error = GetLastError();

    FormatMessage(FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM,
                  NULL, error,
                  MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),
                  (LPTSTR) &message, 0, NULL);

    fprintf(stderr, "%s failed with error %d: %s\n", function, error, message);

    LocalFree(message);
}

static DWORD
SecondsToMillis(DWORD dwSeconds)
{
    if (dwSeconds > INFINITE / 1000) {
        return INFINITE;
    }
    return dwSeconds * 1000;
}

static DWORD RunProcess(LPCSTR lpCommandLine, DWORD dwHoldSeconds)
{
    DWORD dwExitCode   = HOLD_TIMEOUT;
    DWORD dwHoldMillis = INFINITE;

    PROCESS_INFORMATION pi;
    STARTUPINFO         si;

    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);

    if (!CreateProcess(NULL, (LPSTR)lpCommandLine, NULL, NULL, FALSE,
                       0, NULL, NULL, &si, &pi)) {
        fprintf(stderr, "mutexwrap: Failed to create process: \"%s\"\n",
                lpCommandLine);
        ErrorReport("CreateProcess");
        return (DWORD)-1;
    }

    dwHoldMillis = SecondsToMillis(dwHoldSeconds);
    if (WaitForSingleObject(pi.hProcess, dwHoldMillis) == WAIT_OBJECT_0) {
        GetExitCodeProcess(pi.hProcess, &dwExitCode);
    }
    else {
        fprintf(stderr,
                "mutexwrap: timed out holding mutex with program running.");
        TerminateProcess(pi.hProcess, (DWORD)-1);
    }

    CloseHandle(pi.hProcess);
    CloseHandle(pi.hThread);

    return dwExitCode;
}

static BOOL
AcquireMutex(HANDLE hMutex, DWORD dwTimeoutSeconds)
{
    time_t nowTime;
    time_t endTime;

    time(&endTime);
    endTime += dwTimeoutSeconds;

    while (time(&nowTime) < endTime) {
        DWORD dwWaitMillis = INFINITE;
        if (endTime - nowTime < INFINITE * 1000i64) {
            dwWaitMillis = (DWORD)((endTime - nowTime) * 1000);
        }
        if (WaitForSingleObject(hMutex, dwWaitMillis) == WAIT_OBJECT_0) {
            return TRUE;
        }
    }
    fprintf(stderr, "mutexwrap: timed out acquiring mutex.\n");
    return FALSE;
}

int main(int argc, LPCSTR argv[])
{
    DWORD dwWaitSeconds = INFINITE;
    DWORD dwHoldSeconds = INFINITE;
    DWORD dwExitCode    = 0;

    argv++;
    argc--;

    while (argc > 0 && (argv[0][0] == '/' || argv[0][0] == '-')) {
        if (tolower(argv[0][1]) == 'w' && argc > 2) {
            if (!ParseDWord(argv[1], &dwWaitSeconds)) {
                fprintf(stderr, "mutexwrap: Invalid wait time.\n");
                return -1;
            }
        }
        else if (tolower(argv[0][1]) == 'h' && argc > 2) {
            if (!ParseDWord(argv[1], &dwHoldSeconds)) {
                fprintf(stderr, "mutexwrap: Invalid hold time.\n");
                return -1;
            }
        }
        else {
            Usage();
            return -1;
        }
        argv += 2;
        argc -= 2;
    }

    tprintf("Wait time %us, Hold time %us\n", dwWaitSeconds, dwHoldSeconds);

    if (argc != 2) {
        Usage();
        return -1;
    }

    SetConsoleCtrlHandler(CtrlHandler, TRUE);

    if (NULL == (g_hMutex = CreateMutex(NULL, FALSE, argv[0]))) {
        fprintf(stderr, "mutexwrap: failed to create mutex.\n");
        ErrorReport("CreateMutex");
        return -1;
    }

    argc--;
    argv++;

    if (AcquireMutex(g_hMutex, dwWaitSeconds)) {
        dwExitCode = RunProcess(argv[0], dwHoldSeconds);
        ReleaseMutex(g_hMutex);
    }
    else {
        dwExitCode = ACQUIRE_TIMEOUT;
    }

    CloseHandle(g_hMutex);
    return dwExitCode;
}
