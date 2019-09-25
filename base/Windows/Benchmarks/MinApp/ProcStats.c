#include <winlean.h>
#include <psapi.h>
#include <stdio.h>

void Dump(PPROCESS_MEMORY_COUNTERS pcounters) {

    printf("PeakWorkingSetSize: %d\n", pcounters->PeakWorkingSetSize);
    printf("WorkingSetSize: %d\n", pcounters->WorkingSetSize);
    printf("QuotaPeakPagedPoolUsage: %d\n",
           pcounters->QuotaPeakPagedPoolUsage);
    printf("QuotaPagedPoolUsage: %d\n", pcounters->QuotaPagedPoolUsage);
    printf("QuotaPeakNonPagedPoolUsage: %d\n",
           pcounters->QuotaPeakNonPagedPoolUsage);
    printf("QuotaNonPagedPoolUsage: %d\n", pcounters->QuotaNonPagedPoolUsage);
    printf("PagefileUsage: %d\n", pcounters->PagefileUsage);
    printf("PeakPagefileUsage: %d\n", pcounters->PeakPagefileUsage);
}


void main(int argc, char* argv[])
{
    STARTUPINFO si;
    PROCESS_INFORMATION pi;
    PROCESS_MEMORY_COUNTERS counters;
    BOOL success;

    if (argc != 2) {
        printf("usage: procstats <exe to be measured>\n");
        exit(1);
    }

    ZeroMemory(&si, sizeof(si));
    si.cb = sizeof(si);
    ZeroMemory(&pi, sizeof(pi));

    //
    // Start the child process.
    //
    if (!CreateProcess(NULL,     // No module name (use command line).
                       argv[1],  // Command line.
                       NULL,     // Process handle not inheritable.
                       NULL,     // Thread handle not inheritable.
                        FALSE,   // Set handle inheritance to FALSE.
                       0,        // No creation flags.
                       NULL,     // Use parent's environment block.
                       NULL,     // Use parent's starting directory.
                       &si,      // Pointer to STARTUPINFO structure.
                       &pi)      // Pointer to PROCESS_INFORMATION structure.
    )
    {
        printf( "CreateProcess failed (%d).\n", GetLastError() );
        return;
    }

    // Make sure child has had a chance to initialize.
    Sleep(2000);

    success = GetProcessMemoryInfo(pi.hProcess, &counters,
                                   sizeof(PROCESS_MEMORY_COUNTERS));
    Dump(&counters);

    // Kill process.
    TerminateProcess(pi.hProcess, 0);

    printf("done.\n");
    // Close process and thread handles.
}
