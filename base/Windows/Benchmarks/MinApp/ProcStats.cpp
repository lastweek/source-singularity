// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

// ProcStats.cpp : Defines the entry point for the console application.
//
//#include <stdafx.h>
#include <iostream>
#include <windows.h>
#include <psapi.h>
#include <stdio.h>

void Dump(PPROCESS_MEMORY_COUNTERS pcounters) {
    std::cout << "PeakWorkingSetSize:" << pcounters->PeakWorkingSetSize << "\n";
    std::cout << "WorkingSetSize:" << pcounters->WorkingSetSize << "\n";
    std::cout << "QuotaPeakPagedPoolUsage:" << pcounters->QuotaPeakPagedPoolUsage <<"\n";
    std::cout << "QuotaPagedPoolUsage:" << pcounters->QuotaPagedPoolUsage << "\n";
    std::cout << "QuotaPeakNonPagedPoolUsage:" << pcounters->QuotaPeakNonPagedPoolUsage << "\n";
    std::cout << "QuotaNonPagedPoolUsage:" << pcounters->QuotaNonPagedPoolUsage << "\n";
    std::cout << "PagefileUsage:" << pcounters->PagefileUsage << "\n";
    std::cout << "PeakPagefileUsage:" << pcounters->PeakPagefileUsage<< "\n";
}

void main( int argc, char* argv[])
{
  if( argc != 2) {
    printf("usage: procstats <exe to be measured>\n");
    exit(1);
  }
    STARTUPINFO si;
    PROCESS_INFORMATION pi;

    ZeroMemory( &si, sizeof(si) );
    si.cb = sizeof(si);
    ZeroMemory( &pi, sizeof(pi) );

    // Start the child process. 
    if( !CreateProcess( NULL,   // No module name (use command line). 
        argv[1], // Command line. 
        NULL,             // Process handle not inheritable. 
        NULL,             // Thread handle not inheritable. 
        FALSE,            // Set handle inheritance to FALSE. 
        0,                // No creation flags. 
        NULL,             // Use parent's environment block. 
        NULL,             // Use parent's starting directory. 
        &si,              // Pointer to STARTUPINFO structure.
        &pi )             // Pointer to PROCESS_INFORMATION structure.
    ) 
    {
        printf( "CreateProcess failed (%d).\n", GetLastError() );
        return;
    }


    
   
    PROCESS_MEMORY_COUNTERS counters;
    BOOL success = GetProcessMemoryInfo(pi.hProcess, &counters, sizeof(PROCESS_MEMORY_COUNTERS));
    Dump(&counters);

    // Kill process.
    TerminateProcess(pi.hProcess, 0);

    printf("done.\n");
    // Close process and thread handles. 
}
