#include <winlean.h>
#include <stdio.h>

#define GetCycleCount() __rdtsc()
ULONG64
__rdtsc(VOID);
#pragma intrinsic(__rdtsc)

int __cdecl
main()
{
    ULONG64 n = GetCycleCount();

    int r = -1;
    FILE *f = fopen("result.txt", "w");
    if (f != NULL)
    {
        //
        // File format is tied to CreateProcess.c - do not
        // change here without updating there
        // 
        r = fprintf(f, "child start at:\n%llu\n", n);
        fclose(f);
    }

    return r;
}
