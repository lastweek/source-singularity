//////////////////////////////////////////////////////////////////////////////
//
//  testpe.cpp - Singularity Hardware Abstraction Layer
//
//  Copyright Microsoft Corporation.
//

typedef unsigned short      bartok_char;
typedef signed short        int16;
typedef signed int          int32;
typedef __int64             int64;
typedef unsigned char       uint8;
typedef unsigned short      uint16;
typedef unsigned int        uint32;
typedef unsigned __int64    uint64;

struct Struct_System_ObjectHeader
{
    int32  syncBlockValue;
};

struct Class_System_Object
{
    void * f_vtable;
};

struct Class_System_VTable : Class_System_Object
{
};

struct Struct_Microsoft_Singularity_V1_Services_DebugService
{
    static void g_Break();
    static void g_Print(bool);
    static void g_Print(bartok_char);
    static void g_Print(int32);
    static void g_Print(int64);
    static void g_Print(uint32);
    static void g_Print(uint64);
    static void g_Print(uint8);
};

struct Struct_Microsoft_Singularity_V1_Services_ProcessService
{
    static void g_Waypoint(int32);
};

//////////////////////////////////////////////////////////////////////////////
//
uint8 __fastcall test8()
{
    return 0;
}

uint16 __fastcall test16()
{
    return 0;
}

uint32 __fastcall test32()
{
    return 0;
}

uint64 __fastcall test64()
{
    return 0;
}

struct Struct_Microsoft_Singularity_V1_Services_StackService
{
    static void g_GetUnlinkStackRange(uint64 *unlinkBegin, uint64 *unlinkLimit);
    static void g_WalkStack();
};

extern "C" int32 __fastcall entry(int32 threadIndex)
{
    if (threadIndex == -1) {
#if MAXIMUM
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('-');
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('H');

        uint64 unlinkBegin = 0;
        uint64 unlinkLimit = 0;

        Struct_Microsoft_Singularity_V1_Services_StackService::g_GetUnlinkStackRange
            (&unlinkBegin, &unlinkLimit);
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(unlinkBegin);
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(' ');
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(unlinkLimit);
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('\n');

        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('-');
        Struct_Microsoft_Singularity_V1_Services_StackService::g_WalkStack();
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('-');
#else
        Struct_Microsoft_Singularity_V1_Services_ProcessService::g_Waypoint(999);
#endif
    }
    else {
#if MAXIMUM
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('T');
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(threadIndex);
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('\n');
#else
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('T');
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(threadIndex);
        Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('\n');
#endif
    }
    return 0;
}
