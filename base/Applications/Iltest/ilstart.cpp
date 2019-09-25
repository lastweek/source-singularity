//////////////////////////////////////////////////////////////////////////////
//
//  ilstart.cpp - Singularity Hardware Abstraction Layer
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

//////////////////////////////////////////////////////////////////////////////
//
struct Class_Microsoft_Singularity_Iltest
{
    static int g_Main();
    static int g_ThreadMain(int threadIndex);
};

extern "C" void __cdecl _throwDispatcherExplicitAddrAfter()
{
    // ecx = exception
    // dex = throw addr
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('E');
}

extern "C" int32 __fastcall IlStart(int32 threadIndex)
{
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('-');
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('I');
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print('\n');
    if (threadIndex == -1) {
        return Class_Microsoft_Singularity_Iltest::g_Main();
    }
    else {
        return Class_Microsoft_Singularity_Iltest::g_ThreadMain(threadIndex);
    }
}

extern "C" void __cdecl _pushStackMark()
{
}

extern "C" void __cdecl _popStackMark()
{
}
