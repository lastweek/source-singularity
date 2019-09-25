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

struct Class_System_String : public Class_System_Object
{
    static int32 _vtable;

    int32 f_arrayLength;
    int32 f_stringLength;
    bartok_char chars[1];
};

struct Struct_Microsoft_Singularity_V1_Services_DebugService
{
    static void g_Break();
    static void g_Print(bool);
    static void g_Print(bartok_char);
    static void g_Print(Class_System_String *);
    static void g_Print(int32);
    static void g_Print(int64);
    static void g_Print(uint32);
    static void g_Print(uint64);
    static void g_Print(uint8);
};

struct ClassVector_Class_System_String : Class_System_Object
{
    int32 length;
    Class_System_String * strings[1];
};

//////////////////////////////////////////////////////////////////////////////
//
int32 Class_System_String::_vtable = 0;

#define MAKE_STRING(s,v) \
struct _##s \
{ \
    Struct_System_ObjectHeader header; \
    union \
    { \
        struct \
        { \
            Class_System_VTable * vable; \
            int32 arrayLength; \
            int32 stringLength; \
            wchar_t chars[sizeof(v)]; \
        }; \
        Class_System_String string; \
    }; \
} s = { \
    {}, \
    (Class_System_VTable *)&Class_System_String::_vtable, \
    sizeof(v), \
    sizeof(v) - 1, \
    L##v \
}

static MAKE_STRING(sHelloWorld, "Hello World!\n");
static MAKE_STRING(sExceptionThrown, "Exception Thrown!\n");
static MAKE_STRING(sLine, "..................................................\n");

//////////////////////////////////////////////////////////////////////////////
//
struct Class_Microsoft_Singularity_Nulltest
{
    static int g_Main();
    static int g_ThreadMain(int threadIndex);
};

extern "C" void __cdecl _throwDispatcherExplicitAddrAfter()
{
    // ecx = exception
    // dex = throw addr
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(&sExceptionThrown.string);
}

extern "C" int32 __fastcall IlStart(int32 threadIndex)
{
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(&sLine.string);
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(&sHelloWorld.string);
    Struct_Microsoft_Singularity_V1_Services_DebugService::g_Print(&sLine.string);
    if (threadIndex == -1) {
        return Class_Microsoft_Singularity_Nulltest::g_Main();
    }
    else {
        return Class_Microsoft_Singularity_Nulltest::g_ThreadMain(threadIndex);
    }
}

extern "C" void __cdecl _pushStackMark()
{
}

extern "C" void __cdecl _popStackMark()
{
}
