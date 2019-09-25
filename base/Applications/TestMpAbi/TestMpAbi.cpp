//////////////////////////////////////////////////////////////////////////////
//
//  TestMpAbi.cpp
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
typedef unsigned char       byte;

struct Struct_System_DateTime {char data[8];};

struct Struct_Microsoft_Singularity_V1_Services_ProcessService
{
    static int g_HelloProcessABI(int, int);
    static unsigned __int64 g_TestAbiCallOne(unsigned __int64);
    static int g_TestAbiCallTwo(unsigned int, wchar_t *);
    static wchar_t * g_TestAbiCallThree(int, int *, unsigned char);
    static struct Struct_System_DateTime g_GetUtcTime();
};


extern "C" int32 __fastcall entry(int32 threadIndex)
{
    //Struct_Microsoft_Singularity_V1_Services_ProcessService::g_GetUtcTime();

    int a = Struct_Microsoft_Singularity_V1_Services_ProcessService::g_HelloProcessABI(3, 11);
    int b = Struct_Microsoft_Singularity_V1_Services_ProcessService::g_HelloProcessABI(a, 7);
    int c = Struct_Microsoft_Singularity_V1_Services_ProcessService::g_HelloProcessABI(b, a);

    uint64 a1= 33;
    uint64 r1 = Struct_Microsoft_Singularity_V1_Services_ProcessService::g_TestAbiCallOne(a1);

    uint64 r5 = Struct_Microsoft_Singularity_V1_Services_ProcessService::g_TestAbiCallOne(r1);

    wchar_t x1 = 'a';
    wchar_t *b2 =  &x1;
    uint32 a2 = 10;
    int r2 = Struct_Microsoft_Singularity_V1_Services_ProcessService::g_TestAbiCallTwo(a2, b2);


    int a3 = 44;
    int *b3 = & a3;
    byte c3 = 1;
    wchar_t *r3 = Struct_Microsoft_Singularity_V1_Services_ProcessService::g_TestAbiCallThree(a3, b3, c3);

    Struct_Microsoft_Singularity_V1_Services_ProcessService::g_HelloProcessABI(r2, (int)r3);


    return 0;
}
