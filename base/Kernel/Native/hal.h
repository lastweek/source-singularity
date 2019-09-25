///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   hal.h
//
//  Note:
//

#pragma once

#define UNICODE
#define _UNICODE

/////////////////////////////////////////// Core types used by runtime system.
//

typedef __wchar_t           bartok_char;

typedef char                int8;
typedef short               int16;
typedef int                 int32;
typedef __int64             int64;

typedef unsigned char       uint8;
typedef unsigned short      uint16;
typedef unsigned int        uint32;
typedef unsigned __int64    uint64;

typedef float               float32;
typedef double              float64;

#if defined(PTR_SIZE_32)
typedef int                 intptr;
typedef unsigned int        uintptr;
#else
typedef __int64             intptr;
typedef unsigned __int64    uintptr;
#endif

struct uintPtr
{
    uintptr value;
};

struct intPtr
{
    intptr value;
};

typedef struct uintPtr *UIntPtr;
typedef struct intPtr *IntPtr;

/////////////////////////////////////////////////////////////// Static Assert.
//
// Compile-time (not run-time) assertion. Code will not compile if
// expr is false. Note: there is no non-debug version of this; we
// want this for all builds. The compiler optimizes the code away.
//
template <bool x> struct STATIC_ASSERT_FAILURE;
template <> struct STATIC_ASSERT_FAILURE<true> { };
template <int x> struct static_assert_test { };

#define STATIC_CAT_INNER(x,y) x##y
#define STATIC_CAT(x,y) STATIC_CAT_INNER(x,y)
#define STATIC_ASSERT(condition) \
   typedef static_assert_test< \
      sizeof(STATIC_ASSERT_FAILURE<(bool)(condition)>)> \
         STATIC_CAT(__static_assert_typedef_, __COUNTER__)

//////////////////////////////////////////////////////////////////////////////
//
#define OFFSETOF(s,m)   ((uintptr)&(((s *)0)->m))
#define ARRAYOF(a)      (sizeof(a)/sizeof(a[0]))

//////////////////////////////////////////////////////////////////////////////
//
typedef signed int INT;
typedef signed char INT8;
typedef signed short INT16;
typedef signed long INT32;
typedef signed __int64 INT64;
typedef unsigned int UINT;
typedef unsigned char UINT8;
typedef unsigned short UINT16;
typedef unsigned long UINT32;
typedef unsigned __int64 UINT64;

typedef wchar_t WCHAR;
typedef unsigned char UCHAR;

typedef void *PVOID;
typedef uintptr ULONG_PTR;
typedef uint64 ULARGEST;
typedef int64 LARGEST;

typedef int BOOL;

typedef struct
{
    UINT64  _lo;
    UINT64  _hi;
} UINT128;

#define NULL 0

extern "C" {
    extern UINT32 ProcessorContextOffset;
};


#if SINGULARITY_KERNEL

#ifndef _VA_LIST_DEFINED
typedef char *va_list;
#define _VA_LIST_DEFINED

#if PTR_SIZE_32

#define _INTSIZEOF(n)    ( (sizeof(n) + sizeof(int) - 1) & ~(sizeof(int) - 1) )
#define va_start(ap,v) ap = (va_list)&v + _INTSIZEOF(v)
#define va_arg(ap,t) ( *(t *)((ap += _INTSIZEOF(t)) - _INTSIZEOF(t)) )
#define va_end(ap) ap = (va_list)0

#else // PTR_SIZE_64

// the following extern "C" code is needed to ensure the
// compiler intrinsic IV_VA_START is invoked.
extern "C" void __cdecl __va_start(va_list *, ...);

#define va_dcl          va_list va_alist;
#define va_start(ap,x)   ( __va_start(&ap, x) )
#define va_arg(ap, t)   \
    ( ( sizeof(t) > sizeof(__int64) || ( sizeof(t) & (sizeof(t) - 1) ) != 0 ) \
        ? **(t **)( ( ap += sizeof(__int64) ) - sizeof(__int64) ) \
        :  *(t  *)( ( ap += sizeof(__int64) ) - sizeof(__int64) ) )
#define va_end(ap)      ( ap = (va_list)0 )

#endif // PTR_SIZE_64
#endif // _VA_LIST_DEFINED

#ifndef MAX_CPU
#define MAX_CPU 1
#endif  // MAX_CPU

#endif // SINGULARITY_KERNEL

//////////////////////////////////////////////////////////////////////////////
//
#if SINGULARITY_PROCESS

//////////////////////////////////////////////////////////////////////////////
//
struct Struct_System_ObjectHeader
{
    int32  syncBlockValue;
};

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
    sizeof(v)/sizeof(wchar_t) - 1, \
    v \
}

#endif // SINGULARITY_PROCESS

//////////////////////////////////////////////////////////////////////////////

#pragma warning(disable: 4201)  // Allow nameless struct/union
#pragma warning(disable: 4127)  // 4127: warning about constant conditional

#define EXCEPTION_ACCESS_VIOLATION      1
#define EXCEPTION_CONTINUE_EXECUTION    2
#define EXCEPTION_CONTINUE_SEARCH       3
#define EXCEPTION_FLT_DIVIDE_BY_ZERO    4
#define EXCEPTION_INT_DIVIDE_BY_ZERO    5
#define EXCEPTION_INT_OVERFLOW          6
#define EXCEPTION_STACK_OVERFLOW        7

//////////////////////////////////////////////////////////////////////////////

// Used to pass various data through "int 29"
struct KdDebugTrapData
{
    enum Tag
    {
        FIRST_CHANCE_EXCEPTION,
        LOADED_BINARY,
        UNLOADED_BINARY
    } tag;
    union
    {
        struct
        {
            uintptr throwAddr;
        } firstChanceException;
        struct
        {
            UIntPtr baseAddress;
            UIntPtr bytes;
            UIntPtr name;
            uint32 checksum;
            uint32 timestamp;
            bool silent;
            bool ret;
        } loadedBinary;
        struct
        {
            UIntPtr baseAddress;
            bool silent;
            bool ret;
        } unloadedBinary;
    };
};

//////////////////////////////////////////////////////////////////////////////
//
#pragma warning(disable: 4103)
#include "halclass.h"

//////////////////////////////////////////////////////////////////////////////
//
struct ClassVector : Class_System_Object
{
    uint32          length;
};

struct ClassVector_uint8 : ClassVector
{
    static struct Class_System_VTable ClassVector_uint8::_vtable;

    uint8           values[1];
};

struct ClassVector_ClassVector_uint8 : ClassVector
{
    static struct Class_System_VTable ClassVector_ClassVector_uint8::_vtable;

    ClassVector_uint8 * values[1];
};

struct ClassVector_bartok_char : ClassVector
{
    static struct Class_System_VTable ClassVector_bartok_char::_vtable;

    bartok_char     values[1];
};

////////////////////////////////////////////////////////////// Dynamic Assert.
//
#if DEBUG
#if SINGULARITY_KERNEL
extern void fail_assert(const char *expr);
#define __fail_assert(expr, file, line) fail_assert("assert(" #expr ") failed at " file ":" #line)
#define Assert(expr) { if (!(expr)) { __fail_assert(expr, __FILE__, __LINE__); } }
#elif SINGULARITY_PROCESS
extern void fail_assert(Class_System_String *message);
#define Assert(expr) { if (!(expr)) { static MAKE_STRING(msg, L"assert(" L#expr L") failed"); fail_assert(&msg.string); } }
#endif
#else //DEBUG
#define Assert(expr) { 0; }
#endif//DEBUG

//////////////////////////////////////////////////////////////////////////////

int printf(const char *pszFmt, ...);

void Cls(void);

#if SINGULARITY_KERNEL
void ProcessorInitialize(Class_Microsoft_Singularity_Hal_Cpu* processor);
#endif
void KdNotifyTrap(KdDebugTrapData *data);
void KdNotifyException(Class_System_Exception *exception, unsigned int throwAddr);

//////////////////////////////////////////////////////////////////////////////

#define arrayof(a)      (sizeof(a)/sizeof(a[0]))
#define offsetof(s,m)   (size_t)&(((s *)0)->m)

#pragma warning(disable: 4100)  // allow unreferenced formal parameters

// Include standard compiler intrinsics
#include "intrinsics.h"

////////////////////////////////////////////////////////////////// End of File.
