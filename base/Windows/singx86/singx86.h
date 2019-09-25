/////////////////////////////////////////////////////////////////////////////
//
//  singx86.h - Singularity Debugger Extension common Header.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
//  For more information, see http://ddkslingshot/webs/debugexw/
//

#pragma warning(disable:4201) // Enable nameless structs and unions.

#include <winlean.h>
#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <string.h>

//
// Define KDEXT_64BIT to make all wdbgexts APIs recognize 64 bit addresses
// It is recommended for extensions to use 64 bit headers from wdbgexts so
// the extensions could support 64 bit targets.
//
// #define KDEXT_64BIT
// #include <wdbgexts.h>
#include <dbgeng.h>

//////////////////////////////////////////////////////////////////////////////
//
// Load the Singularity types exported by halclass.h
//

#define arrayof(a)      (sizeof(a)/sizeof(a[0]))

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

//
//  X64 context definitions
//

typedef struct _X64_M128 {
    ULONGLONG Low;
    LONGLONG High;
} X64_M128, *PX64_M128;

typedef struct _X64_XMM_SAVE_AREA64 {
    USHORT ControlWord;
    USHORT StatusWord;
    UCHAR TagWord;
    UCHAR Reserved1;
    USHORT ErrorOpcode;

    ULONG64 ErrorOffset;
    ULONG64 DataOffset;
    ULONG MxCsr;
    ULONG MxCsr_Mask;

    X64_M128 FloatRegisters[8];
    X64_M128 XmmRegisters[16];
    UCHAR Reserved4[96];
} X64_XMM_SAVE_AREA64, *PX64_XMM_SAVE_AREA64;


typedef struct _X64_CONTEXT {

    //
    // Register parameter home addresses.
    //

    ULONG64 P1Home;
    ULONG64 P2Home;
    ULONG64 P3Home;
    ULONG64 P4Home;
    ULONG64 P5Home;
    ULONG64 P6Home;

    //
    // Control flags.
    //

    ULONG ContextFlags;
    ULONG MxCsr;

    //
    // Segment Registers and processor flags.
    //

    USHORT SegCs;
    USHORT SegDs;
    USHORT SegEs;
    USHORT SegFs;
    USHORT SegGs;
    USHORT SegSs;
    ULONG EFlags;

    //
    // Debug registers
    //

    ULONG64 Dr0;
    ULONG64 Dr1;
    ULONG64 Dr2;
    ULONG64 Dr3;
    ULONG64 Dr6;
    ULONG64 Dr7;

    //
    // Integer registers.
    //

    ULONG64 Rax;
    ULONG64 Rcx;
    ULONG64 Rdx;
    ULONG64 Rbx;
    ULONG64 Rsp;
    ULONG64 Rbp;
    ULONG64 Rsi;
    ULONG64 Rdi;
    ULONG64 R8;
    ULONG64 R9;
    ULONG64 R10;
    ULONG64 R11;
    ULONG64 R12;
    ULONG64 R13;
    ULONG64 R14;
    ULONG64 R15;

    //
    // Program counter.
    //

    ULONG64 Rip;

    //
    // Floating point state.
    //

    union {
        X64_XMM_SAVE_AREA64 FltSave;
        struct {
            X64_M128 Header[2];
            X64_M128 Legacy[8];
            X64_M128 Xmm0;
            X64_M128 Xmm1;
            X64_M128 Xmm2;
            X64_M128 Xmm3;
            X64_M128 Xmm4;
            X64_M128 Xmm5;
            X64_M128 Xmm6;
            X64_M128 Xmm7;
            X64_M128 Xmm8;
            X64_M128 Xmm9;
            X64_M128 Xmm10;
            X64_M128 Xmm11;
            X64_M128 Xmm12;
            X64_M128 Xmm13;
            X64_M128 Xmm14;
            X64_M128 Xmm15;
        };
    };

    //
    // Vector registers.
    //

    X64_M128 VectorRegister[26];
    ULONG64 VectorControl;

    //
    // Special debug control registers.
    //

    ULONG64 DebugControl;
    ULONG64 LastBranchToRip;
    ULONG64 LastBranchFromRip;
    ULONG64 LastExceptionToRip;
    ULONG64 LastExceptionFromRip;
} X64_CONTEXT, *PX64_CONTEXT;


//
//  X86 context definitions
//


#define SIZE_OF_80387_REGISTERS      80
#define X86_MAXIMUM_SUPPORTED_EXTENSION     512

typedef struct _X86_FLOATING_SAVE_AREA {
    DWORD   ControlWord;
    DWORD   StatusWord;
    DWORD   TagWord;
    DWORD   ErrorOffset;
    DWORD   ErrorSelector;
    DWORD   DataOffset;
    DWORD   DataSelector;
    BYTE    RegisterArea[SIZE_OF_80387_REGISTERS];
    DWORD   Cr0NpxState;
} X86_FLOATING_SAVE_AREA;

typedef struct _X86_CONTEXT {

    //
    // The flags values within this flag control the contents of
    // a CONTEXT record.
    //
    // If the context record is used as an input parameter, then
    // for each portion of the context record controlled by a flag
    // whose value is set, it is assumed that that portion of the
    // context record contains valid context. If the context record
    // is being used to modify a threads context, then only that
    // portion of the threads context will be modified.
    //
    // If the context record is used as an IN OUT parameter to capture
    // the context of a thread, then only those portions of the thread's
    // context corresponding to set flags will be returned.
    //
    // The context record is never used as an OUT only parameter.
    //

    DWORD ContextFlags;

    //
    // This section is specified/returned if X86_CONTEXT_DEBUG_REGISTERS is
    // set in ContextFlags.  Note that X86_CONTEXT_DEBUG_REGISTERS is NOT
    // included in X86_CONTEXT_FULL.
    //

    DWORD   Dr0;
    DWORD   Dr1;
    DWORD   Dr2;
    DWORD   Dr3;
    DWORD   Dr6;
    DWORD   Dr7;

    //
    // This section is specified/returned if the
    // ContextFlags word contains the flag X86_CONTEXT_FLOATING_POINT.
    //

    X86_FLOATING_SAVE_AREA FloatSave;

    //
    // This section is specified/returned if the
    // ContextFlags word contains the flag X86_CONTEXT_SEGMENTS.
    //

    DWORD   SegGs;
    DWORD   SegFs;
    DWORD   SegEs;
    DWORD   SegDs;

    //
    // This section is specified/returned if the
    // ContextFlags word contains the flag X86_CONTEXT_INTEGER.
    //

    DWORD   Edi;
    DWORD   Esi;
    DWORD   Ebx;
    DWORD   Edx;
    DWORD   Ecx;
    DWORD   Eax;

    //
    // This section is specified/returned if the
    // ContextFlags word contains the flag X86_CONTEXT_CONTROL.
    //

    DWORD   Ebp;
    DWORD   Eip;
    DWORD   SegCs;              // MUST BE SANITIZED
    DWORD   EFlags;             // MUST BE SANITIZED
    DWORD   Esp;
    DWORD   SegSs;

    //
    // This section is specified/returned if the
    // ContextFlags word contains the flag X86_CONTEXT_SYSTEM
    //

    DWORD   Cr0;
    DWORD   Cr2;
    DWORD   Cr3;
    DWORD   Cr4;

    //
    // This section is specified/returned if the ContextFlags word
    // contains the flag X86_CONTEXT_EXTENDED_REGISTERS.
    // The format and contexts are processor specific
    //

    BYTE    ExtendedRegisters[X86_MAXIMUM_SUPPORTED_EXTENSION];

} X86_CONTEXT;

typedef struct _ARM_CONTEXT {

    //
    // Control flags.
    //

    DWORD   ContextFlags;

    //
    // Integer registers
    //

    DWORD   R0;
    DWORD   R1;
    DWORD   R2;
    DWORD   R3;
    DWORD   R4;
    DWORD   R5;
    DWORD   R6;
    DWORD   R7;
    DWORD   R8;
    DWORD   R9;
    DWORD   R10;
    DWORD   R11;
    DWORD   R12;

    //
    // Control Registers
    //

    DWORD   Sp;
    DWORD   Lr;
    DWORD   Pc;
    DWORD   Cpsr;

} ARM_CONTEXT;

//
//////////////////////////////////////////////////////////////////////////////

// Declares an extension routine.
#define EXT_DECL(Name) \
    extern "C" HRESULT CALLBACK \
    Name(PDEBUG_CLIENT client, PCSTR args)

// Set up and clean up for an extension routine.
#define EXT_ENTER() \
    HRESULT status = ExtQuery(client); \
    if (status != S_OK) goto Exit; else 0

#define EXT_LEAVE() \
    Exit: ExtRelease(); return status

// Safe release and NULL.
#define EXT_RELEASE(Unk) \
    ((Unk) != NULL ? ((Unk)->Release(), (Unk) = NULL) : NULL)

// Evaluates a numeric expression from the current args
// and updates the Args location.
// Assumes variables args and status, plus exit label Exit.
#define EXT_ARG(Dst) \
    if ((status = ExtEvalU64(&args, &(Dst))) != S_OK) goto Exit; else 0

#define EXT_CHECK(expr) \
    if ((status = expr) != S_OK) goto Exit; else 0

// Global variables initialized by query.
extern PDEBUG_ADVANCED       g_ExtAdvanced;
extern PDEBUG_CLIENT         g_ExtClient;
extern PDEBUG_CONTROL4       g_ExtControl;
extern PDEBUG_DATA_SPACES4   g_ExtData;
extern PDEBUG_REGISTERS2     g_ExtRegisters;
extern PDEBUG_SYMBOLS        g_ExtSymbols;
extern PDEBUG_SYSTEM_OBJECTS g_ExtSystem;

// Queries for all debugger interfaces.
HRESULT ExtQuery(PDEBUG_CLIENT Client);

// Cleans up all debugger interfaces.
void ExtRelease(void);

// Normal output.
void __cdecl ExtOut(PCSTR Format, ...);
// Error output.
void __cdecl ExtErr(PCSTR Format, ...);
// Warning output.
void __cdecl ExtWarn(PCSTR Format, ...);
// Verbose output.
void __cdecl ExtVerb(PCSTR Format, ...);


// Evaluates an expression from the given string
// and updates the string pointer.  Consumes trailing whitespace.
HRESULT ExtEvalU64(PCSTR* Str, PULONG64 Val);
HRESULT ExtDefPointer(ULONG64 Address, PULONG64 Val);

extern BOOL  Connected;
extern ULONG TargetMachine;

HRESULT OnTargetAccessible(PDEBUG_CLIENT Client,
                           PDEBUG_CONTROL Control);

HRESULT OnGetKnownStructNames(PDEBUG_CLIENT Client,
                              PSTR Buffer,
                              PULONG BufferSize);
HRESULT OnGetSingleLineOutput(PDEBUG_CLIENT Client,
                              ULONG64 Address,
                              PSTR StructName,
                              PSTR Buffer,
                              PULONG BufferSize);
HRESULT OnGetSuppressTypeName(PDEBUG_CLIENT Client,
                              PSTR StructName);

ULONG64 GetStaticPointer(PCSTR name);

HRESULT FindKernelNameAndInitialize(PDEBUG_CLIENT client);

///////////////////////////////// Remote to Local conversions for structs.
//

// Metadata structures.
struct StructType
{
    struct StructType * next;
    struct FieldType * fields;
    ULONG       fieldCount;
    PSTR        name;
    ULONG64     module;
    ULONG       type;
    ULONG       size;
    PBYTE       temp;
    ULONG       localSize;

  public:
    static StructType * registered;
    static HRESULT InitializeRegistered();

  public:
    StructType(PSTR name, ULONG localSize, struct FieldType *fields);

    HRESULT Initialize();
    HRESULT RemoteOffsetFromLocal(ULONG localOffset, ULONG *remoteOffset);

    HRESULT Clear();
    HRESULT Read(ULONG64 address, PVOID local);
    HRESULT RawAccess(ULONG remoteOffset, PVOID *raw);
    HRESULT Update(PVOID local);
    HRESULT Flush(ULONG64 address);
};

struct FieldType
{
    struct StructType *parent;
    PCSTR       name;
    ULONG       localOffset;
    ULONG64     module;
    ULONG       type;
    ULONG       offset;
    ULONG       size;
};

// Macros for defining metadata.
#define FIELD(s,f)  { NULL, #f, offsetof(s,f), 0, 0, 0, 0 }
#define FIELDEND()  { NULL, NULL, 0, 0, 0, 0, 0 }

/////////////////////////////////////////////////////////// Known Structs.
//
struct MmxContext
{
    ULONG64     fcw;
    ULONG64     fsw;
    ULONG64     ftw;
    ULONG64     fop;
    ULONG64     ip;
    ULONG64     cs;
    ULONG64     dp;
    ULONG64     ds;
    ULONG64     mxcsr;
    ULONG64     mxcsrmask;
    ULONG64     st0;
    ULONG64     st1;
    ULONG64     st2;
    ULONG64     st3;
    ULONG64     st4;
    ULONG64     st5;
    ULONG64     st6;
    ULONG64     st7;
};

struct SpillContext
{
    // X86 & X64 Registers
    ULONG64     ax;
    ULONG64     bx;
    ULONG64     cx;
    ULONG64     dx;
    ULONG64     di;
    ULONG64     si;
    ULONG64     sp; // also used for ARM sp (aka r13)
    ULONG64     ip;
    ULONG64     bp;
    ULONG64     fl;

    // X64 Registers
    ULONG64     r8;
    ULONG64     r9;
    ULONG64     r10;
    ULONG64     r11;
    ULONG64     r12;
    ULONG64     r13;
    ULONG64     r14;
    ULONG64     r15;

    // ARM Registers
    ULONG64     r0;
    ULONG64     r1;
    ULONG64     r2;
    ULONG64     r3;
    ULONG64     r4;
    ULONG64     r5;
    ULONG64     r6;
    ULONG64     r7;
    // r8..r12 repeated above.
    // r13 is sp
    ULONG64     lr; // aka r14
    ULONG64     pc; // aka r15
    ULONG64     cpsr;

    // X86 & X64
    struct MmxContext   mmx;
};

struct ThreadRecord
{
    struct SpillContext spill;
    ULONG64             activeStackLimit;
};
extern StructType ThreadRecordStruct;

struct ThreadContext
{
    struct ThreadRecord threadRecord;

    ULONG64     num;
    ULONG64     regs;
    ULONG64     prev;
    ULONG64     next;
    ULONG64     stackBegin;
    ULONG64     stackLimit;
    ULONG64     processId;
    ULONG64     uncaughtFlag;
    ULONG64     suspendAlert;
    ULONG64     _thread;
    ULONG64     processThread;
    ULONG64     stackMarkers;
    ULONG64     processMarkers;
    ULONG64     threadIndex;
    ULONG64     processThreadIndex;
    ULONG64     gcStates;
};

extern FieldType *ThreadContextFields;
extern StructType *ThreadContextStruct;

struct Thread
{
    ULONG64     blocked;
    ULONG64     blockedOn;
    ULONG64     blockedOnCount;
    ULONG64     blockedUntil;
    ULONG64     process;
    ULONG64     schedulerEntry;
    ThreadContext   context;
};

extern FieldType *ThreadFields;
extern StructType *ThreadStruct;

struct ThreadEntry
{
    ULONG64     queue;
};

extern StructType ThreadEntryStruct;

struct CpuRecord
{
    // struct SpillContext spill; unused here

    ULONG64     id;
    ULONG64     interruptStackBegin;
    ULONG64     interruptStackLimit;

    struct ThreadRecord bootThread;
};
extern StructType CpuRecordStruct;

struct ProcessorContext
{
    struct CpuRecord        cpuRecord;

    ULONG64     _processor;
    ULONG64     exception;

    ULONG64     nextProcessorContext;
};
extern StructType ProcessorContextStruct;

struct Processor
{
    ULONG64     context;

    ULONG64     pic;
    ULONG64     timer;
    ULONG64     clock;

    ULONG64     timerInterrupt;
    ULONG64     clockInterrupt;
    ULONG64     inInterruptContext;
    ULONG64     halted;

    ULONG64     NumExceptions;
    ULONG64     NumInterrupts;
    ULONG64     NumContextSwitches;

    ULONG64     interruptCounts;
};
extern StructType ProcessorStruct;

struct String
{
    ULONG64     m_stringLength;
    ULONG64     m_firstChar;
};

extern FieldType StringFields[];
extern StructType StringStruct;

struct LogEntry
{
    ULONG64     _cycleCount;
    ULONG64     _cpuId;
    ULONG64     _eip;
    ULONG64     _threadId;
    ULONG64     _processId;
    ULONG64     _tag;
    ULONG64     _severity;
    ULONG64     _strings;
    ULONG64     _text;
    union
    {
        ULONG64     _args[6];
        struct
        {
            ULONG64 _arg0;
            ULONG64 _arg1;
            ULONG64 _arg2;
            ULONG64 _arg3;
            ULONG64 _arg4;
            ULONG64 _arg5;
        };
    };
};
extern StructType LogEntryStruct;

// The name of the Singularity kernel is 'kernel.*'.  However, when performing kernel debugging the
// Microsoft debuggers want to call it 'nt'.  Since we want to use the Singx86 debug extension both
// for kernel and non-kernel debugging, we need a way to build the debug extension for each naming
// convention.

// We fix in place, so OnTargetAccessible checks that that sizeof(KERNEL_NAME) exceeds
// sizeof(ALTERNATE_KERNEL_NAME) before it activates the alternate name.
#define KERNEL_NAME                 "kernel"
#define ALTERNATE_KERNEL_NAME       "nt"

#define LEN_KERNEL_NAME             (sizeof(KERNEL_NAME) - 1)
#define LEN_ALTERNATE_KERNEL_NAME   (sizeof(ALTERNATE_KERNEL_NAME) - 1)

extern BOOL                         UseAlternateKernelName;
void                                FixKernelName(char *candidate);

// Resources:

// Turn 'RES_ENTRY(g_pBootInfo, blah)' into 'extern char kernel_g_pBootInfo [];'
#define RES_ENTRY(sym, name)     extern char kernel_ ## sym [];
#include "res.inl"
#undef RES_ENTRY

// Turn 'RES_ENTRY(g_pBootInfo, blah)' into 'enum_kernel_g_pBootInfo,'
#define RES_ENTRY(sym, name)     enum_kernel_ ## sym,
enum enum_KernelTable {
#include "res.inl"
                                 countKernelTable,
};
#undef RES_ENTRY

extern char *KernelTable[];
HRESULT TraceRead(UINT64 address, void * buffer, ULONG size);
HRESULT TraceReadPointer(int count, UINT64 address, PULONG64 buffer);


