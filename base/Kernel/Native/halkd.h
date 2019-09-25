///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkd.h
//

#define IN
#define OUT
#define OPTIONAL
#define CONST const

#if PTR_SIZE_32
#define SIGN_EXTEND(x)  ((UINT64)(INT64)(INT32)(x))
#elif PTR_SIZE_64
#define SIGN_EXTEND(x)  ((UINT64)(x))
#endif

// NT Compat types
typedef BOOL BOOLEAN;
typedef char *PCHAR;
typedef char  CHAR;
typedef UCHAR *PUCHAR;
typedef UINT32 NTSTATUS;

typedef struct _STRING {
    UINT16  Length;
    UINT16  MaximumLength;
    CHAR *  Buffer;
} STRING, *PSTRING;

typedef struct _UNICODE_STRING {
    UINT16  Length;
    UINT16  MaximumLength;
    WCHAR * Buffer;
} UNICODE_STRING;

typedef struct _LIST_ENTRY {
    struct _LIST_ENTRY *Flink;
    struct _LIST_ENTRY *Blink;
} LIST_ENTRY, *PLIST_ENTRY;

//======================================================================
// Selected structs and defines used by the kernel debugger
//
typedef struct _KLDR_DATA_TABLE_ENTRY {
    LIST_ENTRY InLoadOrderLinks;
    PVOID   __Unused1;
    PVOID   __Unused2;
    PVOID   __Unused3;
    PVOID   NonPagedDebugInfo;
    PVOID   DllBase;
    PVOID   EntryPoint;
    UINT32  SizeOfImage;
    UNICODE_STRING FullDllName;
    UNICODE_STRING BaseDllName;
    UINT32  Flags;
    UINT16  LoadCount;
    UINT16  __Unused5;
    PVOID   SectionPointer;
    UINT32  CheckSum;
    // UINT32 padding on IA64
    UINT32  TimeDateStamp;
    //    PVOID LoadedImports;
    PVOID   __Unused6;
} KLDR_DATA_TABLE_ENTRY, *PKLDR_DATA_TABLE_ENTRY;

//======================================================================
// Selected structs and defines used by the KD protocol
//

///////////////////////////////////////////////////////////////////////// X86.
//
#define X86_REPORT_INCLUDES_SEGS    0x0001
// Indicates the current CS is a standard 32-bit flat segment.
// This allows the debugger to avoid retrieving the
// CS descriptor to see if it's 16-bit code or not.
// Note that the V86 flag in EFlags must also be checked
// when determining the code type.
#define X86_REPORT_STANDARD_CS      0x0002

#define X86_DEBUG_CONTROL_SPACE_KSPECIAL    716

//////////////////////////////////////////////////////////////////////// IA64.
//
#define IA64_DBGKD_CONTROL_SET_CONTINUE_NONE                0x0000
#define IA64_DBGKD_CONTROL_SET_CONTINUE_TRACE_INSTRUCTION   0x0001
#define IA64_DBGKD_CONTROL_SET_CONTINUE_TRACE_TAKEN_BRANCH  0x0002

//
// Aliases to keep old-timers comfortable with new-fangled code.
//
#define ALPHA_DBGKD_CONTROL_REPORT      Struct_Microsoft_Singularity_Kd_AlphaKdControlReport
#define ALPHA_DBGKD_CONTROL_SET         Struct_Microsoft_Singularity_Kd_AlphaKdControlSet
#define ARM_CONTEXT                     Struct_Microsoft_Singularity_Kd_ArmContext
#define ARM_DBGKD_CONTROL_REPORT        Struct_Microsoft_Singularity_Kd_ArmKdControlReport
#define ARM_DBGKD_CONTROL_SET           Struct_Microsoft_Singularity_Kd_ArmKdControlSet
#define ARM_KPROCESSOR_STATE            Struct_Microsoft_Singularity_Kd_ArmKProcessorState
#define ARM_KSPECIAL_REGISTERS          Struct_Microsoft_Singularity_Kd_ArmKSpecialRegisters
#define ARM_RUNTIME_FUNCTION            Struct_Microsoft_Singularity_Kd_ArmRuntimeFunction
#define ARM_RUNTIME_FUNCTION_EXCEPTION  Struct_Microsoft_Singularity_Kd_ArmRuntimeFunctionException
#define IA64_DBGKD_CONTROL_REPORT       Struct_Microsoft_Singularity_Kd_Ia64KdControlReport
#define IA64_DBGKD_CONTROL_SET          Struct_Microsoft_Singularity_Kd_Ia64KdControlSet
#define X64_CONTEXT                     Struct_Microsoft_Singularity_Kd_X64Context
#define X64_DBGKD_CONTROL_REPORT        Struct_Microsoft_Singularity_Kd_X64KdControlReport
#define X64_DBGKD_CONTROL_SET           Struct_Microsoft_Singularity_Kd_X64KdControlSet
#define X64_DESCRIPTOR                  Struct_Microsoft_Singularity_Kd_X64Descriptor
#define X64_KPROCESSOR_STATE            Struct_Microsoft_Singularity_Kd_X64KProcessorState
#define X64_KSPECIAL_REGISTERS          Struct_Microsoft_Singularity_Kd_X64KSpecialRegisters
#define X64_VECTOR_REGISTERS            Struct_Microsoft_Singularity_Kd_X64VectorRegisters
#define X86_387_REGISTER                Struct_Microsoft_Singularity_Kd_X86Fp387Register
#define X86_387_SAVE_AREA               Struct_Microsoft_Singularity_Kd_X86Fp387SaveArea
#define X86_CONTEXT                     Struct_Microsoft_Singularity_Kd_X86Context
#define X86_DBGKD_CONTROL_REPORT        Struct_Microsoft_Singularity_Kd_X86KdControlReport
#define X86_DBGKD_CONTROL_SET           Struct_Microsoft_Singularity_Kd_X86KdControlSet
#define X86_DESCRIPTOR                  Struct_Microsoft_Singularity_Kd_X86Descriptor
#define X86_KPROCESSOR_STATE            Struct_Microsoft_Singularity_Kd_X86KProcessorState
#define X86_KSPECIAL_REGISTERS          Struct_Microsoft_Singularity_Kd_X86KSpecialRegisters
#define X86_SEGMENT_REGISTERS           Struct_Microsoft_Singularity_Kd_X86SegmentRegisters
#define X86_UNALIGNED_128               Struct_Microsoft_Singularity_Kd_X86Unaligned128
#define X86_XMM_SAVE_AREA32             Struct_Microsoft_Singularity_Kd_X86XmmSaveArea32
#define EXCEPTION_RECORD64              Struct_Microsoft_Singularity_Kd_ExceptionRecord64

//////////////////////////////////////////////////////////////////// All ISAs.
//

#define CONTEXT_X86     0x00010000      // i386, etc.
#define CONTEXT_X64     0x00100000      // x64 context record is quite different
#define CONTEXT_ARM     0x00100000

#define CONTEXT_EXCEPTION_ACTIVE    0x08000000
#define CONTEXT_SERVICE_ACTIVE      0x10000000
#define CONTEXT_EXCEPTION_REQUEST   0x40000000
#define CONTEXT_EXCEPTION_REPORTING 0x80000000

#if ISA_IX86

#define CONTEXT_CONTROL             (CONTEXT_X86 | 0x1L) // SS:SP, CS:IP, FLAGS, BP
#define CONTEXT_INTEGER             (CONTEXT_X86 | 0x2L) // AX, BX, CX, DX, SI, DI
#define CONTEXT_SEGMENTS            (CONTEXT_X86 | 0x4L) // DS, ES, FS, GS
#define CONTEXT_FLOATING_POINT      (CONTEXT_X86 | 0x8L) // 387 state
#define CONTEXT_DEBUG_REGISTERS     (CONTEXT_X86 | 0x10L) // DB 0-3,6,7
#define CONTEXT_EXTENDED_REGISTERS  (CONTEXT_X86 | 0x20L) // cpu specific extensions

#define CONTEXT_FULL (CONTEXT_CONTROL | CONTEXT_INTEGER | CONTEXT_SEGMENTS)

#define CONTEXT_ALL (CONTEXT_CONTROL | CONTEXT_INTEGER | CONTEXT_SEGMENTS | CONTEXT_FLOATING_POINT | CONTEXT_DEBUG_REGISTERS | CONTEXT_EXTENDED_REGISTERS)

typedef X86_CONTEXT CONTEXT, *PCONTEXT;
typedef X86_KSPECIAL_REGISTERS KSPECIAL_REGISTERS, *PKSPECIAL_REGISTERS;
typedef X86_KPROCESSOR_STATE KPROCESSOR_STATE, *PKPROCESSOR_STATE;
typedef X86_DBGKD_CONTROL_REPORT DBGKD_CONTROL_REPORT, *PDBGKD_CONTROL_REPORT;
typedef X86_DBGKD_CONTROL_SET DBGKD_CONTROL_SET;

#define KDP_BREAKPOINT_TYPE         uint8
#define KDP_BREAKPOINT_BUFFER       sizeof(uint8)
#define KDP_BREAKPOINT_ALIGN        0
#define KDP_BREAKPOINT_INSTR_ALIGN  0
#define KDP_BREAKPOINT_VALUE        0xcc        // int 3

#elif ISA_IX64

#define CONTEXT_CONTROL             (CONTEXT_X64 | 0x1L)
#define CONTEXT_INTEGER             (CONTEXT_X64 | 0x2L)
#define CONTEXT_SEGMENTS            (CONTEXT_X64 | 0x4L)
#define CONTEXT_FLOATING_POINT      (CONTEXT_X64 | 0x8L)
#define CONTEXT_DEBUG_REGISTERS     (CONTEXT_X64 | 0x10L)

#define CONTEXT_FULL (CONTEXT_CONTROL | CONTEXT_INTEGER | CONTEXT_FLOATING_POINT)

#define CONTEXT_ALL (CONTEXT_CONTROL | CONTEXT_INTEGER | CONTEXT_SEGMENTS | CONTEXT_FLOATING_POINT | CONTEXT_DEBUG_REGISTERS)

typedef X64_CONTEXT CONTEXT, *PCONTEXT;
typedef X64_KSPECIAL_REGISTERS KSPECIAL_REGISTERS, *PKSPECIAL_REGISTERS;
typedef X64_KPROCESSOR_STATE KPROCESSOR_STATE, *PKPROCESSOR_STATE;
typedef X64_DBGKD_CONTROL_REPORT DBGKD_CONTROL_REPORT, *PDBGKD_CONTROL_REPORT;
typedef X64_DBGKD_CONTROL_SET DBGKD_CONTROL_SET;

#define KDP_BREAKPOINT_TYPE         uint8
#define KDP_BREAKPOINT_BUFFER       sizeof(uint8)
#define KDP_BREAKPOINT_ALIGN        0
#define KDP_BREAKPOINT_INSTR_ALIGN  0
#define KDP_BREAKPOINT_VALUE        0xcc        // int 3

#elif ISA_ARM

#define CONTEXT_CONTROL             (CONTEXT_ARM | 0x1L)
#define CONTEXT_INTEGER             (CONTEXT_ARM | 0x2L)
#define CONTEXT_FLOATING_POINT      (CONTEXT_ARM | 0x4L)
#define CONTEXT_DEBUG_REGISTERS     (CONTEXT_ARM | 0x8L)

#define CONTEXT_FULL (CONTEXT_CONTROL | CONTEXT_INTEGER | CONTEXT_FLOATING_POINT)

#define CONTEXT_ALL (CONTEXT_CONTROL | CONTEXT_INTEGER | CONTEXT_FLOATING_POINT | CONTEXT_DEBUG_REGISTERS)

typedef ARM_CONTEXT CONTEXT, *PCONTEXT;
typedef ARM_KSPECIAL_REGISTERS KSPECIAL_REGISTERS, *PKSPECIAL_REGISTERS;
typedef ARM_KPROCESSOR_STATE KPROCESSOR_STATE, *PKPROCESSOR_STATE;
typedef ARM_DBGKD_CONTROL_REPORT DBGKD_CONTROL_REPORT, *PDBGKD_CONTROL_REPORT;
typedef ARM_DBGKD_CONTROL_SET DBGKD_CONTROL_SET;

#define KDP_BREAKPOINT_TYPE         UINT32
#define KDP_BREAKPOINT_BUFFER       sizeof(UINT32)
#define KDP_BREAKPOINT_ALIGN        4
#define KDP_BREAKPOINT_INSTR_ALIGN  4
#define KDP_BREAKPOINT_VALUE        0xefffff01  // swi 0xffff01

#endif

//-----> From winnt.h#3566

//#pragma pack(pop)

//
//  Values put in ExceptionRecord.ExceptionInformation[0]
//  First parameter is always in ExceptionInformation[1],
//  Second parameter is always in ExceptionInformation[2]
//

#define BREAKPOINT_BREAK            0
#define BREAKPOINT_PRINT            1
#define BREAKPOINT_PROMPT           2
#define BREAKPOINT_LOAD_SYMBOLS     3
#define BREAKPOINT_UNLOAD_SYMBOLS   4
#define BREAKPOINT_COMMAND_STRING   5

// Don't care what these point to!
typedef void *PKTRAP_FRAME;
typedef void *PKEXCEPTION_FRAME;

//
// Processor modes.
//
typedef CHAR KPROCESSOR_MODE;
typedef enum _MODE {
    KernelMode,
    UserMode,
    MaximumMode
} MODE;


typedef struct _DBGKM_EXCEPTION64 {
    EXCEPTION_RECORD64 ExceptionRecord;
    UINT32 FirstChance;
} DBGKM_EXCEPTION64, *PDBGKM_EXCEPTION64;

typedef struct _DBGKD_ANY_CONTROL_REPORT {
    union {
        X86_DBGKD_CONTROL_REPORT X86ControlReport;
        ALPHA_DBGKD_CONTROL_REPORT AlphaControlReport;
        IA64_DBGKD_CONTROL_REPORT IA64ControlReport;
        X64_DBGKD_CONTROL_REPORT X64ControlReport;
        ARM_DBGKD_CONTROL_REPORT ARMControlReport;
    };
} DBGKD_ANY_CONTROL_REPORT, *PDBGKD_ANY_CONTROL_REPORT;

typedef struct _DBGKD_LOAD_SYMBOLS64 {
    UINT32  PathNameLength;
    UINT64  BaseOfDll;
    UINT64  ProcessId;
    UINT32  CheckSum;
    UINT32  SizeOfImage;
    BOOLEAN UnloadSymbols;
} DBGKD_LOAD_SYMBOLS64, *PDBGKD_LOAD_SYMBOLS64;

typedef struct _DBGKD_COMMAND_STRING {
    UINT32  Flags;
    UINT32  Reserved1;
    UINT64  Reserved2[7];
} DBGKD_COMMAND_STRING, *PDBGKD_COMMAND_STRING;

// Protocol version 6 state change.
typedef struct _DBGKD_ANY_WAIT_STATE_CHANGE {
    UINT32  NewState;
    UINT16  ProcessorLevel;
    UINT16  Processor;
    UINT32  NumberProcessors;
    UINT64  Thread;
    UINT64  ProgramCounter;
    union {
        DBGKM_EXCEPTION64 Exception;
        DBGKD_LOAD_SYMBOLS64 LoadSymbols;
        DBGKD_COMMAND_STRING CommandString;
    };
    // The ANY control report is unioned here to
    // ensure that this structure is always large
    // enough to hold any possible state change.
    union {
        DBGKD_CONTROL_REPORT ControlReport;
        DBGKD_ANY_CONTROL_REPORT AnyControlReport;
    };
} DBGKD_ANY_WAIT_STATE_CHANGE, *PDBGKD_ANY_WAIT_STATE_CHANGE;

#define DEBUG_CONTROL_SPACE_KSPECIAL 2

typedef struct _DBGKD_READ_MEMORY64 {
    UINT64  TargetBaseAddress;
    UINT32  TransferCount;
    UINT32  ActualBytesRead;
} DBGKD_READ_MEMORY64, *PDBGKD_READ_MEMORY64;

typedef struct _DBGKD_WRITE_MEMORY64 {
    UINT64  TargetBaseAddress;
    UINT32  TransferCount;
    UINT32  ActualBytesWritten;
} DBGKD_WRITE_MEMORY64, *PDBGKD_WRITE_MEMORY64;

typedef struct _DBGKD_READ_WRITE_IO64 {
    UINT64 IoAddress;
    UINT32 DataSize;                     // 1, 2, 4
    UINT32 DataValue;
} DBGKD_READ_WRITE_IO64, *PDBGKD_READ_WRITE_IO64;

//
// Response is a get context message with a full context record following
//

typedef struct _DBGKD_GET_CONTEXT {
    UINT32  Unused;
} DBGKD_GET_CONTEXT, *PDBGKD_GET_CONTEXT;

//
// Full Context record follows
//

typedef struct _DBGKD_SET_CONTEXT {
    UINT32  ContextFlags;
} DBGKD_SET_CONTEXT, *PDBGKD_SET_CONTEXT;

//
// Define breakpoint table entry structure.
//

#define KD_BREAKPOINT_IN_USE        0x00000001
#define KD_BREAKPOINT_NEEDS_WRITE   0x00000002
#define KD_BREAKPOINT_SUSPENDED     0x00000004
#define KD_BREAKPOINT_NEEDS_REPLACE 0x00000008

typedef struct _BREAKPOINT_ENTRY {
    UINT32  Flags;
    ULONG_PTR DirectoryTableBase;
    PVOID   Address;
    KDP_BREAKPOINT_TYPE Content;
} BREAKPOINT_ENTRY, *PBREAKPOINT_ENTRY;

#define BREAKPOINT_TABLE_SIZE   32      // max number supported by kernel


typedef struct _DBGKD_WRITE_BREAKPOINT32 {
    UINT32  BreakPointAddress;
    UINT32  BreakPointHandle;
} DBGKD_WRITE_BREAKPOINT32, *PDBGKD_WRITE_BREAKPOINT32;

typedef struct _DBGKD_WRITE_BREAKPOINT64 {
    UINT64  BreakPointAddress;
    UINT32  BreakPointHandle;
} DBGKD_WRITE_BREAKPOINT64, *PDBGKD_WRITE_BREAKPOINT64;

typedef struct _DBGKD_RESTORE_BREAKPOINT {
    UINT32  BreakPointHandle;
} DBGKD_RESTORE_BREAKPOINT, *PDBGKD_RESTORE_BREAKPOINT;

typedef struct _DBGKD_CONTINUE {
    NTSTATUS ContinueStatus;
} DBGKD_CONTINUE, *PDBGKD_CONTINUE;

typedef struct _DBGKD_ANY_CONTROL_SET {
    union {
        X86_DBGKD_CONTROL_SET X86ControlSet;
        ALPHA_DBGKD_CONTROL_SET AlphaControlSet;
        IA64_DBGKD_CONTROL_SET IA64ControlSet;
        X64_DBGKD_CONTROL_SET X64ControlSet;
        ARM_DBGKD_CONTROL_SET ARMControlSet;
    };
} DBGKD_ANY_CONTROL_SET, *PDBGKD_ANY_CONTROL_SET;

// This structure must be 32-bit packed for
// for compatibility with older, processor-specific
// versions of this structure.

typedef struct _DBGKD_CONTINUE2 {
    // The ANY control set is unioned here to
    // ensure that this structure is always large
    // enough to hold any possible continue.
    union {
        NTSTATUS ContinueStatus;
        DBGKD_CONTROL_SET ControlSet;
        DBGKD_ANY_CONTROL_SET AnyControlSet;
    };
} DBGKD_CONTINUE2, *PDBGKD_CONTINUE2;

//
// MSR support
//

typedef struct _DBGKD_READ_WRITE_MSR {
    UINT32  Msr;
    UINT32  DataValueLow;
    UINT32  DataValueHigh;
} DBGKD_READ_WRITE_MSR, *PDBGKD_READ_WRITE_MSR;


typedef struct _DBGKD_GET_VERSION64 {
    UINT16  MajorVersion;
    UINT16  MinorVersion;
    UINT16  ProtocolVersion;
    UINT16  Flags;
    UINT16  MachineType;

    //
    // Protocol command support descriptions.
    // These allow the debugger to automatically
    // adapt to different levels of command support
    // in different kernels.
    //

    // One beyond highest packet type understood, zero based.
    UCHAR   MaxPacketType;
    // One beyond highest state change understood, zero based.
    UCHAR   MaxStateChange;
    // One beyond highest state manipulate message understood, zero based.
    UCHAR   MaxManipulate;

    // Kind of execution environment the kernel is running in,
    // such as a real machine or a simulator.  Written back
    // by the simulation if one exists.
    UCHAR   Simulation;

    UINT16  Unused[1];

    UINT64  KernBase;
    UINT64  PsLoadedModuleList;

    //
    // Components may register a debug data block for use by
    // debugger extensions.  This is the address of the list head.
    //
    // There will always be an entry for the debugger.
    //

    UINT64  DebuggerDataList;

} DBGKD_GET_VERSION64, *PDBGKD_GET_VERSION64;


typedef struct _DBGKD_MANIPULATE_STATE64 {
    UINT32 ApiNumber;
    UINT16 ProcessorLevel;
    UINT16 Processor;
    NTSTATUS ReturnStatus;
    union {
        DBGKD_READ_MEMORY64 ReadMemory;
        DBGKD_WRITE_MEMORY64 WriteMemory;
        DBGKD_GET_VERSION64 GetVersion64;
        DBGKD_GET_CONTEXT GetContext;
        DBGKD_SET_CONTEXT SetContext;
        DBGKD_WRITE_BREAKPOINT64 WriteBreakPoint;
        DBGKD_RESTORE_BREAKPOINT RestoreBreakPoint;
        DBGKD_CONTINUE Continue;
        DBGKD_CONTINUE2 Continue2;
        DBGKD_READ_WRITE_MSR ReadWriteMsr;
        DBGKD_READ_WRITE_IO64 ReadWriteIo;
#if 0
        DBGKD_READ_WRITE_IO_EXTENDED64 ReadWriteIoExtended;
        DBGKD_QUERY_SPECIAL_CALLS QuerySpecialCalls;
        DBGKD_SET_SPECIAL_CALL64 SetSpecialCall;
        DBGKD_SET_INTERNAL_BREAKPOINT64 SetInternalBreakpoint;
        DBGKD_GET_INTERNAL_BREAKPOINT64 GetInternalBreakpoint;
        DBGKD_BREAKPOINTEX BreakPointEx;
        DBGKD_SEARCH_MEMORY SearchMemory;
        DBGKD_GET_SET_BUS_DATA GetSetBusData;
        DBGKD_FILL_MEMORY FillMemory;
        DBGKD_QUERY_MEMORY QueryMemory;
        DBGKD_SWITCH_PARTITION SwitchPartition;
#endif

    };
} DBGKD_MANIPULATE_STATE64, *PDBGKD_MANIPULATE_STATE64;

//
// If the packet type is PACKET_TYPE_KD_DEBUG_IO, then
// the format of the packet data is as follows:
//

#define DbgKdPrintStringApi     0x00003230L
#define DbgKdGetStringApi       0x00003231L

//
// For print string, the Null terminated string to print
// immediately follows the message
//
typedef struct _DBGKD_PRINT_STRING {
    UINT32 LengthOfString;
} DBGKD_PRINT_STRING, *PDBGKD_PRINT_STRING;

//
// For get string, the Null terminated prompt string
// immediately follows the message. The LengthOfStringRead
// field initially contains the maximum number of characters
// to read. Upon reply, this contains the number of bytes actually
// read. The data read immediately follows the message.
//
//
typedef struct _DBGKD_GET_STRING {
    UINT32 LengthOfPromptString;
    UINT32 LengthOfStringRead;
} DBGKD_GET_STRING, *PDBGKD_GET_STRING;

typedef struct _DBGKD_DEBUG_IO {
    UINT32 ApiNumber;
    UINT16 ProcessorLevel;
    UINT16 Processor;
    union {
        DBGKD_PRINT_STRING PrintString;
        DBGKD_GET_STRING GetString;
    };
} DBGKD_DEBUG_IO, *PDBGKD_DEBUG_IO;

//
// DbgKd APIs are for the portable kernel debugger
//

//
// KD_PACKETS are the low level data format used in KD. All packets
// begin with a packet leader, byte count, packet type. The sequence
// for accepting a packet is:
//
//  - read 4 bytes to get packet leader.  If read times out (10 seconds)
//    with a short read, or if packet leader is incorrect, then retry
//    the read.
//
//  - next read 2 byte packet type.  If read times out (10 seconds) with
//    a short read, or if packet type is bad, then start again looking
//    for a packet leader.
//
//  - next read 4 byte packet Id.  If read times out (10 seconds)
//    with a short read, or if packet Id is not what we expect, then
//    ask for resend and restart again looking for a packet leader.
//
//  - next read 2 byte count.  If read times out (10 seconds) with
//    a short read, or if byte count is greater than PACKET_MAX_SIZE,
//    then start again looking for a packet leader.
//
//  - next read 4 byte packet data checksum.
//
//  - The packet data immediately follows the packet.  There should be
//    ByteCount bytes following the packet header.  Read the packet
//    data, if read times out (10 seconds) then start again looking for
//    a packet leader.
//


typedef struct _KD_PACKET {
    UINT32 PacketLeader;
    UINT16 PacketType;
    UINT16 ByteCount;
    UINT32 PacketId;
    UINT32 Checksum;
} KD_PACKET, *PKD_PACKET;

#define PACKET_MAX_SIZE 4000
#define INITIAL_PACKET_ID 0x80800000    // Don't use 0
#define SYNC_PACKET_ID    0x00000800    // Or in with INITIAL_PACKET_ID
                                        // to force a packet ID reset.

//
// BreakIn packet
//

#define BREAKIN_PACKET                  0x62626262
#define BREAKIN_PACKET_BYTE             0x62

//
// Packet lead in sequence
//

#define PACKET_LEADER                   0x30303030 //0x77000077
#define PACKET_LEADER_BYTE              0x30

#define CONTROL_PACKET_LEADER           0x69696969
#define CONTROL_PACKET_LEADER_BYTE      0x69

//
// Packet Trailing Byte
//

#define PACKET_TRAILING_BYTE            0xAA

//
// Packet Types
//

#define PACKET_TYPE_UNUSED              0
#define PACKET_TYPE_KD_STATE_CHANGE32   1
#define PACKET_TYPE_KD_STATE_MANIPULATE 2
#define PACKET_TYPE_KD_DEBUG_IO         3
#define PACKET_TYPE_KD_ACKNOWLEDGE      4       // Packet-control type
#define PACKET_TYPE_KD_RESEND           5       // Packet-control type
#define PACKET_TYPE_KD_RESET            6       // Packet-control type
#define PACKET_TYPE_KD_STATE_CHANGE64   7
#define PACKET_TYPE_KD_POLL_BREAKIN     8
#define PACKET_TYPE_KD_TRACE_IO         9
#define PACKET_TYPE_KD_CONTROL_REQUEST  10
#define PACKET_TYPE_KD_FILE_IO          11
#define PACKET_TYPE_MAX                 12


// State change constants
#define DbgKdMinimumStateChange       0x00003030L
#define DbgKdExceptionStateChange     0x00003030L
#define DbgKdLoadSymbolsStateChange   0x00003031L
#define DbgKdCommandStringStateChange 0x00003032L
#define DbgKdMaximumStateChange       0x00003033L


//
// If the packet type is PACKET_TYPE_KD_STATE_MANIPULATE, then
// the format of the packet data is as follows:
//
// Api Numbers for state manipulation
//

#define DbgKdMinimumManipulate              0x00003130L

#define DbgKdReadVirtualMemoryApi           0x00003130L
#define DbgKdWriteVirtualMemoryApi          0x00003131L
#define DbgKdGetContextApi                  0x00003132L
#define DbgKdSetContextApi                  0x00003133L
#define DbgKdWriteBreakPointApi             0x00003134L
#define DbgKdRestoreBreakPointApi           0x00003135L
#define DbgKdContinueApi                    0x00003136L
#define DbgKdReadControlSpaceApi            0x00003137L
#define DbgKdWriteControlSpaceApi           0x00003138L
#define DbgKdReadIoSpaceApi                 0x00003139L
#define DbgKdWriteIoSpaceApi                0x0000313AL
#define DbgKdRebootApi                      0x0000313BL
#define DbgKdContinueApi2                   0x0000313CL
#define DbgKdReadPhysicalMemoryApi          0x0000313DL
#define DbgKdWritePhysicalMemoryApi         0x0000313EL
//#define DbgKdQuerySpecialCallsApi           0x0000313FL
#define DbgKdSetSpecialCallApi              0x00003140L
#define DbgKdClearSpecialCallsApi           0x00003141L
#define DbgKdSetInternalBreakPointApi       0x00003142L
#define DbgKdGetInternalBreakPointApi       0x00003143L
#define DbgKdReadIoSpaceExtendedApi         0x00003144L
#define DbgKdWriteIoSpaceExtendedApi        0x00003145L
#define DbgKdGetVersionApi                  0x00003146L
#define DbgKdWriteBreakPointExApi           0x00003147L
#define DbgKdRestoreBreakPointExApi         0x00003148L
#define DbgKdCauseBugCheckApi               0x00003149L
#define DbgKdSwitchProcessor                0x00003150L
#define DbgKdPageInApi                      0x00003151L // obsolete
#define DbgKdReadMachineSpecificRegister    0x00003152L
#define DbgKdWriteMachineSpecificRegister   0x00003153L
#define OldVlm1                             0x00003154L
#define OldVlm2                             0x00003155L
#define DbgKdSearchMemoryApi                0x00003156L
#define DbgKdGetBusDataApi                  0x00003157L
#define DbgKdSetBusDataApi                  0x00003158L
#define DbgKdCheckLowMemoryApi              0x00003159L
#define DbgKdClearAllInternalBreakpointsApi 0x0000315AL
#define DbgKdFillMemoryApi                  0x0000315BL
#define DbgKdQueryMemoryApi                 0x0000315CL
#define DbgKdSwitchPartition                0x0000315DL

#define DbgKdMaximumManipulate              0x0000315EL

typedef struct _KD_CONTEXT {
    UINT32 KdpDefaultRetries;
    BOOLEAN KdpControlCPending;
} KD_CONTEXT, *PKD_CONTEXT;

typedef enum {
    ContinueError = 0,
    ContinueSuccess = 1,
    ContinueProcessorReselected,
    ContinueNextProcessor
} KCONTINUE_STATUS;

//
// If the packet type is PACKET_TYPE_KD_FILE_IO, then
// the format of the packet data is as follows:
//

#define DbgKdCreateFileApi      0x00003430L
#define DbgKdReadFileApi        0x00003431L
#define DbgKdWriteFileApi       0x00003432L
#define DbgKdCloseFileApi       0x00003433L

// Unicode filename follows as additional data.
typedef struct _DBGKD_CREATE_FILE {
    UINT32  DesiredAccess;
    UINT32  FileAttributes;
    UINT32  ShareAccess;
    UINT32  CreateDisposition;
    UINT32  CreateOptions;
    // Return values.
    UINT64  Handle;
    UINT64  Length;
} DBGKD_CREATE_FILE, *PDBGKD_CREATE_FILE;

// Data is returned as additional data in the response.
typedef struct _DBGKD_READ_FILE {
    UINT64  Handle;
    UINT64  Offset;
    UINT32  Length;
} DBGKD_READ_FILE, *PDBGKD_READ_FILE;

// Data is given as additional data.
typedef struct _DBGKD_WRITE_FILE {
    UINT64  Handle;
    UINT64  Offset;
    UINT32  Length;
} DBGKD_WRITE_FILE, *PDBGKD_WRITE_FILE;

typedef struct _DBGKD_CLOSE_FILE {
    UINT64  Handle;
} DBGKD_CLOSE_FILE, *PDBGKD_CLOSE_FILE;

typedef struct _DBGKD_FILE_IO {
    UINT32  ApiNumber;
    NTSTATUS Status;
    union {
        UINT64 ReserveSpace[7];
        DBGKD_CREATE_FILE CreateFile;
        DBGKD_READ_FILE ReadFile;
        DBGKD_WRITE_FILE WriteFile;
        DBGKD_CLOSE_FILE CloseFile;
    };
} DBGKD_FILE_IO, *PDBGKD_FILE_IO;

//
// status Constants for Packet waiting
//

typedef enum {
    KDP_PACKET_RECEIVED     = 0,
    KDP_PACKET_TIMEOUT      = 1,
    KDP_PACKET_RESEND       = 2
} KDP_STATUS;

//
// Status Constants for reading data from comport
//

#define STATUS_SUCCESS                  ((NTSTATUS)0x00000000L)     // ntsubauth

#define STATUS_VCPP_EXCEPTION           ((NTSTATUS)0x406d1388L)
#define STATUS_CPP_EH_EXCEPTION         ((NTSTATUS)0xe06d7363L)

//  The operation that was requested is pending completion.
#define STATUS_PENDING                  ((NTSTATUS)0x00000103L)     // winnt

//  The requested operation was unsuccessful.
#define STATUS_UNSUCCESSFUL             ((NTSTATUS)0xC0000001L)

//  The instruction at "0x%08lx" referenced memory at "0x%08lx". The memory could not be "%s".
#define STATUS_ACCESS_VIOLATION         ((NTSTATUS)0xC0000005L)     // winnt

//  Illegal Instruction: An attempt was made to execute an illegal instruction.
#define STATUS_ILLEGAL_INSTRUCTION      ((NTSTATUS)0xC000001DL)     // winnt

//  {Application Error}:
//  The exception %s (0x%08lx) occurred in the application at location 0x%08lx.
//
#define STATUS_UNHANDLED_EXCEPTION      ((NTSTATUS)0xC0000144L)

//  {EXCEPTION}: Breakpoint: A breakpoint has been reached.
#define STATUS_BREAKPOINT               ((NTSTATUS)0x80000003L)     // winnt

//
// MessageId: STATUS_SINGLE_STEP
//
// MessageText:
//
//  {EXCEPTION}
//  Single Step
//  A single step or trace operation has just been completed.
//
#define STATUS_SINGLE_STEP               ((NTSTATUS)0x80000004L)    // winnt

//
// MessageId: STATUS_WAKE_SYSTEM_DEBUGGER
//
// MessageText:
//
//  {EXCEPTION}
//  Kernel Debugger Awakened
//  The system debugger was awakened by an interrupt.
//
#define STATUS_WAKE_SYSTEM_DEBUGGER      ((NTSTATUS)0x80000007L)    // winnt


#define DBGKD_64BIT_PROTOCOL_VERSION2 6
//
// If DBGKD_VERS_FLAG_DATA is set in Flags, info should be retrieved from
// the KDDEBUGGER_DATA block rather than from the DBGKD_GET_VERSION
// packet.  The data will remain in the version packet for a while to
// reduce compatibility problems.
//

#define DBGKD_VERS_FLAG_MP         0x0001   // kernel is MP built
#define DBGKD_VERS_FLAG_DATA       0x0002   // DebuggerDataList is valid
#define DBGKD_VERS_FLAG_PTR64      0x0004   // native pointers are 64 bits
#define DBGKD_VERS_FLAG_NOMM       0x0008   // No MM - don't decode PTEs
#define DBGKD_VERS_FLAG_HSS        0x0010   // hardware stepping support
#define DBGKD_VERS_FLAG_PARTITIONS 0x0020   // multiple OS partitions exist

#define IMAGE_FILE_MACHINE_X86     0x014c   // Intel 386, etc.
#define IMAGE_FILE_MACHINE_X64     0x8664   // AMD64 (K8), etc.
#define IMAGE_FILE_MACHINE_ARM     0x01c0   // Little endian ARM w/ Thumb

//
// KD version MajorVersion high-byte identifiers.
//
typedef enum _DBGKD_MAJOR_TYPES {
    DBGKD_MAJOR_NT,
    DBGKD_MAJOR_XBOX,
    DBGKD_MAJOR_BIG,
    DBGKD_MAJOR_EXDI,
    DBGKD_MAJOR_NTBD,
    DBGKD_MAJOR_EFI,
    DBGKD_MAJOR_TNT,
    DBGKD_MAJOR_SINGULARITY,
    DBGKD_MAJOR_COUNT
} DBGKD_MAJOR_TYPES;

#define DBGKD_MAJOR_TYPE(MajorVersion) \
    ((DBGKD_MAJOR_TYPES)((MajorVersion) >> 8))


#define MMDBG_COPY_WRITE            0x00000001
#define MMDBG_COPY_PHYSICAL         0x00000002
#define MMDBG_COPY_UNSAFE           0x00000004
#define MMDBG_COPY_CACHED           0x00000008
#define MMDBG_COPY_UNCACHED         0x00000010
#define MMDBG_COPY_WRITE_COMBINED   0x00000020

#define MMDBG_COPY_MAX_SIZE 8


//////////////////////////////////////////////////////////////////////////////
//

void KdInitialize(Class_Microsoft_Singularity_Hal_Platform *platform);
void KdPutChar(char c);

void kdprintf(const char * pszFmt, ...); // Low level debug (to screen) only.
void kdprints(const char * pszFmt); // Low level debug (to screen) only.

void KdpSpin();
UINT32 KdpComputeChecksum(IN PCHAR Buffer, IN UINT32 Length);

bool KdpSerialInit(Class_Microsoft_Singularity_Hal_Platform *nbi);
KDP_STATUS KdpSerialGetByte(OUT PUCHAR Input, BOOL WaitForByte);
void KdpSerialPutByte(IN UCHAR Output);

void KdpSerialSendPacket(UINT32 PacketType,
                         IN PSTRING MessageHeader,
                         IN PSTRING MessageData OPTIONAL,
                         IN OUT PKD_CONTEXT KdContext);
KDP_STATUS KdpSerialReceivePacket(IN UINT32 PacketType,
                                  OUT PSTRING MessageHeader,
                                  OUT PSTRING MessageData,
                                  OUT UINT32 * DataLength,
                                  IN OUT PKD_CONTEXT KdContext);
bool KdpSerialPollBreakIn();

bool Kdp1394Init(UINT16 Channel, ULONG_PTR Base, ULONG_PTR BufferAddr32, UINT32 BufferSize32);

void Kdp1394SendPacket(UINT32 PacketType,
                       IN PSTRING MessageHeader,
                       IN PSTRING MessageData OPTIONAL,
                       IN OUT PKD_CONTEXT KdContext);
KDP_STATUS Kdp1394ReceivePacket(IN UINT32 PacketType,
                                OUT PSTRING MessageHeader,
                                OUT PSTRING MessageData,
                                OUT UINT32 * DataLength,
                                IN OUT PKD_CONTEXT KdContext);
bool Kdp1394PollBreakIn();

///////////////////////////////////////////////// Processor Specific Routines.
//
bool KdpDisableInterruptsInline();
void KdpRestoreInterruptsInline(bool enabled);
void KdpPause();
void KdpFlushInstCache();
bool KdpReadMsr(UINT32 msr, OUT UINT32 *plo, OUT UINT32 *phi);
bool KdpWriteMsr(UINT32 msr, UINT32 lo, UINT32 hi);

void KdpToKdContext(IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *singularity,
                    OUT CONTEXT *windbg);
void KdpFromKdContext(IN CONST CONTEXT *windbg,
                      OUT Struct_Microsoft_Singularity_Isal_SpillContext *singularity);

void KdpSetControlReport(IN OUT PDBGKD_CONTROL_REPORT report,
                         IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *x86Context);
void KdpSetControlSet(IN CONST DBGKD_CONTROL_SET * control,
                      IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *x86Context);

void KdpReadSpecialRegisters(OUT KSPECIAL_REGISTERS *pksp,
                             IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *x86Context);
void KdpWriteSpecialRegisters(IN CONST KSPECIAL_REGISTERS *pksp);

KdDebugTrapData * KdpIsDebugTrap(IN CONST Struct_Microsoft_Singularity_Isal_SpillContext *context,
                                 int id);

void KdpConvertTrapToException(IN OUT EXCEPTION_RECORD64 *per,
                               IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *context,
                               int id);

int KdpReadWriteIoSpace(int size, int iowrite, unsigned short addr, unsigned int value);

//////////////////////////////////////////////////////////// Shared Variables.
//

extern BOOL KdDebuggerNotPresent;
extern UINT32 KdCompNumberRetries;
extern UINT32 KdCompRetryCount;
extern UINT32 KdPacketId;

///////////////////////////////////////////////////////////////// End of File.
