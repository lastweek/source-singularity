////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   eventing.h
//
//  Note: 
//

//  Misc. general purpose declarations

#define ROUND_UP_TO_POWER2( x, n ) (((uintptr)(x) + (uintptr)((n)-1)) & ~((uintptr)(n)-1))
extern "C" void *  __cdecl memcpy(void *, const void *, size_t);

#define C_ASSERT(e) typedef char __C_ASSERT__[(e)?1:-1]

#define BUFFER_VALIDATION 1

#ifdef BUFFER_VALIDATION 

#define EV_ASSERT(x) if (!(x)) __debugbreak();

#else // !BUFFER_VALIDATION 

#define EV_ASSERT(x)

#endif // BUFFER_VALIDATION 


#ifndef PCHAR
#define PCHAR char*
#endif

inline
uint32
strlen(char * str)
{
    uint32 length = 0;
    while (*str++) length += 1;
    return length;
}


extern "C"
PVOID
_ReturnAddress(
    void
    );

char * ConvertToChars(char * dst, bartok_char *src, int32 length);

//  Memory zone management

#define EV_MAXIMUM_ZONE_SIZE            ((uint16)0xff80)
#define EV_DEFAULT_ZONE_BUFFER_RATIO    10
#define EV_ZONE_ALIGNMENT               0x10

typedef struct _ZONE_READY_LIST {

    union {

        struct {

            uint16 ReadyList;
            uint16 Count;
        };

        volatile INT32 AtomicValue32;
    };
    
} ZONE_READY_LIST, *PZONE_READY_LIST;

typedef struct _ZONE_ALLOCATION_POINTER {

    union {

        struct {

            uint16 FreeOffset;
            uint16 Count : 13;
            uint16 Recycling : 1;  // the entire zone is filled with blocks. 
            uint16 Filled : 1;  // the entire zone is filled with blocks. 
            uint16 Committed : 1;  // The last entry allocated has been committed
        };

        volatile INT32 AtomicValue32;
    };
    
} ZONE_ALLOCATION_POINTER, *PZONE_ALLOCATION_POINTER;

//  Declare the system event structures by including the common definition

//  Type definitions for the structure generation macros
//

#define TYPE_UIntPtr UIntPtr
#define TYPE_uint8 uint8
#define TYPE_uint16 uint16
#define TYPE_uint32 uint32
#define TYPE_uint64 uint64
#define TYPE_PCHAR PCHAR
#define TYPE_BOOL bool

#define DECLARE_STRUCTURE_BEGIN(x,d) typedef struct _##x {
#define DECLARE_STRUCTURE_END(x)   } ##x, *P##x;
#define DECLARE_FIELD(c,t,n)   t n;
#define DECLARE_GENERIC_FIELD(s,t,sz,t1,n) t n;
#define DECLARE_SPECIAL_FIELD DECLARE_FIELD
#define DECLARE_EXTENDED_ARRAY_FIELD(s,t,n) uint16 n;
#define _CONSTANT_DEFINITIONS 1
    #include "SystemEvents.inl"
#undef _CONSTANT_DEFINITIONS

//  Declare the external types that are required by the kernel repository

#define _LOGGING_TO_REPOSITORY    

#define DECLARE_STRUCTURE_BEGIN(x,d)  extern UIntPtr Handle_##x;

    #include "SystemEvents.inl"

#undef _LOGGING_TO_REPOSITORY    


#ifdef BUFFER_VALIDATION

void SetEndOfBuffer(PMEMORY_ZONE Zone);

void CheckEndOfBuffer(PMEMORY_ZONE Zone);

#else

#define SetEndOfBuffer(x)

#define CheckEndOfBuffer(x)

#endif // BUFFER_VALIDATION

#define GetMemoryHeader(p,o) (PMEMORY_HEADER)((ULONG_PTR)(p) + (o))
#define GetEntryOffset(p,o) (uint32)((ULONG_PTR)(o) - (ULONG_PTR)(p))
PSOURCE_DESCRIPTOR GetSourceFromHandle(UIntPtr sourceHandle);

void DebugPrintEvent(UIntPtr eventHandle);

//
//  Record layout (optional extensions)
//

#define RECORD_STACK_TRACES Class_Microsoft_Singularity_Eventing_EventSource_CAPTURE_STACK_TRACE

#define RECORD_LAYOUT_FLAGS (RECORD_STACK_TRACES)

// Stack TrackTraces
// Variable size array, first pointer represents the number of pointers in the array

#define RECORD_MAXSTACKSIZE 32

uint32
inline
GetRecordHeaderSize (
    uint16 Flags,
    uint16 StackSize
    )

{
    uint16 HeaderSize = sizeof(MEMORY_HEADER);

    if (Flags & RECORD_STACK_TRACES) {
        
        HeaderSize += StackSize;
    }

    return HeaderSize;
}


inline    
void *
GetRecordInternalStructure (
    PMEMORY_HEADER Record,
    uint16 RecordFlag
    )
{
    if (Record->Flags & RecordFlag) {

        uint16 HeaderSize;

        if (RecordFlag & (RecordFlag - 1)) {

            //  A single bit at the time can be set to query the internal layout info.
            //  Return failure otherwise.

            return NULL;
        }

        //  The structures are allocated in order, as the flags bits decrease
        //  We can clear the flags 

        HeaderSize = GetRecordHeaderSize(Record->Flags & (~((RecordFlag << 1) - 1)), 0);

        return (PVOID)((ULONG_PTR)Record + HeaderSize);
    }

    return NULL;
}


inline    
void *
GetUserRecordStructure (
    PMEMORY_HEADER Record
    )
{
    if (Record->Flags & RECORD_STACK_TRACES) {

        ULONG_PTR * StackSize = (ULONG_PTR *)GetRecordInternalStructure(Record, RECORD_STACK_TRACES);
        return (PVOID)((ULONG_PTR)Record + GetRecordHeaderSize(Record->Flags, (uint16)(*StackSize + 1) * sizeof(UIntPtr)));

    } else {

        return (PVOID)((ULONG_PTR)Record + GetRecordHeaderSize(Record->Flags, 0));
    }

    return NULL;
}

PMEMORY_ZONE
InitializeMemoryZone(void * Buffer, uint16 Size, UIntPtr storageHandle);

PMEMORY_HEADER
AllocateEventEntry(PMEMORY_ZONE Zone, uint16 size);

void
CommitEventEntry(PMEMORY_HEADER Entry);

bool
IsZoneCompleted(PMEMORY_ZONE Zone);

bool
RecycleZone(PMEMORY_ZONE Zone);


#define MEMORY_STORAGE_FLAGS_RECYCLE_MEMORY Struct_Microsoft_Singularity_Eventing_QualityOfService_RecyclableEvents 
#define MEMORY_STORAGE_FLAGS_BREAK_ON_RECYCLE Struct_Microsoft_Singularity_Eventing_QualityOfService_OOM_BreakOnRecycle 
#define MEMORY_STORAGE_FLAGS_ACTIVE_STORAGE Struct_Microsoft_Singularity_Eventing_QualityOfService_ActiveEvents
#define MEMORY_STORAGE_FLAGS_PERMANENT Struct_Microsoft_Singularity_Eventing_QualityOfService_PermanentEvents

//  Just use the pointers for now in translation. 
//  More type checking and safety would have to be added
//

#define HANDLE_TO_STORAGE(x) ((PMEMORY_STORAGE)(x))
#define HANDLE_TO_HEADER(x) ((PMEMORY_HEADER)(x))

#define HANDLE_TO_TYPE(x) ((PEVENT_DESCRIPTOR) (HANDLE_TO_HEADER(x) + 1))
#define HANDLE_TO_SOURCE(x) ((PSOURCE_DESCRIPTOR)( HANDLE_TO_HEADER(x) + 1))

UIntPtr 
RegisterNativeSource(char * sourceName, UIntPtr storageHandle, uint32 controlFlags);

char * GetExtendedString(UIntPtr EntryHandle, int index);

PMEMORY_HEADER 
InternalLogRecord(UIntPtr StorageHandle, 
    uint32 Flags, 
    UIntPtr eventType, 
    PVOID Buffer, 
    uint32 size,
    PVOID * ExtendedBuffer,
    uint32 ExtendedSize );

PMEMORY_HEADER 
InternalLogFixedRecord(UIntPtr StorageHandle, 
    uint32 Flags, 
    UIntPtr eventType, 
    PVOID Buffer, 
    uint32 size);

PMEMORY_HEADER 
InternalLogVariableRecord(bool doCommit,
                          UIntPtr StorageHandle, 
                          uint32 Flags, 
                          UIntPtr eventType, 
                          PVOID Buffer, 
                          uint32 size,
                          int32 stringCount, 
                          Struct_Microsoft_Singularity_Eventing_ArrayType * strings);

//
//  Event fields type
//


#define EVENT_FIELD_TYPE_uint8 Class_Microsoft_Singularity_Eventing_DataType___uint8
#define EVENT_FIELD_TYPE_uint16 Class_Microsoft_Singularity_Eventing_DataType___uint16
#define EVENT_FIELD_TYPE_uint32 Class_Microsoft_Singularity_Eventing_DataType___uint32
#define EVENT_FIELD_TYPE_uint64 Class_Microsoft_Singularity_Eventing_DataType___uint64
#define EVENT_FIELD_TYPE_int8 Class_Microsoft_Singularity_Eventing_DataType___int8
#define EVENT_FIELD_TYPE_int16 Class_Microsoft_Singularity_Eventing_DataType___int16
#define EVENT_FIELD_TYPE_int32 Class_Microsoft_Singularity_Eventing_DataType___int32
#define EVENT_FIELD_TYPE_int64 Class_Microsoft_Singularity_Eventing_DataType___int64

#define EVENT_FIELD_TYPE_IntPtr Class_Microsoft_Singularity_Eventing_DataType___IntPtr
#define EVENT_FIELD_TYPE_UIntPtr Class_Microsoft_Singularity_Eventing_DataType___UIntPtr

#define EVENT_FIELD_TYPE_arrayType Class_Microsoft_Singularity_Eventing_DataType___arrayType
#define EVENT_FIELD_TYPE_string Class_Microsoft_Singularity_Eventing_DataType___string
#define EVENT_FIELD_TYPE_szChar Class_Microsoft_Singularity_Eventing_DataType___szChar

PMEMORY_HEADER
RegisterEventDescriptorImplementation(int stringType,
                                      PVOID name, 
                                      uint16 nameLength, 
                                      PVOID description, 
                                      uint16 descriptionLength);
PMEMORY_HEADER
RegisterFieldDescriptorImplementation(int stringType,
                                      PMEMORY_HEADER Descriptor, 
                                      PVOID name,
                                      uint32 nameLength,
                                      uint16 offset,
                                      uint16 type );

PMEMORY_HEADER
RegisterGenericFieldDescriptorImplementation( int stringType,
                                              PMEMORY_HEADER event, 
                                              PVOID name,
                                              uint32 nameLength,
                                              uint16 offset,
                                              uint16 size,
                                              UIntPtr typeFieldDescriptor);

PMEMORY_HEADER
RegisterEnumDescriptorImplementation(int stringType,
                                     PVOID name, 
                                     uint16 nameLength, 
                                     uint16 type);

PMEMORY_HEADER
RegisterValueDescriptorImplementation(int stringType,
                                      PMEMORY_HEADER descriptor, 
                                      PVOID name,
                                      uint32 nameLength,
                                      uint64 value,
                                      uint8 flagLetter);

void
InitializeRegistrationSystem(void * buffer, size_t size);

void
RegisterNativeTypes();

extern SOURCE_CONTROLLER SourceController;

void
RegisterExternalController(PEXTERNAL_CONTROLLER_DESCRIPTOR controller);

void
UnRegisterExternalController(PEXTERNAL_CONTROLLER_DESCRIPTOR controller);

PMEMORY_STORAGE
inline
GetLocalRepository()
{
    return SourceController.SourceRepository;
}

UIntPtr
inline
GetLocalRepositoryHandle()
{
    return (UIntPtr)GetLocalRepository();
}

void
RegisterRepositoryStorage(PMEMORY_STORAGE storage);

bool
RegisterStorage(PMEMORY_STORAGE storage);

void
UnRegisterStorage(PMEMORY_STORAGE storage);

uint32
MemoryStorageGetNextGeneration(PMEMORY_STORAGE Storage);

PQUERY_VIEW AllocateQueryView( );

PMEMORY_HEADER
GetFirstEntry(PMEMORY_ZONE Zone, bool forward);

PMEMORY_HEADER
GetNextEntry(PQUERY_VIEW view);

void
EnumerateStorageEntries(UIntPtr storageHandle, bool forward);

void
UnRegisterQueryView(PQUERY_VIEW queryView);

//
//  Specific logging prototypes for usage in the native size
//

extern UIntPtr TracingStorageHandle;

void LogExceptionInfo(UIntPtr throwFrom, UIntPtr handler, Class_System_String * exceptionName);


UIntPtr
OpenLoggingStorage(UIntPtr sourceHandle, uint32 * flags);

//
///////////////////////////////////////////////////////////////// End of File.
