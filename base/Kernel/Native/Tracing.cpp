////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Tracing.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"
#include "eventing.h"

UIntPtr TracingStorageHandle = 0;
const UINT32 Tracing_ControlFlag_Active = 0x00010000;
PSOURCE_DESCRIPTOR TracingSource = NULL;
UIntPtr TracingTypeHandle = 0;

uint16
inline
GetCurrentProcessId()
{
    return Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext()->processId;
}

void
Class_Microsoft_Singularity_Tracing::
g_Initialize()
{
#if SINGULARITY_KERNEL

    Class_Microsoft_Singularity_Hal_Platform *platform = Class_Microsoft_Singularity_Hal_Platform::c_thePlatform;

    InitializeRegistrationSystem((void *)platform->LogTextBuffer,
                                  platform->LogTextSize);

    TracingStorageHandle = Class_Microsoft_Singularity_Eventing_MemoryStorage::
        g_MemoryStorageCreateImpl(MEMORY_STORAGE_FLAGS_RECYCLE_MEMORY,
                                  (uint8 *)platform->LogRecordBuffer,
                                  (uint32)platform->LogRecordSize,
                                  0);
    if (TracingStorageHandle) {

        UIntPtr sourceHandle = RegisterNativeSource("LegacyTracing",
                                                    TracingStorageHandle,
                                                    Tracing_ControlFlag_Active);
        TracingSource = GetSourceFromHandle(sourceHandle);
    }


#elif SINGULARITY_PROCESS

    Struct_Microsoft_Singularity_V1_Services_ProcessService::
        g_GetSharedSourceHandles(Class_Microsoft_Singularity_Eventing_Controller_TracingInfo,
                                 &TracingStorageHandle,
                                 (UIntPtr *)&TracingSource,
                                 &TracingTypeHandle);

#else
#error "File should be compiled with SINGULARITY_KERNEL or SINGULARITY_PROCESS"
#endif
}

bool __inline IsTracingEnabled()
{
    return ((TracingSource != NULL) &&
            (TracingSource->ControlFlags & Tracing_ControlFlag_Active));
}



bool GetTracingHandles(UIntPtr * storageHandle,
                       UIntPtr * sourceHandle,
                       UIntPtr * eventTypeHandle)
{
    *storageHandle = TracingStorageHandle;
    *sourceHandle = (UIntPtr)TracingSource;
    *eventTypeHandle = TracingTypeHandle;
    return true;
}

uint8 * CompareExchange(uint8 **dest, uint8 *exch, uint8 *comp)
{
    return (uint8 *) InterlockedCompareExchangePointer((PVOID *) dest,
                                                       (PVOID) exch,
                                                       (PVOID) comp);
}

UIntPtr
Class_Microsoft_Singularity_Tracing::
g_GetSystemTracingStorageHandle()
{
    return TracingStorageHandle;
}


void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity, GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              0,0,0,0,0,0};
    InternalLogFixedRecord(TracingStorageHandle,
                           TracingSource->ControlFlags,
                           TracingTypeHandle,
                           &entry,
                           sizeof(entry));
}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity, GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,0,0,0,0,0,0,0,0};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);

}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      UIntPtr arg0)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity, GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1, arg0,0,0,0,0,0,0,0};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      UIntPtr arg0, UIntPtr arg1)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity, GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1, arg0,arg1,0,0,0,0, 0,0};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      UIntPtr arg0, UIntPtr arg1, UIntPtr arg2)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,arg0,arg1,arg2,0,0,0,0,0};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      UIntPtr arg0, UIntPtr arg1, UIntPtr arg2,
      UIntPtr arg3)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,arg0,arg1,arg2,arg3,0,0,0,0};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      UIntPtr arg0, UIntPtr arg1, UIntPtr arg2,
      UIntPtr arg3, UIntPtr arg4)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,arg0,arg1,arg2,arg3,arg4,0,0,0};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      UIntPtr arg0, UIntPtr arg1, UIntPtr arg2,
      UIntPtr arg3, UIntPtr arg4, UIntPtr arg5)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,arg0,arg1,arg2,arg3,arg4,arg5,0,0};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      Class_System_String *arg0)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,0,0,0,0,0,0,2,0};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar},
        {arg0->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &arg0->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);

}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      Class_System_String *arg0,
      UIntPtr arg1)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,arg1,0,0,0,0,0,2,0};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar},
        {arg0->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &arg0->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);

}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      Class_System_String *arg0,
      UIntPtr arg1, UIntPtr arg2)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,arg1,arg2,0,0,0,0,2,0};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar},
        {arg0->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &arg0->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);

}

void Class_Microsoft_Singularity_Tracing::
g_Log(uint8 severity,
      Class_System_String *msg,
      Class_System_String *arg0,
      Class_System_String *arg1)
{
    if (!IsTracingEnabled()) return;

    LEGACY_LOG_ENTRY entry = {severity,GetCurrentProcessId(), (UIntPtr)_ReturnAddress(),
                              1,0,0,0,0,0,0,2,3};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {msg->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &msg->m_firstChar},
        {arg0->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &arg0->m_firstChar},
        {arg1->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &arg1->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}


void LogExceptionInfo(UIntPtr throwFrom, UIntPtr handler, Class_System_String * exceptionName)
{
    if (!IsTracingEnabled()) return;

    LOG_EXCEPTION entry = {throwFrom, handler, 1};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {exceptionName->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &exceptionName->m_firstChar}};

    InternalLogVariableRecord(true,
                              TracingStorageHandle,
                              TracingSource->ControlFlags,
                              TracingTypeHandle,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}



//
///////////////////////////////////////////////////////////////// End of File.
