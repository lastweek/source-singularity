////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Monitoring.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"
#include "eventing.h"

#define MONITORING_BUFFER_SIZE (6 * 1024 * 1024)
#define MONITORING_TEXT_SIZE   (2 * 1024 * 1024)

UIntPtr MonitoringStorageHandle = 0;
PSOURCE_DESCRIPTOR MonitoringSource = NULL;
UIntPtr MonitoringTypeHandle = 0;

const UINT32 Monitoring_ControlFlag_Active = 0x00010000;

void
Class_Microsoft_Singularity_Monitoring::
g_Initialize()
{

#if SINGULARITY_KERNEL

    g_InitPages((UIntPtr)(MONITORING_BUFFER_SIZE));

    if (c_buffer != NULL) {

        MonitoringStorageHandle = Class_Microsoft_Singularity_Eventing_MemoryStorage::
            g_MemoryStorageCreateImpl(MEMORY_STORAGE_FLAGS_RECYCLE_MEMORY,
                                      (uint8 *)c_buffer,
                                      (uint32)MONITORING_BUFFER_SIZE,
                                      0);

        if (MonitoringStorageHandle) {

            UIntPtr sourceHandle = RegisterNativeSource("Monitoring",
                                                        MonitoringStorageHandle,
                                                        Monitoring_ControlFlag_Active);

            MonitoringSource = GetSourceFromHandle(sourceHandle);
        }
    }

#elif SINGULARITY_PROCESS

    Struct_Microsoft_Singularity_V1_Services_ProcessService::
        g_GetSharedSourceHandles(Class_Microsoft_Singularity_Eventing_Controller_MonitoringInfo,
                                 &MonitoringStorageHandle,
                                 (UIntPtr *)&MonitoringSource,
                                 &MonitoringTypeHandle);

#else
#error "File should be compiled with SINGULARITY_KERNEL or SINGULARITY_PROCESS"
#endif
}

bool GetMonitoringHandles(UIntPtr * storageHandle,
                          UIntPtr * sourceHandle,
                          UIntPtr * eventTypeHandle)
{
    *storageHandle = MonitoringStorageHandle;
    *sourceHandle = (UIntPtr)MonitoringSource;
    *eventTypeHandle = MonitoringTypeHandle;
    return true;
}


bool __inline IsMonitoringEnabled()
{
    return ((MonitoringSource != NULL) &&
            (MonitoringSource->ControlFlags & Monitoring_ControlFlag_Active));
}


void Class_Microsoft_Singularity_Monitoring::
g_Log(uint16 provider, uint16 type)
{
    if (IsMonitoringEnabled()) {

        Struct_Microsoft_Singularity_ThreadContext *threadContext =
            Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext();

        MONITORING_ENTRY entry = {threadContext->processId, provider,type,0,0,0,0,0,0};
        InternalLogFixedRecord(MonitoringStorageHandle,
                               MonitoringSource->ControlFlags,
                               MonitoringTypeHandle,
                               &entry,
                               sizeof(entry));
    }
}

void Class_Microsoft_Singularity_Monitoring::
g_Log(uint16 provider, uint16 type, uint16 version,
      uint32 a0, uint32 a1, uint32 a2, uint32 a3, uint32 a4)
{
    if (IsMonitoringEnabled()) {

        Struct_Microsoft_Singularity_ThreadContext *threadContext =
            Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext();

        MONITORING_ENTRY entry = {threadContext->processId, provider,type,version,a0,a1,a2,a3,a4};
        InternalLogFixedRecord(MonitoringStorageHandle,
                               MonitoringSource->ControlFlags,
                               MonitoringTypeHandle,
                               &entry,
                               sizeof(entry));
    }
}

void Class_Microsoft_Singularity_Monitoring::
g_Log(uint16 provider, uint16 type, Class_System_String *s)
{
    if (IsMonitoringEnabled()) {

        Struct_Microsoft_Singularity_ThreadContext *threadContext =
            Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext();

        MONITORING_ENTRY entry = {threadContext->processId, provider,type,0,0,0,0,0,0,1};

        Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
            {s->m_stringLength,
             sizeof(char),
             Class_Microsoft_Singularity_Eventing_DataType___string,
             &s->m_firstChar}};

        InternalLogVariableRecord(true,
                                  MonitoringStorageHandle,
                                  MonitoringSource->ControlFlags,
                                  MonitoringTypeHandle,
                                  &entry,
                                  sizeof(entry),
                                  sizeof(array)/sizeof(array[0]),
                                  array);
    }
}


bool Class_Microsoft_Singularity_Monitoring::
g_isActive()
{
    return IsMonitoringEnabled();
}

void Class_Microsoft_Singularity_Monitoring::
g_setActive(bool active)
{
    if (MonitoringSource != NULL) {
        if (active) {
            MonitoringSource->ControlFlags |= Monitoring_ControlFlag_Active;
        } else {
            MonitoringSource->ControlFlags &= ~Monitoring_ControlFlag_Active;
        }
    }
}

int Class_Microsoft_Singularity_Monitoring::
g_FillLogEntry(Struct_Microsoft_Singularity_Monitoring_LogEntry * log,
               UINT64 * min_counter)
{
    //
    //  TODO: impplement it to fix monnet
    //
    return 0;
}

int Class_Microsoft_Singularity_Monitoring::
g_FillTextEntry(uint8 * src, UINT64 counter, uint8 * dst, int max_size)
{
    //
    //  TODO: impplement it to fix monnet
    //

    return 0;
}

//
///////////////////////////////////////////////////////////////// End of File.
