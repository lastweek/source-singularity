////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   GSTracing.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"
#include "eventing.h"

void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogFunction(uint32 funcNo, UIntPtr eip)
{
    GC_FUNCTION entry = {funcNo, eip};
    InternalLogFixedRecord((UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_TypeStorageHandle,
                           0, Handle_GC_FUNCTION, &entry, sizeof(entry));
}


void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogAllocation(int32 threadId, UIntPtr objectAddress, uint32 stkNo)
{
    GC_ALLOCATION entry = {threadId, stkNo, objectAddress};
    InternalLogFixedRecord((UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_StorageHandle,
                            0, Handle_GC_ALLOCATION, &entry, sizeof(entry));
}

void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogStack(uint32 stackNo, uint32 typeNo, UIntPtr size, uint32 stackSize, uint32 * funcIDs)
{
    GC_STACK entry = {stackNo, typeNo, (uint32)size, 1};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {(uint16)(stackSize * sizeof(uint32)),
         sizeof(uint32),
         Class_Microsoft_Singularity_Eventing_DataType___arrayType,
         funcIDs}};

    InternalLogVariableRecord(true,
                              (UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_TypeStorageHandle,
                              0,
                              Handle_GC_STACK,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogInterval(uint64 Delta)
{
    GC_INTERVAL entry = {Delta};
    InternalLogFixedRecord((UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_StorageHandle,
                           0, Handle_GC_INTERVAL, &entry, sizeof(entry));
}


void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogType(uint32 typeId, Class_System_String * typeName)
{
    GC_TYPE entry = {typeId, 1};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {typeName->m_stringLength,
         sizeof(char),
         Class_Microsoft_Singularity_Eventing_DataType___string,
         &typeName->m_firstChar}};

    InternalLogVariableRecord(true,
                              (UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_TypeStorageHandle,
                              0,
                              Handle_GC_TYPE,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogObject(uint32 ArraySize, UIntPtr * objectParameters)
{
    GC_OBJECT entry = {1};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {(uint16)(ArraySize * sizeof(UIntPtr)),
         sizeof(UIntPtr),
         Class_Microsoft_Singularity_Eventing_DataType___arrayType,
         objectParameters}};

    InternalLogVariableRecord(true,
                              (UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_StorageHandle,
                              0,
                              Handle_GC_OBJECT,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogGenerations(int maxGeneration, int * generations)
{
    GC_GENERATIONS entry = {1};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {(uint16)(maxGeneration * sizeof(int32)),
         sizeof(int32),
         Class_Microsoft_Singularity_Eventing_DataType___arrayType,
         generations}};

    InternalLogVariableRecord(true,
                              (UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_StorageHandle,
                              0,
                              Handle_GC_GENERATIONS,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}

void Class_Microsoft_Singularity_GCProfilerLogger_ProfilerBuffer::
g_LogRoots(uint32 ArraySize, UIntPtr * objectRoots)
{
    GC_ROOTS entry = {1};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {(uint16)(ArraySize * sizeof(UIntPtr)),
         sizeof(UIntPtr),
         Class_Microsoft_Singularity_Eventing_DataType___arrayType,
         objectRoots}};

    InternalLogVariableRecord(true,
                              (UIntPtr)Class_Microsoft_Singularity_GCProfilerLogger::c_StorageHandle,
                              0,
                              Handle_GC_ROOTS,
                              &entry,
                              sizeof(entry),
                              sizeof(array)/sizeof(array[0]),
                              array);
}


//
///////////////////////////////////////////////////////////////// End of File.
