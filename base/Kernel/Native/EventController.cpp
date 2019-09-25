////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: EventController.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"
#include "eventing.h"

bool GetTracingHandles(UIntPtr * storageHandle,
                       UIntPtr * sourceHandle,
                       UIntPtr * eventTypeHandle);

bool GetMonitoringHandles(UIntPtr * storageHandle,
                          UIntPtr * sourceHandle,
                          UIntPtr * eventTypeHandle);

SOURCE_CONTROLLER SourceController = {NULL, NULL, NULL, NULL, NULL};

char * ConvertToChars(char * dst, bartok_char *src, int32 length)
{
    if (src != NULL) {
        bartok_char *end = src + length;

        while (src < end) {
            *dst++ = (uint8)*src++;
        }
    }
    *dst++ = '\0';
    return dst;
}

void ConvertToChars(char * dst, Class_System_String *arg)
{
    ConvertToChars(dst, &arg->m_firstChar, arg->m_stringLength);
}

void
RegisterRepositoryStorage(PMEMORY_STORAGE storage)
{
    EV_ASSERT(SourceController.SourceRepository == NULL);
    SourceController.SourceRepository = storage;
    RegisterNativeTypes();
}

bool
RegisterStorage(PMEMORY_STORAGE storage)
{
    //  Note the caller of this function needs to assure mutual exclusion

    if (SourceController.SourceRepository == NULL) {

        //  The first storage registered needs to be the type repository

        RegisterRepositoryStorage(storage);

    } else {

        storage->Link = SourceController.StorageList;
        SourceController.StorageList = storage;
    }

    return true;
}


void
UnRegisterStorage(PMEMORY_STORAGE storage)
{
    //  Note the caller of this function needs to assure mutual exclusion

    PMEMORY_STORAGE tmpStorage = SourceController.StorageList;

    EV_ASSERT(tmpStorage != NULL);

    if (tmpStorage == storage) {

        SourceController.StorageList = tmpStorage->Link;

    } else {

        while (tmpStorage->Link != storage) {

            tmpStorage = tmpStorage->Link;
        }

        if (tmpStorage->Link == storage) {

            tmpStorage->Link = storage->Link;
        }
    }
}

void
RegisterExternalController(PEXTERNAL_CONTROLLER_DESCRIPTOR controller)
{
    //  Note the caller of this function needs to assure mutual exclusion

    controller->Link = SourceController.ExternalControllers;
    SourceController.ExternalControllers = controller;
}

void
UnRegisterExternalController(PEXTERNAL_CONTROLLER_DESCRIPTOR controller)
{
    //  Note the caller of this function needs to assure mutual exclusion

    PEXTERNAL_CONTROLLER_DESCRIPTOR tmpController = SourceController.ExternalControllers;

    EV_ASSERT(tmpController != NULL);

    if (tmpController == controller) {

        SourceController.ExternalControllers = tmpController->Link;

    } else {

        while (tmpController->Link != controller) {

            tmpController = tmpController->Link;
        }

        if (tmpController->Link == controller) {

            tmpController->Link = controller->Link;
        }
    }

    //  Insert it to the free llist

    controller->Link = SourceController.FreeControllerList;
    SourceController.FreeControllerList = controller;

}

void
RegisterQueryView(PQUERY_VIEW queryView)
{
    //  Note the caller of this function needs to assure mutula exclusion

    queryView->Link = SourceController.QueryViews;
    SourceController.QueryViews = queryView;
}

void
UnRegisterQueryView(PQUERY_VIEW queryView)
{
    //  Note the caller of this function needs to assure mutual exclusion

    PQUERY_VIEW tmpQueryView = SourceController.QueryViews;

    EV_ASSERT(tmpQueryView != NULL);

    if (tmpQueryView == queryView) {

        SourceController.QueryViews = tmpQueryView->Link;

    } else {

        while (tmpQueryView->Link != queryView) {

            tmpQueryView = tmpQueryView->Link;
        }

        if (tmpQueryView->Link == queryView) {

            tmpQueryView->Link = queryView->Link;
        }
    }

    //  Insert it to the free llist

    queryView->Link = SourceController.QueryViews;
    SourceController.FreeQueryViews = queryView;

}

PQUERY_VIEW AllocateQueryView( )
{
    if (SourceController.FreeQueryViews != NULL) {

        PQUERY_VIEW queryView = SourceController.FreeQueryViews;
        SourceController.FreeQueryViews = queryView->Link;
        RegisterQueryView(queryView);
        return queryView;
    }

    QUERY_VIEW source;

    PMEMORY_HEADER Entry = InternalLogFixedRecord( GetLocalRepositoryHandle(),
        RECORD_EVENT_CONTROLLER,
        0,
        &source,
        sizeof(source));

    if (Entry == NULL) {
        return NULL;
    }

    PQUERY_VIEW newSource = (PQUERY_VIEW)GetUserRecordStructure(Entry);
    RegisterQueryView(newSource);
    return newSource;
}



bool
RegisterSource(PSOURCE_DESCRIPTOR newSource)
{
    //  Note the caller of this function needs to assure mutual exclusion

    newSource->Link = (UIntPtr)SourceController.SourceDescriptors;
    SourceController.SourceDescriptors = newSource;

    return true;
}


//
//  ABI entries
//

UIntPtr Class_Microsoft_Singularity_Eventing_LocalController::
    g_FetchLocalStorage()
{
    return (UIntPtr)GetLocalRepository();
}

bool Class_Microsoft_Singularity_Eventing_LocalController::g_SetRepositoryStorage(UIntPtr storageHandle)
{
    if (SourceController.SourceRepository != NULL) {
        return false;
    }

    RegisterRepositoryStorage(HANDLE_TO_STORAGE(storageHandle));
    return true;
}


UIntPtr Class_Microsoft_Singularity_Eventing_LocalController::
    g_RegisterEventDescriptorInternal(Class_System_String * eventName,
                                      Class_System_String * eventDescription)
{
    return (UIntPtr)RegisterEventDescriptorImplementation(Class_Microsoft_Singularity_Eventing_DataType___string,
                                                          &eventName->m_firstChar,
                                                          eventName->m_stringLength,
                                                          &eventDescription->m_firstChar,
                                                          eventDescription->m_stringLength);
}

UIntPtr Class_Microsoft_Singularity_Eventing_LocalController::
    g_RegisterEventFieldInternal(UIntPtr eventHandle,
        Class_System_String * fieldName,
        uint16 offset,
        uint16 type)
{
    return (UIntPtr) RegisterFieldDescriptorImplementation(
                            Class_Microsoft_Singularity_Eventing_DataType___string,
                            HANDLE_TO_HEADER(eventHandle),
                            &fieldName->m_firstChar,
                            fieldName->m_stringLength,
                            offset,
                            type);
}

UIntPtr Class_Microsoft_Singularity_Eventing_LocalController::
    g_RegisterEventGenericFieldInternal(UIntPtr eventHandle,
                                        Class_System_String * fieldName,
                                        uint16 offset,
                                        uint16 size,
                                        UIntPtr typeFieldDescriptor)
{
    return (UIntPtr)RegisterGenericFieldDescriptorImplementation(
                     Class_Microsoft_Singularity_Eventing_DataType___string,
                     HANDLE_TO_HEADER(eventHandle),
                     &fieldName->m_firstChar,
                     fieldName->m_stringLength,
                     offset,
                     size,
                     typeFieldDescriptor);
}

UIntPtr Class_Microsoft_Singularity_Eventing_LocalController::
    g_RegisterEnumDescriptorInternal(Class_System_String * name,
                                     uint16 type)
{
    return (UIntPtr)RegisterEnumDescriptorImplementation(
                        Class_Microsoft_Singularity_Eventing_DataType___string,
                        &name->m_firstChar,
                        name->m_stringLength,
                        type);
}

UIntPtr Class_Microsoft_Singularity_Eventing_LocalController::
    g_RegisterValueDescriptorInternal(UIntPtr eventHandle,
                                      Class_System_String * name,
                                      uint64 value,
                                      uint8 flagLetter)
{
    return (UIntPtr)RegisterValueDescriptorImplementation(
                         Class_Microsoft_Singularity_Eventing_DataType___string,
                         HANDLE_TO_HEADER(eventHandle),
                         &name->m_firstChar,
                         name->m_stringLength,
                         value,
                         flagLetter);
}


bool
Class_Microsoft_Singularity_Eventing_LocalController::g_RegisterStorageImpl(UIntPtr storageHandle)
{
  return RegisterStorage(HANDLE_TO_STORAGE(storageHandle));
}
void
Class_Microsoft_Singularity_Eventing_LocalController::g_UnRegisterStorageImpl(UIntPtr storageHandle)
{
  UnRegisterStorage(HANDLE_TO_STORAGE(storageHandle));
}

UIntPtr
Class_Microsoft_Singularity_Eventing_LocalController::g_AllocateSourceHandleImpl(
    Class_System_String * sourceName)
{
    SOURCE_DESCRIPTOR source = {NULL, 0};
    PVOID ExtendedBuffer;

    PMEMORY_HEADER Entry = InternalLogRecord( GetLocalRepositoryHandle(),
        RECORD_EVENT_SOURCE,
        0,
        &source,
        sizeof(source),
        &ExtendedBuffer,
        sourceName->m_stringLength + 1);

    if (Entry != NULL) {

        PSOURCE_DESCRIPTOR newSource = (PSOURCE_DESCRIPTOR)GetUserRecordStructure(Entry);

        ConvertToChars((char *)ExtendedBuffer, sourceName);
        RegisterSource(newSource);
        CommitEventEntry(Entry);
    }

    return (UIntPtr)Entry;
}

PSOURCE_DESCRIPTOR
GetSourceFromHandle(UIntPtr sourceHandle)
{
    if (sourceHandle == 0) {

        return NULL;
    }

    PMEMORY_HEADER entry = HANDLE_TO_HEADER(sourceHandle);

    if (entry->Flags == RECORD_EVENT_SOURCE) {

        return (PSOURCE_DESCRIPTOR)GetUserRecordStructure(entry);
    }
    return NULL;
}

UIntPtr
AllocateNativeSourceHandle(char * sourceName)
{
    SOURCE_DESCRIPTOR source = {0,NULL,0,0,0,0,0,0};

    PVOID ExtendedBuffer;
    uint16 sourceLen = strlen(sourceName) + 1;

    PMEMORY_HEADER Entry = InternalLogRecord( GetLocalRepositoryHandle(),
        RECORD_EVENT_SOURCE,
        0,
        &source,
        sizeof(source),
        &ExtendedBuffer,
        sourceLen);

    if (Entry != NULL) {

        PSOURCE_DESCRIPTOR newSource = (PSOURCE_DESCRIPTOR)GetUserRecordStructure(Entry);
        memcpy(ExtendedBuffer, sourceName, sourceLen);

        RegisterSource(newSource);
        CommitEventEntry(Entry);
    }

    return (UIntPtr)Entry;
}

UIntPtr
RegisterNativeSource(char * sourceName, UIntPtr storageHandle, uint32 controlFlags)
{
    UIntPtr sourceHandle = AllocateNativeSourceHandle(sourceName);

    if (sourceHandle != 0) {

        Class_Microsoft_Singularity_Eventing_LocalController::g_RegisterSourceStorageImpl(
            sourceHandle, storageHandle, controlFlags);

        if (storageHandle != 0) {

            RegisterStorage(HANDLE_TO_STORAGE(storageHandle));
        }

    }

    return sourceHandle;
}

void
Class_Microsoft_Singularity_Eventing_LocalController::g_RegisterSourceStorageImpl(
    UIntPtr sourceHandle,
    UIntPtr storageHandle,
    uint32 controlFlags)
{
    PSOURCE_DESCRIPTOR Source;

    Source = (PSOURCE_DESCRIPTOR)GetUserRecordStructure(HANDLE_TO_HEADER(sourceHandle));

    if (Source) {
        Source->StorageHandle = storageHandle;
        Source->EventTypeHandle = 0;
        Source->DebuggerBufferAddress = 0;
        Source->Count = 0;
        Source->EntrySize = 0;
        Source->ControlFlags = controlFlags;
    }
}

void
Class_Microsoft_Singularity_Eventing_LocalController::g_RegisterActiveSourceImpl(
    UIntPtr sourceHandle,
    UIntPtr eventTypeHandle,
    UIntPtr debuggerBufferAddress,
    uint16 count,
    uint16 entrySize)
{
    PSOURCE_DESCRIPTOR Source;

    Source = (PSOURCE_DESCRIPTOR)GetUserRecordStructure(HANDLE_TO_HEADER(sourceHandle));

    if (Source) {

        Source->StorageHandle = 0;
        Source->EventTypeHandle = eventTypeHandle;
        Source->DebuggerBufferAddress = debuggerBufferAddress;
        Source->Count = count;
        Source->EntrySize = entrySize;
        Source->ControlFlags = 0xFFFF0000;
    }
}

void
Class_Microsoft_Singularity_Eventing_LocalController::g_UnRegisterSourceImpl(
    UIntPtr sourceHandle)
{
    PSOURCE_DESCRIPTOR Source;

    Source = (PSOURCE_DESCRIPTOR)GetUserRecordStructure(HANDLE_TO_HEADER(sourceHandle));

    if (Source) {

        EV_ASSERT(Source->StorageHandle == 0);
        Source->StorageHandle = 0;
    }
}


bool Class_Microsoft_Singularity_Eventing_LocalController::
    g_GetControllerHandle(UIntPtr *storageHandle, UIntPtr *contextHandle)
{
    // ????? Some correct values are needed that would allow switching to the right context in debugger
    // Note these values are not being accessed programatically. Correct contracts should be established
    // to query entries cross SIPs

    *storageHandle = (UIntPtr)&SourceController;
    *contextHandle = 0;
    return true;
}


bool Class_Microsoft_Singularity_Eventing_LocalController::
g_QueryNativeSourceInfo(UIntPtr sourceHandle,
                            UIntPtr * storageHandle,
                            bartok_char * bufferName,
                            uint16 bufferSize)
{
    PMEMORY_HEADER Entry = HANDLE_TO_HEADER(sourceHandle);
    PSOURCE_DESCRIPTOR source = (PSOURCE_DESCRIPTOR)GetUserRecordStructure(Entry);

    *storageHandle = source->StorageHandle;

    char * src = (char *)(source + 1);

    if ((bufferName != NULL) && (bufferSize != 0)) {

        while ((bufferSize != 0) && (*src)) {

            *bufferName++ = *src++;
            bufferSize -= sizeof(bartok_char);
        }

        if (bufferSize == 0) {

            // Move back one position to insert the null terminator.
            // We have at least this character in the buffer due to the test two levels above

            bufferSize -= sizeof(bartok_char);
        }

        *bufferName = 0;
    }

    return true;
}


int Class_Microsoft_Singularity_Eventing_LocalController::
g_QuerySystemSources(UIntPtr * sourceHandles,
                              uint16 arraySize)
{

    int totalSources = 0;

    PSOURCE_DESCRIPTOR source = SourceController.SourceDescriptors;

    while (source != NULL) {

        if (totalSources < arraySize) {

            sourceHandles[totalSources] = (UIntPtr)((PMEMORY_HEADER)source - 1);
        }

        source = (PSOURCE_DESCRIPTOR)source->Link;
        totalSources += 1;
    }

    return totalSources;
}

bool Class_Microsoft_Singularity_Eventing_Controller::
    g_GetSharedSourceHandlesInternal(uint32 infoId,
                                     UIntPtr * storageHandle,
                                     UIntPtr * sourceHandle,
                                     UIntPtr * eventTypeHandle)
{
    switch (infoId) {
        case Class_Microsoft_Singularity_Eventing_Controller_TracingInfo:
            return GetTracingHandles(storageHandle, sourceHandle, eventTypeHandle);

        case Class_Microsoft_Singularity_Eventing_Controller_MonitoringInfo:
            return GetMonitoringHandles(storageHandle, sourceHandle, eventTypeHandle);
    }

    return false;
}



//
///////////////////////////////////////////////////////////////// End of File.

