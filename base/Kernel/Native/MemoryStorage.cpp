////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   MemoryStorage.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"
#include "eventing.h"

#ifndef SINGULARITY_KERNEL
void DebugPrintEvent(UIntPtr eventHandle)
{
    Class_Microsoft_Singularity_Eventing_SystemControllerProxy::g_DebugPrintLogEntry(eventHandle);
}
#endif

uint32
MemoryStorageGetNextGeneration(PMEMORY_STORAGE Storage)
{
    return (uint32)InterlockedIncrement((volatile INT32* )&Storage->Generation);
}

PMEMORY_HEADER
MemoryStorageAdvanceCursor(PMEMORY_STORAGE Storage,
                           PMEMORY_ZONE CurrentCursor,
                           uint16 size)
{
    PMEMORY_ZONE NewCursor;
    PMEMORY_ZONE CapturedCursor = Storage->ZoneCursor;
    BOOL Reycled = false;

    NewCursor = CurrentCursor;

    if (NewCursor == NULL) {

        NewCursor = Storage->MemoryZoneLink;
    }

    for (NewCursor = NewCursor->Link; NewCursor != CurrentCursor; NewCursor = NewCursor->Link) {

        if (NewCursor == NULL) {

            //  Restart from the begining of the storage
            //  Make sure the policy allows this

            if (Storage->Flags & MEMORY_STORAGE_FLAGS_RECYCLE_MEMORY) {

                if (Reycled) {

                    // Every zone has been tried for this allocation
                    // return back the failure.

                    return NULL;
                }

                if (Storage->Flags & MEMORY_STORAGE_FLAGS_BREAK_ON_RECYCLE) {

                    // If we trap here, there is a request to stop before over-writing
                    // any buffer contents.  That is about to happen, so this is the
                    // last chance to retrieve those contents before they are lost.
                    //
                    // Then proceed from this breakpoint.

                    __debugbreak();
                }

                Reycled = true;

                NewCursor = Storage->MemoryZoneLink;

            } else {

                // We must return here failure, as recycling the memory for older events
                // is not permited

                return NULL;
            }

        }

        if (IsZoneCompleted(NewCursor)) {

            RecycleZone(NewCursor);
        }

        PMEMORY_HEADER Event = AllocateEventEntry(NewCursor, size);
        if (Event != NULL) {

            // we were successfuly in using this zone, set it as current cursor
            // It is possible some other thread already did it, or even moved far ahead
            // But this should not be a problem as there are no guarantees wrt. ordering
            // in the storage

            InterlockedCompareExchangePointer((PVOID *)&Storage->ZoneCursor,
                    (PVOID)NewCursor,
                    (PVOID)CapturedCursor);
            return Event;
        }
    }

    return NULL;
}


uint32
CaptureStackTrace(UIntPtr * StackArray, UINT MaxStackSize)
{

    uint32 Index;
    UIntPtr CurrentFrame = Class_Microsoft_Singularity_Isal_Isa::g_GetFramePointer();
    UIntPtr CallerFrame = Class_Microsoft_Singularity_Isal_Isa::g_GetFrameCallerFrame(CurrentFrame);

    Struct_Microsoft_Singularity_ProcessorContext *processorContext =
        Class_Microsoft_Singularity_Processor::g_GetCurrentProcessorContext();

    if ((CurrentFrame <= (UIntPtr)processorContext->cpuRecord.interruptStackBegin) &&
        (CurrentFrame > (UIntPtr)processorContext->cpuRecord.interruptStackLimit)) {

        //  Capture the interrupte stack. Always check against the limits
        //  before fetching the next frame

        for (Index = 0; (CallerFrame != 0) && Index < MaxStackSize; Index += 1) {

            if ((CallerFrame > (UIntPtr)processorContext->cpuRecord.interruptStackBegin) ||
                (CallerFrame < (UIntPtr)processorContext->cpuRecord.interruptStackLimit)) {

                return Index;
            }
            StackArray[Index] = Class_Microsoft_Singularity_Isal_Isa::g_GetFrameReturnAddress(CallerFrame);
            CallerFrame = Class_Microsoft_Singularity_Isal_Isa::g_GetFrameCallerFrame(CallerFrame);
        }
        return Index;
    }


    for (Index = 0; (CallerFrame != 0) && Index < MaxStackSize; Index += 1) {

        StackArray[Index] = Class_Microsoft_Singularity_Isal_Isa::g_GetFrameReturnAddress(CallerFrame);
        CallerFrame = Class_Microsoft_Singularity_Isal_Isa::g_GetFrameCallerFrame(CallerFrame);
    }
    return Index;
}



PMEMORY_HEADER
InternalLogRecord(UIntPtr StorageHandle,
    uint32 Flags,
    UIntPtr eventType,
    PVOID Buffer,
    uint32 size,
    PVOID * ExtendedBuffer,
    uint32 ExtendedSize )
{
    if (StorageHandle == 0) return NULL;

    PMEMORY_STORAGE Storage = (PMEMORY_STORAGE)StorageHandle;

    UIntPtr Stacks[RECORD_MAXSTACKSIZE];
    uint32 StackSize = 0;
    uint32 allocSize = (uint32)ROUND_UP_TO_POWER2(size, sizeof(UIntPtr));

    if (Flags & RECORD_STACK_TRACES) {

        StackSize = CaptureStackTrace(Stacks, RECORD_MAXSTACKSIZE);

        if (StackSize) {

            // There is no point to save the eip of the current function in the database
            // since is redundant information. Reuse instead that slot to keep the stack size

            Stacks[0] = (UIntPtr)(StackSize - 1);

            // Convert to memory usage

            StackSize *= sizeof(UIntPtr);
        } else {

            // clear the flag as there is no stack available
            Flags &= ~RECORD_STACK_TRACES;
        }
    }

    PMEMORY_ZONE Zone = Storage->ZoneCursor;

    if (Zone == NULL) {

        Zone = Storage->MemoryZoneLink;
    }

    UINT32 EntrySize = GetRecordHeaderSize (Flags, StackSize);

    PMEMORY_HEADER Event = AllocateEventEntry(Zone,
            (uint16)(EntrySize + allocSize + ExtendedSize - sizeof(MEMORY_HEADER)));

    if (Event == NULL) {

        //  The zone is filled up, advance the cursor to the next zone

        Event = MemoryStorageAdvanceCursor(Storage, Zone,
            (uint16)(EntrySize + allocSize + ExtendedSize - sizeof(MEMORY_HEADER)));
    }

    if (Event != NULL) {

        // Copy the entry flags, which also include the layout description

        Event->Flags = (uint16)Flags;
        Event->Type = eventType;
        // Handle the stack traces, if present

        UCHAR * Dest = (UCHAR *)GetRecordInternalStructure(Event, RECORD_STACK_TRACES);

        if (Dest != NULL) {

            memcpy(Dest, Stacks, StackSize);
        }

        //  Copy the remaining portion provided by the user to the buffer

        if (Buffer) {

            memcpy((char *)Event + EntrySize, Buffer, size);
        }

        if (ExtendedSize != 0) {

            *ExtendedBuffer = (char *)Event + EntrySize + allocSize;
        }

    }

    return Event;
}

PMEMORY_HEADER
InternalLogFixedRecord(UIntPtr StorageHandle,
    uint32 Flags,
    UIntPtr eventType,
    PVOID Buffer,
    uint32 size)
{
    PMEMORY_HEADER entry = InternalLogRecord(StorageHandle, Flags, eventType, Buffer, size, NULL, 0);

    if (entry != NULL) {

        if (Flags & Class_Microsoft_Singularity_Eventing_EventSource_CAPTURE_DEBUG_PRINT){

            DebugPrintEvent((UIntPtr)entry);
        }

        CommitEventEntry(entry);
    }

    return entry;
}

PMEMORY_HEADER
InternalLogVariableRecord(
    bool doCommit,
    UIntPtr StorageHandle,
    uint32 Flags,
    UIntPtr eventType,
    PVOID Buffer,
    uint32 size,
    int32 variableItemsCount,
    Struct_Microsoft_Singularity_Eventing_ArrayType * variableItems)
{
    if (StorageHandle == 0) return NULL;

    PVOID ExtendedBuffer;
    int i;
    int arrayDescriptorSize = variableItemsCount * sizeof(uint16);

    int32 extendedSize =  arrayDescriptorSize;

    for (i = 0; i < variableItemsCount; i++) {

        extendedSize += (int32)variableItems[i].Length;

        if ((variableItems[i].Type == EVENT_FIELD_TYPE_string)
                ||
            (variableItems[i].Type == EVENT_FIELD_TYPE_szChar)) {

            // Account for the null terminator that ConvertToChars automatically
            // inserts to the string. For szChar data, the string will also have one
            // null character at the end, that has not been encounted for

            extendedSize += 1;
        }
    }

    PMEMORY_HEADER Entry = InternalLogRecord(StorageHandle,
                                             Flags,
                                             eventType,
                                             Buffer,
                                             size,
                                             &ExtendedBuffer,
                                             extendedSize);

    if (Entry == NULL) {
        return Entry;
    }

    if (extendedSize > 0) {

        //  Note the test for extendedSize. This is the only case where we are
        //  allowed to add something after calling InternalLogRecord. We are also required
        //  explicitely commit the entry when we're done

        for (i = 0; i < variableItemsCount; i++) {

            //
            //  For strings, the mechanism wil automatically extend the buffer with one
            //  extra character to include the null terminator. The length in the field
            //  should be however consistent and report the correct length of the buffer
            //

            if (variableItems[i].Type == EVENT_FIELD_TYPE_string) {

                // Account for the null terminator that ConvertToChars automatically
                // inserts to the string.

                unsigned short adjustedLength = variableItems[i].Length + 1;

                C_ASSERT(sizeof(adjustedLength) == sizeof(variableItems[i].Length));
                memcpy(ExtendedBuffer, &adjustedLength, sizeof(adjustedLength));
                ExtendedBuffer = (char *)ExtendedBuffer + sizeof(variableItems[i].Length);


                //  If this was a bartok string, convert it to ascii

                ExtendedBuffer = ConvertToChars((char *)ExtendedBuffer,
                                                (bartok_char *)variableItems[i].Buffer,
                                                (int32)variableItems[i].Length);


                EV_ASSERT(ExtendedBuffer <= (PVOID)((char*)Entry + Entry->Size ));

            } else  if (variableItems[i].Type == EVENT_FIELD_TYPE_szChar) {

                // Account for the null terminator that is automatically
                // inserted to the string.

                unsigned short adjustedLength = variableItems[i].Length + 1;

                //
                //  Save the total size in bytes and save it to the entry. Move the pointer forward
                //

                C_ASSERT(sizeof(adjustedLength) == sizeof(variableItems[i].Length));
                memcpy(ExtendedBuffer, &adjustedLength, sizeof(adjustedLength));
                ExtendedBuffer = (char *)ExtendedBuffer + sizeof(adjustedLength);

                //
                //  Copy now the actual content of the buffer
                //

                memcpy(ExtendedBuffer, variableItems[i].Buffer, (int32)variableItems[i].Length);
                ExtendedBuffer = (char *)ExtendedBuffer + variableItems[i].Length;
                *(char *)ExtendedBuffer = (char)0;
                ExtendedBuffer = (char *)ExtendedBuffer + 1;

            } else {

                //
                //  Save the length of the data and advance the pointer
                //

                memcpy(ExtendedBuffer, &variableItems[i].Length, sizeof(variableItems[i].Length));
                ExtendedBuffer = (char *)ExtendedBuffer + sizeof(variableItems[i].Length);

                // nothing else to do here, just copy the content and advance the pointer

                memcpy(ExtendedBuffer, variableItems[i].Buffer, (int32)variableItems[i].Length);
                ExtendedBuffer = (char *)ExtendedBuffer + variableItems[i].Length;
            }

            EV_ASSERT(ExtendedBuffer <= (PVOID)((char*)Entry + Entry->Size ));

        }

    }

    if (Flags & Class_Microsoft_Singularity_Eventing_EventSource_CAPTURE_DEBUG_PRINT){

        DebugPrintEvent((UIntPtr)Entry);
    }

    if (doCommit) {

        CommitEventEntry(Entry);
    }


    return Entry;
}


UIntPtr
OpenLoggingStorage(UIntPtr sourceHandle, uint32 * flags)
{
    if (sourceHandle == 0) return 0;

    PSOURCE_DESCRIPTOR source = HANDLE_TO_SOURCE(sourceHandle);
    if (((source->ControlFlags & (*flags)) >> 16) == 0) return 0;

    *flags |= source->ControlFlags;
    return source->StorageHandle;
}


PMEMORY_ZONE
GetNextZone(PQUERY_VIEW view)
{
    if (view->StartZone == NULL) {
        return NULL;
    }

    for (;;) {

        if (view->Forward) {

            view->CurrentZone = view->CurrentZone->Link;

            if (view->CurrentZone == NULL) {

                view->CurrentZone = view->Storage->MemoryZoneLink;
            }
        } else {

            view->CurrentZone = view->CurrentZone->BkLink;

            if (view->CurrentZone == NULL) {

                view->CurrentZone = view->Storage->BkLink;
            }
        }

        if (view->CurrentZone == view->StartZone) {

            return NULL;
        }

        //  ??? handle the generation wrap

        if (view->CurrentZone->Generation <= view->QueryGeneration) {

            view->CurrentEntryIndex = 0;
            view->ZoneGeneration = view->CurrentZone->Generation;
            return view->CurrentZone;
        }

    }
}

PQUERY_VIEW
CreateQuery(UIntPtr storageHandle, bool forward)
{
    PQUERY_VIEW queryView = AllocateQueryView( );

    if (queryView) {

        queryView->Storage = HANDLE_TO_STORAGE(storageHandle);
        queryView->Forward = forward;
        queryView->QueryGeneration = queryView->Storage->Generation;

        queryView->CurrentZone = NULL;
        queryView->ZoneGeneration = 0;
        queryView->CurrentEntry = NULL;
        queryView->CurrentEntryIndex = 0;
        queryView->EndOfBuffer = false;

        if (forward) {

            queryView->StartZone = queryView->Storage->ZoneCursor;

            if (queryView->StartZone != NULL) {

                queryView->StartZone = queryView->StartZone->Link;
            }

            if (queryView->StartZone == NULL) {

                queryView->StartZone  = queryView->Storage->MemoryZoneLink;
            }

        } else {

            queryView->StartZone = queryView->Storage->ZoneCursor;

            if (queryView->StartZone == NULL) {

                queryView->StartZone  = queryView->Storage->BkLink;
            }
        }

        queryView->CurrentZone = queryView->StartZone;
        queryView->QueryReset = true;

   }

    return queryView;
}

PMEMORY_HEADER
GetNextStorageEntry(PQUERY_VIEW queryView)
{
    PMEMORY_HEADER Entry;

    if (queryView->EndOfBuffer) {

        return NULL;
    }

    if (queryView->CurrentEntry) {

        Entry = GetNextEntry(queryView);

        if (Entry) {

            return Entry;
        }
    }

    PMEMORY_ZONE zone;
    if (queryView->QueryReset) {

        zone = queryView->StartZone;
        queryView->QueryReset = false;
        queryView->ZoneGeneration = zone->Generation;
        queryView->CurrentEntryIndex = 0;

    } else {

        zone = GetNextZone(queryView);
    }

    while (zone != NULL) {

        queryView->CurrentEntry = GetFirstEntry(zone, queryView->Forward);

        if (queryView->CurrentEntry) {
            return queryView->CurrentEntry;
        }

        zone = GetNextZone(queryView);
    }

    queryView->EndOfBuffer = true;

    return NULL;
}

//
//  ABI calls for Eventing.MemoryStorage
//

UIntPtr Class_Microsoft_Singularity_Eventing_MemoryStorage::
g_MemoryStorageCreateImpl(uint32 Flags, UCHAR * InitialBuffer, uint32 BufferSize, uint32 ZoneSize)
{
    if (BufferSize <= sizeof(MEMORY_STORAGE)) {

        return 0;
    }

    PMEMORY_STORAGE Storage = (PMEMORY_STORAGE)InitialBuffer;
    Storage->StorageSize = 0;
    Storage->MemoryZoneLink = NULL;
    Storage->ZoneCursor = NULL;
    Storage->Flags = Flags;
    Storage->BkLink = NULL;
    Storage->Generation = 0;

    ZoneSize = (uint32)ROUND_UP_TO_POWER2(ZoneSize, EV_ZONE_ALIGNMENT);

    if (((Flags & 0xF) == MEMORY_STORAGE_FLAGS_PERMANENT)
            ||
        ((Flags & 0xF) == MEMORY_STORAGE_FLAGS_ACTIVE_STORAGE) ) {

        ZoneSize = BufferSize;
    }

    if (ZoneSize < sizeof(MEMORY_ZONE)) {

        ZoneSize = BufferSize / EV_DEFAULT_ZONE_BUFFER_RATIO;
        ZoneSize = (uint32)ROUND_UP_TO_POWER2(ZoneSize, EV_ZONE_ALIGNMENT);
    }

    if (ZoneSize > EV_MAXIMUM_ZONE_SIZE) {
        Storage->DefaultZoneSize = EV_MAXIMUM_ZONE_SIZE;

    } else {

        Storage->DefaultZoneSize = ZoneSize;
    }

    Storage->ZoneCount = 0;
    InitialBuffer = (UCHAR *)(Storage + 1);
    InitialBuffer = (UCHAR *)ROUND_UP_TO_POWER2(InitialBuffer, EV_ZONE_ALIGNMENT);

    Class_Microsoft_Singularity_Eventing_MemoryStorage::g_MemoryStorageRegisterBufferImpl(
        (UIntPtr)Storage,
        InitialBuffer,
        (uint32)(BufferSize - ((uint8 *)InitialBuffer - (uint8 *)Storage)));

    Storage->ZoneCursor = Storage->MemoryZoneLink;

    return (UIntPtr)Storage;
}

void
Class_Microsoft_Singularity_Eventing_MemoryStorage::
g_MemoryStorageRegisterBufferImpl(UIntPtr StorageHandle, UCHAR * Buffer, uint32 BufferSize)
{

    PMEMORY_STORAGE Storage = (PMEMORY_STORAGE)StorageHandle;
    PMEMORY_ZONE LastZone = NULL;
    PMEMORY_ZONE ZoneChain = NULL;
    PMEMORY_ZONE TempZone;
    PMEMORY_ZONE LastExistingZone = Storage->BkLink;

    InterlockedExchangeAdd((volatile INT32 *)&Storage->StorageSize, BufferSize);

    if ((Storage->DefaultZoneSize != 0) && (BufferSize > Storage->DefaultZoneSize)) {

        //  We have to split the larger chunk in multiple zones

        uint32 MaxZone = BufferSize / Storage->DefaultZoneSize;

        for (uint32 i = 0; i < MaxZone; i++) {

            TempZone = InitializeMemoryZone(Buffer, Storage->DefaultZoneSize, StorageHandle);
            EV_ASSERT(TempZone != NULL);

            InterlockedIncrement((volatile INT32* )&Storage->ZoneCount);

            if (ZoneChain == NULL) {

                ZoneChain = TempZone;
            }

            //  Link the zones togeather. Note the chain is not yet published outside
            //  until is pushed to the memory storage list eventually

            if (LastZone) {

                LastZone->Link = TempZone;
            }

            TempZone->BkLink = LastZone;
            LastZone = TempZone;

            Buffer = (UCHAR *)Buffer + Storage->DefaultZoneSize;
            BufferSize -= Storage->DefaultZoneSize;

        }

    }

    TempZone = InitializeMemoryZone(Buffer, BufferSize, StorageHandle);

    if (TempZone != NULL) {

        InterlockedIncrement((volatile INT32 *)&Storage->ZoneCount);

        // Here the remining portion might be too small for a whole zone.

        if (ZoneChain == NULL) {

            ZoneChain = TempZone;
        }

        //  Link the zones togeather. Note the chain is not yet published outside
        //  until is pushed to the memory storage list eventually

        if (LastZone) {

            LastZone->Link = TempZone;
        }

        TempZone->BkLink = LastZone;
        LastZone = TempZone;
    }

    if (LastZone != NULL) {

        LastZone->Link = NULL;

        if (LastExistingZone == NULL) {

            // The existing list is empty. Insert the new one to the head

            ZoneChain->BkLink = NULL;
            Storage->BkLink = LastZone;
            Storage->MemoryZoneLink = ZoneChain;

        } else {

            LastExistingZone->Link = ZoneChain;
            ZoneChain->BkLink = LastExistingZone;

        }

        Storage->BkLink = LastZone;
    }

}


UIntPtr Class_Microsoft_Singularity_Eventing_EventSource::
g_LogSourceEntryImpl(UIntPtr sourceHandle,
                     uint32 flags,
                     UIntPtr eventType,
                     uint8 * Buffer,
                     int32 size)
{
    UIntPtr storageHandle = OpenLoggingStorage(sourceHandle, &flags);
    return (UIntPtr)InternalLogFixedRecord(storageHandle,
                                           flags,
                                           eventType,
                                           Buffer,
                                           size);
}

UIntPtr Class_Microsoft_Singularity_Eventing_EventSource::
    g_LogSourceEntryImpl(UIntPtr sourceHandle,
                         uint32 flags,
                         UIntPtr eventType,
                         uint8 * Buffer,
                         int32 size,
                         int32 arraysCount,
                         Struct_Microsoft_Singularity_Eventing_ArrayType * arrays)
{
    UIntPtr storageHandle = OpenLoggingStorage(sourceHandle, &flags);
    return (UIntPtr)InternalLogVariableRecord(true,
                                              storageHandle,
                                              flags,
                                              eventType,
                                              Buffer,
                                              size,
                                              arraysCount,
                                              arrays);
}


uint32 Class_Microsoft_Singularity_Eventing_MemoryStorage::
g_GetMemoryStorageOveheadImpl()
{
    // Determine the overhead in the pesimistic case

    return sizeof(MEMORY_STORAGE) +
           (sizeof(MEMORY_ZONE) + EV_ZONE_ALIGNMENT) * EV_DEFAULT_ZONE_BUFFER_RATIO +
           sizeof(MEMORY_HEADER) * EV_DEFAULT_ZONE_BUFFER_RATIO;
}

UIntPtr Class_Microsoft_Singularity_Eventing_MemoryStorage::
g_CreateQueryViewImpl(UIntPtr storageHandle, bool forward)
{
    return (UIntPtr)CreateQuery(storageHandle, forward);
}

void Class_Microsoft_Singularity_Eventing_MemoryStorage::
g_DeleteQueryViewImpl(UIntPtr queryHandle)
{
    UnRegisterQueryView((PQUERY_VIEW)queryHandle);
}

UIntPtr Class_Microsoft_Singularity_Eventing_MemoryStorage::
g_GetNextEntryImpl(UIntPtr queryHandle,
                  UIntPtr * typeHandle,
                  uint32 * userOffset,
                  uint8 * buffer,
                  uint16 bufferSize)
{
    PQUERY_VIEW view = (PQUERY_VIEW)queryHandle;

    PMEMORY_HEADER entry = GetNextStorageEntry(view);

    if (entry != NULL) {

        *typeHandle = entry->Type;

        void * src = GetUserRecordStructure(entry);

        if (entry->Size < bufferSize) {

            bufferSize = entry->Size;
        }

        memcpy(buffer, entry , bufferSize);
        *userOffset = (uint32)((ULONG_PTR)src - (ULONG_PTR)entry);
    }

    return (UIntPtr) entry;
}

UIntPtr Class_Microsoft_Singularity_Eventing_MemoryStorage::
g_WalkEventDescriptorImpl(UIntPtr eventHandle,
                          UIntPtr currentField,
                          uint16 * offset,
                          uint16 * type,
                          bartok_char * bufferName,
                          uint16 bufferSize)
{
    if (eventHandle == 0) {

        eventHandle = Handle_MEMORY_HEADER;
    }

    PMEMORY_HEADER Entry = HANDLE_TO_HEADER(eventHandle);

    EV_ASSERT(Entry->Flags == RECORD_EVENT_TYPE);

    PEVENT_DESCRIPTOR eventDescriptor = (PEVENT_DESCRIPTOR)GetUserRecordStructure(Entry);
    PEVENT_FIELD_DESCRIPTOR field = NULL;
    char * src;

    if (currentField == 0) {

        src = GetExtendedString(eventHandle, 1);

    } else if (currentField == eventHandle) {

        // start now with the fields inside the event

        field = eventDescriptor->fieldsLink;

    } else {

        field = (PEVENT_FIELD_DESCRIPTOR)(currentField);
        field = field->fieldsLink;

        if (field == NULL) {

            return 0;
        }
    }

    if (field == NULL) {

        //  This is refers the event descriptor itself.
        //  The type returned will be zero, the only meaningful information
        //  will be the event name

        *offset = 0;
        *type = 0;

    } else {

        *offset = field->Offset;
        *type = field->Type;

        src = GetExtendedString((UIntPtr)((PMEMORY_HEADER)field - 1), 1);
    }

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

    if (field == NULL) {

        return eventHandle;
    }

    return (UIntPtr)field;
}



//
///////////////////////////////////////////////////////////////// End of File.
