////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   EventDescriptor.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"
#include "eventing.h"

#ifdef SINGULARITY_KERNEL
extern UIntPtr MonitoringTypeHandle;
extern UIntPtr TracingTypeHandle;
#endif


#define _LOGGING_TO_REPOSITORY

#define DECLARE_STRUCTURE_BEGIN(x,d)  UIntPtr Handle_##x;
#define DECLARE_ENUM_BEGIN(x,sz)  UIntPtr Handle_##x;

    #include "SystemEvents.inl"

#undef _LOGGING_TO_REPOSITORY

uint16 GetFieldSize(uint16 type)
{
    if (type & EVENT_FIELD_TYPE_arrayType) {

        return sizeof(uint16);
    }

    switch (type) {

        case EVENT_FIELD_TYPE_int8:
        case EVENT_FIELD_TYPE_uint8:
            return sizeof(uint8);

        case EVENT_FIELD_TYPE_int16:
        case EVENT_FIELD_TYPE_uint16:
            return sizeof(uint16);

        case EVENT_FIELD_TYPE_int32:
        case EVENT_FIELD_TYPE_uint32:
            return sizeof(uint32);

        case EVENT_FIELD_TYPE_int64:
        case EVENT_FIELD_TYPE_uint64:
            return sizeof(uint64);

        case EVENT_FIELD_TYPE_IntPtr:
        case EVENT_FIELD_TYPE_UIntPtr:
            return sizeof(UIntPtr);
    }

    return 0;
}


uint16 GetFixedTypeSize(PEVENT_DESCRIPTOR typeEntry)
{
    PEVENT_FIELD_DESCRIPTOR field;
    uint16 size = 0;

    for (field = typeEntry->fieldsLink; field != NULL; field = field->fieldsLink) {

        uint16 fieldSize = GetFieldSize(field->Type);

        if (size < (field->Offset + fieldSize)) {

            size = field->Offset + fieldSize;
        }
    }

    return size;
}

char * GetExtendedString(UIntPtr EntryHandle, int index)
{
    PMEMORY_HEADER entry = HANDLE_TO_HEADER(EntryHandle);
    char * endPtr = (char *)(entry) + entry->Size;

    int entrySize;

    switch (entry->Flags) {

        case RECORD_EVENT_TYPE:
            entrySize = sizeof(EVENT_DESCRIPTOR);
            break;

        case RECORD_EVENT_FIELD:
            entrySize = sizeof(EVENT_FIELD_DESCRIPTOR);
            break;

        case RECORD_EVENT_GENERIC_FIELD:
            entrySize = sizeof(EVENT_GENERIC_TYPE_DESCRIPTOR);
            break;

        case RECORD_EVENT_VALUE:
            entrySize = sizeof(EVENT_VALUE_DESCRIPTOR);
            break;

        case RECORD_EVENT_ENUM:
            entrySize = sizeof(ENUM_DESCRIPTOR);
            break;

        default : {

            PEVENT_DESCRIPTOR typeEntry = HANDLE_TO_TYPE(entry->Type);
            entrySize = GetFixedTypeSize(typeEntry);
        }
    }


    void * base = GetUserRecordStructure(entry);

    char * crtPtr = (char *)base + entrySize;

    crtPtr = (char *)ROUND_UP_TO_POWER2(crtPtr, sizeof(int));
    if (crtPtr >= endPtr) {
        return NULL;
    }

    for (int i = 1; i < index; i++) {

        uint16 length;

        // copy the structure localy since it may not be aligned.

        memcpy(&length, crtPtr, sizeof(uint16));
        crtPtr += length + sizeof(uint16);
        if (crtPtr >= endPtr) {
            return NULL;
        }
    }

    char * ptr = crtPtr + sizeof(uint16); // skip also the size of the string
    if (ptr >= endPtr) {
        return NULL;
    }
    return ptr;
}



//
//  Shared routines to handle both unicode and ascii names for eventing
//

PMEMORY_HEADER
RegisterEventDescriptorImplementation(int stringType,
                                      PVOID name,
                                      uint16 nameLength,
                                      PVOID description,
                                      uint16 descriptionLength)
{
    EVENT_DESCRIPTOR Event = {NULL, 0, 1, 2};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {nameLength,
         sizeof(char),
         stringType,
         name},
        {descriptionLength,
         sizeof(char),
         stringType,
         description}};

    if (descriptionLength == 0) {

        Event.Description = 0;
    }

    PMEMORY_HEADER Entry = InternalLogVariableRecord( true,
        GetLocalRepositoryHandle(),
        RECORD_EVENT_TYPE,
        0,
        &Event,
        sizeof(Event),
        (descriptionLength) ? 2 : 1,
        array);

    return Entry;

}

PMEMORY_HEADER
RegisterFieldDescriptorImplementation(int stringType,
                                      PMEMORY_HEADER Descriptor,
                                      PVOID name,
                                      uint32 nameLength,
                                      uint16 offset,
                                      uint16 type )
{
    PEVENT_DESCRIPTOR eventDescriptor = (PEVENT_DESCRIPTOR)GetUserRecordStructure(Descriptor);
    int fieldSize = GetFieldSize(type);

    if (offset == 0) {

        offset = eventDescriptor->Size;

        //
        //  Align naturaly the field
        //

        offset = (uint16)ROUND_UP_TO_POWER2(offset, fieldSize);
    }

    EV_ASSERT(offset == ROUND_UP_TO_POWER2(offset, fieldSize));
    EV_ASSERT(offset >= eventDescriptor->Size);

    EVENT_FIELD_DESCRIPTOR Field = {NULL, offset, type, NULL};
    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {nameLength,
         sizeof(char),
         stringType,
         name}};

    PMEMORY_HEADER Entry = InternalLogVariableRecord( false,
                                                      GetLocalRepositoryHandle(),
                                                      RECORD_EVENT_FIELD,
                                                      (UIntPtr)Descriptor,
                                                      &Field,
                                                      sizeof(Field),
                                                      1,
                                                      array);

    if (Entry != NULL) {

        PEVENT_FIELD_DESCRIPTOR newField = (PEVENT_FIELD_DESCRIPTOR)GetUserRecordStructure(Entry);

        newField->fieldsLink = eventDescriptor->fieldsLink;
        eventDescriptor->fieldsLink = newField;
        eventDescriptor->Size = offset + fieldSize;

        CommitEventEntry(Entry);
    }

    return Entry;
}

PMEMORY_HEADER
RegisterGenericFieldDescriptorImplementation( int stringType,
                                              PMEMORY_HEADER event,
                                              PVOID name,
                                              uint32 nameLength,
                                              uint16 offset,
                                              uint16 size,
                                              UIntPtr typeFieldDescriptor)
{
    PEVENT_DESCRIPTOR eventDescriptor = (PEVENT_DESCRIPTOR)GetUserRecordStructure(event);

    if (offset == 0) {

        offset = eventDescriptor->Size;

        //
        //  Align naturaly the field
        //

        offset = (uint16)ROUND_UP_TO_POWER2(offset, size);
    }

    EV_ASSERT(offset == ROUND_UP_TO_POWER2(offset, size));
    EV_ASSERT(offset >= eventDescriptor->Size);

    EVENT_GENERIC_TYPE_DESCRIPTOR Field = {NULL,
                                           offset,
                                           GENERIC_TYPE_SIGNATURE,
                                           size,
                                           typeFieldDescriptor,
                                           1};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {nameLength,
         sizeof(char),
         stringType,
         name}};

    PMEMORY_HEADER Entry = InternalLogVariableRecord( false,
                                                      GetLocalRepositoryHandle(),
                                                      RECORD_EVENT_GENERIC_FIELD,
                                                      (UIntPtr)event,
                                                      &Field,
                                                      sizeof(Field),
                                                      1,
                                                      array);

    if (Entry != NULL) {

        PEVENT_FIELD_DESCRIPTOR newField = (PEVENT_FIELD_DESCRIPTOR)GetUserRecordStructure(Entry);

        newField->fieldsLink = eventDescriptor->fieldsLink;
        eventDescriptor->fieldsLink = newField;
        eventDescriptor->Size = offset + size;

        CommitEventEntry(Entry);
    }

    return Entry;
}

PMEMORY_HEADER
RegisterEnumDescriptorImplementation(int stringType,
                                     PVOID name,
                                     uint16 nameLength,
                                     uint16 type)
{
    ENUM_DESCRIPTOR Event = {NULL, type, 0, 1, 2};

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {nameLength,
         sizeof(char),
         stringType,
         name}};

    PMEMORY_HEADER Entry = InternalLogVariableRecord( true,
        GetLocalRepositoryHandle(),
        RECORD_EVENT_ENUM,
        0,
        &Event,
        sizeof(Event),
        1,
        array);

    return Entry;

}

PMEMORY_HEADER
RegisterValueDescriptorImplementation(int stringType,
                                      PMEMORY_HEADER descriptor,
                                      PVOID name,
                                      uint32 nameLength,
                                      uint64 value,
                                      uint8 flagLetter)
{
    EVENT_VALUE_DESCRIPTOR Field = {NULL, flagLetter, value, NULL };

    Struct_Microsoft_Singularity_Eventing_ArrayType array[] = {
        {nameLength,
         sizeof(char),
         stringType,
         name}};

    PMEMORY_HEADER Entry = InternalLogVariableRecord( false,
                                                      GetLocalRepositoryHandle(),
                                                      RECORD_EVENT_VALUE,
                                                      (UIntPtr)descriptor,
                                                      &Field,
                                                      sizeof(Field),
                                                      1,
                                                      array);
    if (Entry != NULL) {

        PENUM_DESCRIPTOR eventDescriptor = (PENUM_DESCRIPTOR)GetUserRecordStructure(descriptor);
        PEVENT_VALUE_DESCRIPTOR newField = (PEVENT_VALUE_DESCRIPTOR)GetUserRecordStructure(Entry);

        newField->fieldsLink = eventDescriptor->fieldsLink;
        eventDescriptor->fieldsLink = newField;

        if (flagLetter) {

            eventDescriptor->FlagsMask |= value;
        }

        CommitEventEntry(Entry);
    }

    return Entry;
}



PMEMORY_HEADER
RegisterEventDescriptor(PCHAR name,
                        uint16 nameLength,
                        PCHAR description,
                        uint16 descriptionLength)
{
    return RegisterEventDescriptorImplementation(EVENT_FIELD_TYPE_szChar,
                                                 name,
                                                 nameLength,
                                                 description,
                                                 descriptionLength);
}

PMEMORY_HEADER
RegisterFieldDescriptor(PMEMORY_HEADER Descriptor,
    PCHAR name,
    uint32 nameLength,
    uint16 offset,
    uint16 type )
{
    return RegisterFieldDescriptorImplementation(
                            EVENT_FIELD_TYPE_szChar,
                            Descriptor,
                            name,
                            nameLength,
                            offset,
                            type);
}

PMEMORY_HEADER
RegisterGenericFieldDescriptor(PMEMORY_HEADER event,
    PCHAR name,
    uint32 nameLength,
    uint16 offset,
    uint16 size,
    UIntPtr typeFieldDescriptor)
{
    return RegisterGenericFieldDescriptorImplementation( EVENT_FIELD_TYPE_szChar,
                                                         event,
                                                         name,
                                                         nameLength,
                                                         offset,
                                                         size,
                                                         typeFieldDescriptor);
}

PMEMORY_HEADER
RegisterEnumDescriptor(PCHAR name,
                       uint16 nameLength,
                       uint16 type)
{
    return RegisterEnumDescriptorImplementation(EVENT_FIELD_TYPE_szChar,
                                                name,
                                                nameLength,
                                                type);
}

PMEMORY_HEADER
RegisterValueDescriptor(PMEMORY_HEADER descriptor,
    PCHAR name,
    uint32 nameLength,
    uint64 value,
    uint8 flagLetter)
{

    return RegisterValueDescriptorImplementation(EVENT_FIELD_TYPE_szChar,
                                                 descriptor,
                                                 name,
                                                 nameLength,
                                                 value,
                                                 flagLetter);
}


//  Declare the system event structures

void
InitializeRegistrationSystem(void * buffer, size_t size)
{

    // Create a bufffer which does not recycle memory

    UIntPtr LocalStorageHandle = Class_Microsoft_Singularity_Eventing_MemoryStorage::
        g_MemoryStorageCreateImpl(MEMORY_STORAGE_FLAGS_PERMANENT, (uint8 *)buffer, (uint32)size, 0);

    RegisterRepositoryStorage(HANDLE_TO_STORAGE(LocalStorageHandle));
}

void
RegisterNativeTypes()
{
//
// Use this opportunity to validate the assumptions around the basic definition
// layouts
//

#define _VALIDATE_INVARIANTS

#define _LOGGING_TO_REPOSITORY


#define DECLARE_STRUCTURE_BEGIN(x,d)  \
{                                   \
    PMEMORY_HEADER __Event;          \
    __Event = RegisterEventDescriptor("System."#x, sizeof("System."#x) - 1, d, sizeof(d)); \
    if (__Event != NULL) {                                                  \
        PMEMORY_HEADER __Field;                                             \
        Handle_##x = (UIntPtr)__Event;

#define DECLARE_ENUM_BEGIN(x,t)  \
{                                   \
    PMEMORY_HEADER __Event;          \
    __Event = RegisterEnumDescriptor("System."#x, sizeof("System."#x) - 1, EVENT_FIELD_##t); \
    if (__Event != NULL) {                                                  \
        PMEMORY_HEADER __Field;                                             \
        Handle_##x = (UIntPtr)__Event;

#define DECLARE_STRUCTURE_END(x)   }}

#define DECLARE_ENUM_END DECLARE_STRUCTURE_END

#define DECLARE_FIELD(s,t,n)        \
        __Field = RegisterFieldDescriptor(__Event, #n, sizeof(#n), offsetof(s, n), EVENT_FIELD_##t);

#define DECLARE_SPECIAL_FIELD(s,t,n)    \
        __Field = RegisterFieldDescriptor(__Event, #n, sizeof(#n), offsetof(s, n), \
        EVENT_FIELD_TYPE_UIntPtr);

#define DECLARE_EXTENDED_ARRAY_FIELD(s,t,n)    \
        __Field = RegisterFieldDescriptor(__Event, #n, sizeof(#n), offsetof(s, n), \
        EVENT_FIELD_TYPE_arrayType | EVENT_FIELD_##t);

#define DECLARE_VALUE(s,v,f,n)        \
        __Field = RegisterValueDescriptor(__Event, #n, sizeof(#n), v, f);

#define DECLARE_GENERIC_FIELD(s,t,sz,t1,n)   \
        __Field = RegisterGenericFieldDescriptor(__Event, #n, sizeof(#n), offsetof(s, n), sz, Handle_##t1);

    #include "SystemEvents.inl"

#undef _LOGGING_TO_REPOSITORY

#ifdef SINGULARITY_KERNEL

    //
    //  For apps, discard the use of handles that have been registered, since these shared
    //  events are going to use the system handles
    //

    MonitoringTypeHandle = Handle_MONITORING_ENTRY;
    TracingTypeHandle = Handle_LEGACY_LOG_ENTRY;

#endif
}


//
///////////////////////////////////////////////////////////////// End of File.

