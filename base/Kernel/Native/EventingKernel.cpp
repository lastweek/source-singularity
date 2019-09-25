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

extern SOURCE_CONTROLLER SourceController;

#include "csformat.inc"

extern int strformat(void (*pfOutput)(void *pContext, char c), void *pContext,
                     const char * pszFmt, va_list args);


struct SNPRINT_CONTEXT {

    char ** CrtPos;
    char * EndBuffer;
};

static void snprintfout(void *pContext, char c)
{
    SNPRINT_CONTEXT * context = (SNPRINT_CONTEXT *)pContext;

    if (*(context->CrtPos) < context->EndBuffer) {

        *(*context->CrtPos)++ = c;
    }
}

int snprintf(char *pszOut, int outSize, const char *pszFmt, ...)
{
    int nOut;
    va_list args;
    SNPRINT_CONTEXT context = {&pszOut, pszOut + outSize - 1};

    va_start(args, pszFmt);
    nOut = strformat(snprintfout, &context, pszFmt, args);
    va_end(args);

    *pszOut = '\0';

    return nOut;
}

extern void kdprints(const char * pszFmt);

PEVENT_FIELD_DESCRIPTOR GetDescriptorField(PEVENT_DESCRIPTOR typeEntry, int fieldIndex)
{
    PEVENT_FIELD_DESCRIPTOR field;

    //
    //  TODO: This needs to be optimized caching the total number of fields
    //

    int numFields = 0;

    for (field = typeEntry->fieldsLink; (field != NULL); field = field->fieldsLink) {

        numFields++;
    }

    fieldIndex = numFields - fieldIndex - 1;

    for (field = typeEntry->fieldsLink; (field != NULL) && (fieldIndex > 0); field = field->fieldsLink) {

        fieldIndex--;
    }

    return field;
}


PEVENT_FIELD_DESCRIPTOR FindFieldDescriptor(PEVENT_DESCRIPTOR typeEntry, int offset)
{
    PEVENT_FIELD_DESCRIPTOR field;

    for (field = typeEntry->fieldsLink; field != NULL; field = field->fieldsLink) {

        if (field->Offset == offset) {

            return field;
        }
    }
    return NULL;
}


uint64 ReadValueAs(void * baseAddress, int offset, int type)
{
    void * memLocation = (char *)baseAddress + offset;

    if (type & EVENT_FIELD_TYPE_arrayType) {

        return *(uint16 *)memLocation;
    }

    switch (type) {

        case EVENT_FIELD_TYPE_int8:
        case EVENT_FIELD_TYPE_uint8:
            return *(uint8 *)memLocation;

        case EVENT_FIELD_TYPE_int16:
        case EVENT_FIELD_TYPE_uint16:
            return *(uint16 *)memLocation;

        case EVENT_FIELD_TYPE_int32:
        case EVENT_FIELD_TYPE_uint32:
            return *(uint32 *)memLocation;

        case EVENT_FIELD_TYPE_int64:
        case EVENT_FIELD_TYPE_uint64:
            return *(uint64 *)memLocation;

        case EVENT_FIELD_TYPE_IntPtr:
        case EVENT_FIELD_TYPE_UIntPtr:
            return (uint64)(*(UIntPtr *)memLocation);
    }

    return 0;
}

uint64 GetFieldValue(UIntPtr EntryHandle, int fieldIndex)
{
    PMEMORY_HEADER entry = HANDLE_TO_HEADER(EntryHandle);
    PEVENT_DESCRIPTOR typeEntry = HANDLE_TO_TYPE(entry->Type);
    PEVENT_FIELD_DESCRIPTOR field = GetDescriptorField(typeEntry, fieldIndex);

    void * base = GetUserRecordStructure(entry);

    if (field != NULL) {

        return ReadValueAs(GetUserRecordStructure(entry), field->Offset, field->Type);
    }

    return 0;
}

struct PRINT_EVENT_CONTEXT {

    UIntPtr EntryHandle;
    int ArgOffset;
};

int WriteSymbolicValue(char *pszOut, int bufferSize, PENUM_DESCRIPTOR enumDescriptor, uint64 value)
{
    PEVENT_VALUE_DESCRIPTOR field;
    int retValue = 0;

    uint64 flags = value & enumDescriptor->FlagsMask;
    uint64 item = value & ~enumDescriptor->FlagsMask;

    for (field = enumDescriptor->fieldsLink; field != NULL; field = field->fieldsLink) {

        int ret = 0;

        if ((field->FlagLetter != 0)) {

            //
            //  This needs to be elaborated further with using a string for the false case too
            //

            char symbol = ((field->Value & flags) == field->Value) ? field->FlagLetter : '.';

            ret = snprintf(pszOut, bufferSize, "%c", symbol);

        } else if (field->Value == item) {

            char * strValue = GetExtendedString((UIntPtr)((PMEMORY_HEADER)field - 1), 1);

            ret = snprintf(pszOut, bufferSize, "%s", strValue);

        }

        //
        //  Advance the output buffer, updating the current number of bytes written
        //

        retValue += ret;
        pszOut += ret;
        bufferSize -= ret;
    }

    return retValue;

}

char * GetStringField(void * context, int argIdx)
{
    PRINT_EVENT_CONTEXT * eventContext = (PRINT_EVENT_CONTEXT*) context;

    argIdx += eventContext->ArgOffset;

    PMEMORY_HEADER entry = HANDLE_TO_HEADER(eventContext->EntryHandle);
    PEVENT_DESCRIPTOR typeEntry = HANDLE_TO_TYPE(entry->Type);

    PEVENT_FIELD_DESCRIPTOR field = GetDescriptorField(typeEntry, argIdx);

    if (field->Type & (Class_Microsoft_Singularity_Eventing_DataType___string |
                       Class_Microsoft_Singularity_Eventing_DataType___szChar)) {

        int extendedIndex = (int)GetFieldValue(eventContext->EntryHandle, argIdx);

        if (extendedIndex > 0) {

            char * str = GetExtendedString(eventContext->EntryHandle, extendedIndex);

            //
            //  From this point all formating is relative to this string
            //

            eventContext->ArgOffset = argIdx + 1;

            return str;
        }
    }

    return NULL;
}

int PrintEventField(void * context, char *pszOut, int bufferSize, int aln, int wid, char fmt, int argIdx)
{
    PRINT_EVENT_CONTEXT * eventContext = (PRINT_EVENT_CONTEXT*) context;
    argIdx += eventContext->ArgOffset;

    PMEMORY_HEADER entry = HANDLE_TO_HEADER(eventContext->EntryHandle);
    PEVENT_DESCRIPTOR typeEntry = HANDLE_TO_TYPE(entry->Type);

    PEVENT_FIELD_DESCRIPTOR field = GetDescriptorField(typeEntry, argIdx);

    if (field == NULL) return 0;

    int retValue = 0;
    char * str = NULL;

    if (field->Type == GENERIC_TYPE_SIGNATURE) {

        //
        //  This might be a nested structure or an enum. The process of retrieving the
        //  actual value becomes a bit more complicated. The existing entry will be placed
        //  at a known offset in the parent structure, but we cannot interpret the value unless
        //  we find out the descriptor for this field.
        //

        if (((PMEMORY_HEADER)field - 1)->Flags == RECORD_EVENT_GENERIC_FIELD) {

            //
            //  After validating the descriptor version agains the nested type, we can safely
            //  cast to a generic field
            //

            PEVENT_GENERIC_TYPE_DESCRIPTOR genericType = (PEVENT_GENERIC_TYPE_DESCRIPTOR)field;
            UIntPtr typeHandle = genericType->GenericTypeHandle;
            PEVENT_DESCRIPTOR descriptor = (PEVENT_DESCRIPTOR)GetUserRecordStructure(HANDLE_TO_HEADER(typeHandle));

            if (((PMEMORY_HEADER)descriptor - 1)->Flags == RECORD_EVENT_ENUM) {

                //
                //  The field is an enum. Handle here the symbolic
                //

                PENUM_DESCRIPTOR enumDescriptor = (PENUM_DESCRIPTOR)descriptor;
                uint16 valueBasicType = enumDescriptor->Type;
                uint64 value = ReadValueAs(GetUserRecordStructure(entry), field->Offset, valueBasicType);

                retValue = WriteSymbolicValue(pszOut, bufferSize, enumDescriptor, value);

            } else {

                retValue = snprintf(pszOut, bufferSize, "(unsupported field)");
            }

        } else {

            retValue = snprintf(pszOut, bufferSize, "(unknown)");
        }

    } else if (field->Type &
                    (Class_Microsoft_Singularity_Eventing_DataType___string |
                     Class_Microsoft_Singularity_Eventing_DataType___szChar)) {

        int extendedIndex = (int)GetFieldValue(eventContext->EntryHandle, argIdx);

        if (extendedIndex > 0) {

            char * str = GetExtendedString(eventContext->EntryHandle, extendedIndex);

            if (str != NULL) {

                retValue = snprintf(pszOut, bufferSize, "%s", str);
            } else {

                retValue = snprintf(pszOut, bufferSize, "(invalid string index)");
            }
        }

    } else {

        uint64 value = GetFieldValue(eventContext->EntryHandle, argIdx);

        if (aln < wid) {
            aln = wid;
        }

        if (fmt == 'x') {
            if (wid > 0) {
                retValue = snprintf(pszOut, bufferSize, "%0x", value);
            }
            else {
                retValue = snprintf(pszOut, bufferSize, "%x", value);
            }
        }
        else {
            retValue = snprintf(pszOut, bufferSize, "%d", value);
        }

    }

    return retValue;
}

void DebugPrintEvent(UIntPtr eventHandle)
{
    char msg[256];
    PRINT_EVENT_CONTEXT printContext = {eventHandle, 0};

    PMEMORY_HEADER entry = HANDLE_TO_HEADER(eventHandle);
    char * frmt = GetExtendedString(entry->Type, 2);

    if (frmt != NULL) {

        FormatCSOutput(&printContext, frmt, msg, sizeof(msg),PrintEventField, GetStringField);
    }

    bartok_char wmsg[256];
    int lMsg = strlen(msg);

    if (lMsg < (sizeof(msg) - 1)) {

        msg[lMsg] = '\n';
        lMsg += 1;
        msg[lMsg] = 0;
    }

    for (int i = 0; i < lMsg; i++) {

        wmsg[i] = msg[i];
    }
    Class_Microsoft_Singularity_DebugStub::g_Print(wmsg, lMsg);
    //kdprints(msg);
}


bool Class_Microsoft_Singularity_Eventing_KernelController::
    g_DebugPrintLogEntry(UIntPtr controllerHandle, UIntPtr entryHandle)
{
    //
    //  TODO: Handle the paging case with apporpriate access as
    //

    DebugPrintEvent(entryHandle);
    return true;
}

bool Class_Microsoft_Singularity_Eventing_KernelController::
    g_RegisterExternalController(UIntPtr storageHandle, UIntPtr contextHandle)
{
    //  The external caller is responsible with the synchronization

    EXTERNAL_CONTROLLER_DESCRIPTOR source = {NULL, storageHandle, contextHandle};

    if (SourceController.FreeControllerList != NULL) {

        PEXTERNAL_CONTROLLER_DESCRIPTOR controller = SourceController.FreeControllerList;
        SourceController.FreeControllerList = controller->Link;
        *controller = source;
        RegisterExternalController(controller);

    } else {

        PMEMORY_HEADER Entry = InternalLogFixedRecord( GetLocalRepositoryHandle(),
            RECORD_EVENT_CONTROLLER,
            0,
            &source,
            sizeof(source));

        if (Entry == NULL) {
            return false;
        }

        PEXTERNAL_CONTROLLER_DESCRIPTOR newSource = (PEXTERNAL_CONTROLLER_DESCRIPTOR)GetUserRecordStructure(Entry);
        RegisterExternalController(newSource);
    }

    return true;
}

void Class_Microsoft_Singularity_Eventing_KernelController::
    g_UnRegisterExternalController(UIntPtr controllerHandle, UIntPtr contextHandle)
{
    //  Note the caller of this function needs to assure mutual exclusion

    PEXTERNAL_CONTROLLER_DESCRIPTOR tmpController = SourceController.ExternalControllers;

    for (tmpController = SourceController.ExternalControllers;
         tmpController != NULL;
         tmpController = tmpController->Link) {

        if ((tmpController->ContextHandle == contextHandle) &&
            (tmpController->ControllerHandle == controllerHandle)){

            UnRegisterExternalController(tmpController);

            return;
        }
    }
}

//
///////////////////////////////////////////////////////////////// End of File.


