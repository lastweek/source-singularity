/////////////////////////////////////////////////////////////////////////////
//
//  diagdump.cpp - Extension using the enumeration support for diagnosis
//  to dump the content of the tracing
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

#include "singx86.h"
#include "diagnose.h"

bool DumpAllEvents = FALSE;
bool DumpStackTraces = FALSE;
bool DumpDescriptions = FALSE;

//
//  Simple transforms on fields
//

//
//  Empty base class for common transform manipulation
//

class EntryTransform {

    public:
    virtual bool IsFieldHidden(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {

        // all fields are visilbe by default
        return FALSE;
    }

    virtual bool DoTransform(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {
        // no transform is applied on fields by default
        return FALSE;
    }

    virtual int GetFieldWidth(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {
        // no transform is applied on fields by default
        return 0;
    }
};

class StringFormatTransform : public EntryTransform {

    // Name of the field the transform will perform on
    char * FieldName;

    // the index of the first argument that will be used in string formatting
    int ArgumentBaseIndex;

    public:

    StringFormatTransform(char * fieldName, int argumentBase)
    {
        FieldName = _strdup(fieldName);
        ArgumentBaseIndex = argumentBase;
    }

    ~StringFormatTransform()
    {
        if (FieldName != NULL) free(FieldName);

    }

    virtual int GetFieldWidth(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {
        if (_stricmp(FieldName, fieldDescriptor->Name) == 0) {

            return 30;  // this is dependent of format and arguments. Just pick a value common
                        // for current usages
        }

        return 0;
    }

    virtual bool DoTransform(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {

        if (_stricmp(FieldName, fieldDescriptor->Name) == 0) {

            ExtOut("  ");
            entryDescriptor->Format(fieldDescriptor->ExtendedFieldIndex + 1, ArgumentBaseIndex);
            return true;
        }

        return false;
    }
};

class SymbolLookupTransform : public EntryTransform {

    // Name of the field the transform will perform on
    char * FieldName;

    public:

    SymbolLookupTransform(char * fieldName)
    {
        FieldName = _strdup(fieldName);
    }

    ~SymbolLookupTransform()
    {
        if (FieldName != NULL) free(FieldName);
    }

    virtual int GetFieldWidth(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {
        if (_stricmp(FieldName, fieldDescriptor->Name) == 0) {

            return 70;
        }
        return 0;
    }

    virtual bool DoTransform(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {

        if (_stricmp(FieldName, fieldDescriptor->Name) == 0) {

            char symbol[512];
            ULONG64 displacement = 0;
            ULONG64 fieldValue = fieldDescriptor->GetFieldNumericValue();

            HRESULT status = g_ExtSymbols->GetNameByOffset(fieldValue,
                                                           symbol,
                                                           arrayof(symbol),
                                                           NULL,
                                                           &displacement);
            if (status == S_OK) {

                ExtOut("  %-68s", symbol);

            } else {

                ExtOut("  %-68s", "");
            }

            return true;
        }

        return false;
    }
};

class RestrictToFieldsTransform : public EntryTransform {

    // The pattern containing the fields available for display
    // in the format "F1|F2|F3"

    char * AvailableFields;

    public:

    RestrictToFieldsTransform(char * fieldList)
    {
        AvailableFields = _strdup(fieldList);
    }

    ~RestrictToFieldsTransform()
    {
        if (AvailableFields != NULL) free(AvailableFields);

    }

    virtual bool IsFieldHidden(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    {
        if ((AvailableFields != NULL) && (strstr(AvailableFields, fieldDescriptor->Name) != NULL)) {

            return TRUE;
        }

        return FALSE;
    }

};

const int MaxTransformAllowed = 16;

EntryTransform * Transforms[MaxTransformAllowed];
int InUseTransforms = 0;

void FlushTransforms()
{
    for (int i = 0; i < InUseTransforms; i++) {

        delete Transforms[i];
        Transforms[i] = NULL;
    }
    InUseTransforms = 0;
}

bool AddTransform(EntryTransform * transform)
{
    if (InUseTransforms < MaxTransformAllowed) {

        Transforms[InUseTransforms++] = transform;
        return true;
    }

    return false;
}

bool ApplyTransforms(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
{
    for (int i = 0; i < InUseTransforms; i++) {

        if (Transforms[i]->DoTransform(entryDescriptor, fieldDescriptor)) {

            return true;
        }
    }
    return false;
}

int GetTransformFieldWidth(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
{
    int width = 0;

    for (int i = 0; i < InUseTransforms; i++) {

        int crtWidth = Transforms[i]->GetFieldWidth(entryDescriptor, fieldDescriptor);

        if (width < crtWidth) {

            width = crtWidth;
        }
    }

    return width;
}


bool TestVisibility(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
{
    for (int i = 0; i < InUseTransforms; i++) {

        if (Transforms[i]->IsFieldHidden(entryDescriptor, fieldDescriptor)) {

            return false;
        }
    }
    return true;
}

void ParseStringFormatTransform(PCSTR & args)
{
    char * str = ReadToken(args);

    if (str != NULL) {

        StringFormatTransform * tr = new StringFormatTransform(str, 3/*FIXME*/);
        if (!AddTransform(tr)) delete tr;
        free(str);
    }
}

void ParseVisibleFields(PCSTR & args)
{
    char * str = ReadToken(args);

    if (str != NULL) {

        RestrictToFieldsTransform * tr = new RestrictToFieldsTransform (str);

        if (!AddTransform(tr)) delete tr;
        free(str);
    }
}

void ParseSymbolLookupTransform(PCSTR & args)
{
    char * str = ReadToken(args);

    if (str != NULL) {

        SymbolLookupTransform * tr = new SymbolLookupTransform(str);
        if (!AddTransform(tr)) delete tr;
        free(str);
    }
}


void WriteLine(int length)
{
    while (length--) ExtOut("-");
}


void DumpStackTrace()
{
    for (int i = 1; ; i++) {

        UINT64 ipValue = GetStackTrace(i);

        if (ipValue == 0) {
            break;
        }

        CHAR name[512];

        if (g_ExtSymbols->GetNameByOffset(ipValue,
                                          (PSTR)&name,
                                          sizeof(name),
                                          NULL, NULL) == S_OK) {
            ExtOut("        %p %s\n", ipValue, name);

        } else {

            ExtOut("        %p {invalid symbol}\n", ipValue);
        }
    }
}

//
//  Implementation of DumpTracing methods
//


bool DumpTracing::TypeCallout(EventTypeEntry * entryDescriptor)
{
    if (!EventingEnumerator::TypeCallout(entryDescriptor)) {

        if (!EventingEnumerator::TypeCallout(SystemHeaderType)) {
            return FALSE;
        }
    }

    if (LastItem != type) {

        if (DumpSummary) ExtOut("Registered event types:\n");
        LastItem = type;
    }

    if (DumpSummary) ExtOut("    %s: (Key=%p, FieldsCount=%ld) - %s\n",
                            entryDescriptor->Name,
                            (UINT64)entryDescriptor->Key,
                            entryDescriptor->NumFields,
                            entryDescriptor->Descriptor);

    return FALSE;

}

void DumpTracing::SourcesCallout(SourceEntry * source)
{
    if (LastItem != DumpTracing::source) {

        if (DumpSummary) ExtOut("Registered sources:\n");
        LastItem = DumpTracing::source;
    }

    if (DumpSummary) ExtOut("    %s: (Key=%p, Storage=%p, ControlFlags=%lx)\n",
                            source->Name,
                            (UINT64)source->Key,
                            source->StorageHandle,
                            source->ControlFlags);
}

bool DumpTracing::ActiveSourceCallout(SourceEntry * source, bool finished, ControllerObject *controller)
{
    if (LastItem != DumpTracing::activesource) {

        if (DumpSummary) ExtOut("Registered active sources:\n");
        LastItem = DumpTracing::activesource;
    }

    if (!finished) {

        EventTypeEntry * typeEntry = controller->FindType(source->EventTypeHandle);

        if (typeEntry != NULL) {

            if (DumpSummary) ExtOut("    %s: (Key=%p, Type=%p, Buffer=%p, %ld %s items)\n",
                                    source->Name,
                                    source->Key,
                                    source->EventTypeHandle,
                                    source->DebuggerBufferAddress,
                                    (int)source->Count,
                                    typeEntry->Name);

        } else {

            if (DumpSummary) ExtOut("    %s: (Key=%p, Type=%p, Buffer=%p, %ld unknown type items)\n",
                                    source->Name,
                                    source->Key,
                                    source->EventTypeHandle,
                                    source->DebuggerBufferAddress,
                                    (int)source->Count);
        }


    }
    return FALSE;
}

bool DumpTracing::ControllerCallout( ControllerObject *ctrl, bool finished)
{
    if (!EventingEnumerator::ControllerCallout(ctrl, finished)) {

        return FALSE;
    }
    if (DumpSummary) {

        if (!finished) {
            ExtOut("********************************************\n");
            ExtOut("*\n");
            ExtOut("* Controller %p (context %p)\n",
                    ctrl->ControllerHandle,
                    ctrl->ContextHandle);
            ExtOut("*\n");
            ExtOut("********************************************\n");
        } else {
            ExtOut("\n\n");
        }
    }
    LastItem = controller;
    return TRUE;
}


bool DumpTracing::FieldCallout(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
{
    if (!TestVisibility(entryDescriptor, fieldDescriptor)) {

        return TRUE;
    }

    if (PrintPhase == 0) {

        if (!DumpDescriptions || (MetadataSize == 0)) {

            fieldDescriptor->PrintValue(entryDescriptor);
        }

    } else if (MetadataSize != 0){

        if (FieldIndex != 0) ExtOut(",");
        ExtOut("%s", fieldDescriptor->Name);
        FieldIndex += 1;
    }

    return TRUE;
}

bool DumpTracing::EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor)
{
    if (entryDescriptor == NULL) {

        return FALSE;
    }

    if (!entryDescriptor->FilterMatch()) {

        return FALSE;
    }

    if (DumpAllEvents) {

        PrintPhase = 0;

        ExtOut("%6ld %p", CrtEntryIndex++, header->StackAddress);
        entryDescriptor->WalkFields(this);

        if (DumpDescriptions) {

            ExtOut("  ");
            entryDescriptor->PrintDescription();
            ExtOut("\n");

        } else {

            PrintPhase = 1;
            FieldIndex = 0;
            ExtOut(" : %s(", entryDescriptor->Name);
            entryDescriptor->WalkFields(this);
            ExtOut(")\n");
        }

        if (header->StackSize && DumpStackTraces) {

            DumpStackTrace();
            ExtOut("\n");
        }
    }

    return TRUE;

}



//
//  Implementation of DumpType class
//

DumpType::DumpType(UINT64 handle)
{
    typeHandle = handle;
    printHeader = 1;
}


bool DumpType::FieldCallout(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
{
    if (!TestVisibility(entryDescriptor, fieldDescriptor)) {

        return TRUE;
    }

    if (printHeader < 3) {

        int width = fieldDescriptor->GetFieldPrintWidth();
        int transformWidth = GetTransformFieldWidth(entryDescriptor, fieldDescriptor);

        if (transformWidth > width) {

            width = transformWidth;
        }

        if (printHeader == 1) {

            char buff[100];

            _snprintf(buff, sizeof(buff), "%%%lds", width);
            ExtOut(buff, fieldDescriptor->Name);

        } else if (printHeader == 2) {

            WriteLine(width);
        }
    } else {

        if (!ApplyTransforms(entryDescriptor, fieldDescriptor)) {

            fieldDescriptor->PrintValue(entryDescriptor);
        }
    }

    return TRUE;
}

bool DumpType::EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor)
{
    if ((entryDescriptor == NULL) || (entryDescriptor->Key != typeHandle)) {

        return FALSE;
    }

    if (!entryDescriptor->FilterMatch()) {

        return FALSE;
    }

    if (DumpAllEvents) {

        if (printHeader == 1) {

            PrintHeader(entryDescriptor);

        } else if ((CrtEntryIndex % 50) == 0){

            printHeader = 1;
            ExtOut(" Index   Stacks");
            entryDescriptor->WalkFields(this);
            ExtOut("\n");
            printHeader += 1;
            WriteLine(6);
            entryDescriptor->WalkFields(this);
            ExtOut("\n");
            printHeader += 1;
        }

        INT64 delta;

        if (lastTimeStamp == 0) {

            delta = 0;
        } else {

            delta = header->timestamp - lastTimeStamp;
        }

        ExtOut("%6ld %p", CrtEntryIndex++, header->StackAddress);
        lastTimeStamp = header->timestamp;
        entryDescriptor->WalkFields(this);
        ExtOut("\n");

        if (header->StackSize && DumpStackTraces) {

            DumpStackTrace();
            ExtOut("\n");
        }
    }

    return TRUE;

}

bool DumpType::PrintHeader(EventTypeEntry * entryDescriptor)
{
    ExtOut("TYPE: %p Key=%p FieldsCount=%ld (%s-%s)\n",
           (UINT64)entryDescriptor,
           (UINT64)entryDescriptor->Key,
           entryDescriptor->NumFields,
           entryDescriptor->Name,
           entryDescriptor->Descriptor);

    ExtOut(" Index   Stacks");
    entryDescriptor->WalkFields(this);
    ExtOut("\n");

    printHeader += 1;
    WriteLine(16);
    entryDescriptor->WalkFields(this);
    ExtOut("\n");
    printHeader += 1;
    CrtEntryIndex = 0;
    return TRUE;

}


bool DumpType::TypeCallout(EventTypeEntry * entryDescriptor)
{

    if (!EventingEnumerator::TypeCallout(entryDescriptor)) {

        if (!EventingEnumerator::TypeCallout(SystemHeaderType)) {
            return FALSE;
        }
    }

    if (entryDescriptor->Key != typeHandle) {

        return FALSE;
    }
    lastTimeStamp = 0;
    return TRUE;

}

bool DumpType::ActiveEntryCallout(EventTypeEntry * entryDescriptor, BOOL finished)
{
    if (finished) {
        ExtOut("\n");
        return TRUE;
    }

    if (entryDescriptor->Key != typeHandle) {

        return FALSE;
    }

    if (!entryDescriptor->FilterMatch()) {

        return FALSE;
    }

    if (printHeader == 1) {

        PrintHeader(entryDescriptor);
    }

    ExtOut("%6ld", CrtEntryIndex++);

    return TRUE;

}


bool DumpType::ActiveSourceCallout(SourceEntry * source, bool finished, ControllerObject *controller)
{
    if (!finished) {

        CrtEntryIndex = 0;
        printHeader = 1;

        if ((source->EventTypeHandle == typeHandle)) {

            ExtOut("ACTIVE SOURCE: %p Key=%p Type=%p Buffer=%p (%ld items)(%s)\n",
                (UINT64)source,
                source->Key,
                source->EventTypeHandle,
                source->DebuggerBufferAddress,
                (int)source->Count,
                source->Name);

            return TRUE;
        }

        return FALSE;

    } else {
        ExtOut("\n");
    }
    return TRUE;
}

//
//  Implementation of the TypeFilterEnumerator methods
//

TypeFilterEnumerator::TypeFilterEnumerator()
{
    Array = new VariableArray();
    Pattern = NULL;
}

TypeFilterEnumerator::~TypeFilterEnumerator()
{
    if (Array != NULL) delete (Array);
    if (Pattern != NULL) delete (Pattern);

}

void TypeFilterEnumerator::SetPattern(StringPattern * pattern) {

    Pattern = pattern;
}


bool TypeFilterEnumerator::TypeCallout(EventTypeEntry * entryDescriptor)
{
    if (Pattern->IsMatch(entryDescriptor->Name)) {

        Array->Add(entryDescriptor->Key);
    }

    return FALSE;
}

//
//  Implementation of the TypeEntryCollector methods
//

TypeEntryCollector::TypeEntryCollector(UINT64 typeHandle, char * field)
    : TypeFilterEnumerator()
{
    TypeHandle = typeHandle;
    sortField = field;
    cascadeEnumerator = NULL;
    GroupByController = FALSE;
}

TypeEntryCollector::~TypeEntryCollector() {

}

bool TypeEntryCollector::MedataCallout(ControllerObject *controller)
{
    if (cascadeEnumerator) {

        return cascadeEnumerator->MedataCallout(controller);
    }

    return TRUE;
}

void TypeEntryCollector::SourcesCallout(SourceEntry * source)
{
    if (cascadeEnumerator) {

        return cascadeEnumerator->SourcesCallout(source);
    }
}

bool TypeEntryCollector::StorageCallout(UINT64 storageAddress, bool finished)
{
    if (cascadeEnumerator) {

        return cascadeEnumerator->StorageCallout(storageAddress, finished);
    }

    return TRUE;
}


bool TypeEntryCollector::FieldCallout(EventTypeEntry * entryDescriptor,
                                      FieldEntry * fieldDescriptor)
{
    //  NOTE this assumes inserting FieldsWidth elements to the array

    if (_stricmp(sortField, fieldDescriptor->Name) == 0) {

        Array->Add(crtHandle);
        Array->Add(fieldDescriptor->GetFieldNumericValue());
        Array->Add((UINT64)currentController);
    }

    return TRUE;
}

bool TypeEntryCollector::EntryCallout(EntryHeader *header,
                                      EventTypeEntry * entryDescriptor)
{
    if ((entryDescriptor == NULL) ||
        ((TypeHandle != 0) && (entryDescriptor->Key != TypeHandle))) {

        return FALSE;
    }

    if (!entryDescriptor->FilterMatch()) {

        return FALSE;
    }

    crtHandle = header->address;
    entryDescriptor->WalkFields(this);

    return TRUE;

}

bool TypeEntryCollector::TypeCallout(EventTypeEntry * entryDescriptor)
{

    if (!EventingEnumerator::TypeCallout(entryDescriptor)) {

        if (!EventingEnumerator::TypeCallout(SystemHeaderType)) {
            return FALSE;
        }
    }

    if (cascadeEnumerator) {

        cascadeEnumerator->TypeCallout(entryDescriptor);
    }

    if ((TypeHandle != 0) && (entryDescriptor->Key != TypeHandle)) {

        return FALSE;
    }
    return TRUE;

}

static int ItemCompare(const void * e1, const void * e2)
{
    UINT64 *ptr1 = (UINT64 *) e1;
    UINT64 *ptr2 = (UINT64 *) e2;

    if (ptr1[1] < ptr2[1]) {
        return -1;
    } else if (ptr1[1] == ptr2[1]) {
        return 0;
    }

    return 1;
}

void TypeEntryCollector::SortItems()
{
    qsort(Array->Array, Array->InUse / FieldsWidth, FieldsWidth*sizeof(UINT64), ItemCompare);
}

void TypeEntryCollector::WalkItems(EventingEnumerator * enumerator)
{

    for (int i = 0; i < Array->InUse; i+= FieldsWidth) {

        ControllerObject * ctrl = (ControllerObject *)Array->Array[i+2];

        if (ctrl != NULL) {

            ctrl->ReadMemoryHeader(enumerator, Array->Array[i]);
        }
    }
}

bool TypeEntryCollector::ControllerCallout(ControllerObject *controller, bool finished)
{
    if (!EventingEnumerator::ControllerCallout(controller, finished)) {

        return FALSE;
    }

    if (finished) {

        if (GroupByController) {

            SortItems();

            if (cascadeEnumerator) {

                WalkItems(cascadeEnumerator);
                cascadeEnumerator->ControllerCallout(controller, finished);
            }

            //
            //  Recycle the elements captured so far since the cascade enumerator processed them
            //  already
            //

            if (Array != NULL) delete (Array);
            Array = new VariableArray();
        }
        currentController = 0;

    } else {

        currentController = controller;
        if (GroupByController) {
            if (cascadeEnumerator) {

                cascadeEnumerator->ControllerCallout(controller, finished);
            }
        }
    }
    return TRUE;
}

bool TypeEntryCollector::SystemCallout(bool finished)
{

    if (finished) {

        SortItems();

        if (cascadeEnumerator) {

            WalkItems(cascadeEnumerator);
        }
    }
    return TRUE;
}

//
//  Source collector methods.
//

SourceCollector::SourceCollector(char * sourceName, char * field)
    : TypeEntryCollector(0, field)
{
    SourcePattern = NULL;
    storageHandle = 0;

    if (sourceName != NULL) {
        SourcePattern = new StringPattern();

        if (SourcePattern) {

            SourcePattern->ParseInput(sourceName);
        }
    }
}

void SourceCollector::SourcesCallout(SourceEntry * source)
{
    if (SourcePattern) {

        if (SourcePattern->IsMatch(source->Name)) {

            storageHandle = source->StorageHandle;
        }
    }
}


bool SourceCollector::StorageCallout(UINT64 storageAddress, bool finished)
{
    if ((storageHandle == 0) || (storageAddress == storageHandle)) {

        return TRUE;
    }

    return FALSE;
}


