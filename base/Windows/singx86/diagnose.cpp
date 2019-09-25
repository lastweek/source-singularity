/////////////////////////////////////////////////////////////////////////////
//
//  diagnose.cpp - Extension to find parse Singularity trace log.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

#include "singx86.h"
#include "diagnose.h"

ULONG pointerSize;

volatile BOOL BreakOnInternalError = FALSE;
extern bool DumpAllEvents;
extern bool DumpStackTraces;
extern bool DumpDescriptions;
bool DumpKernelOnly;

#include "..\..\Kernel\native\Csformat.inc"

//////////////////////////////////////////////////////////////////////////////
//
static HRESULT Usage()
{
    ExtOut("Usage:\n"
           "    !diagnose {options}\n"
           "Options:\n"
           "    Tracing commands:\n"
           "    [-s <SourcePatternFilter>] [-t <TypePatternFilter>] [-o <SortArgument>] [-f <Filter1>] [-f <Filter2>] [...]\n"
           "\n"
           "    Filter format:\n"
           "        -f <Field_Name>[<=,<,>,!> <Field_Value>]\n"
           "        See below sample usages. If no value is specified, it will select all types\n"
           "        defining that field\n"
           "\n"
           "    Sample commands:\n"
           "        !diagnose -n : dumps a sumary of basic types and sources available in the system\n"
           "        !diagnose -t *: Type filtering. The output will organize all entries by type\n"
           "                     : all events of all types will be displayed\n"
           "        !diagnose -s *Tracing* -t *LOG*: Same as above, but only types which will have the string\n"
           "                         : LOG anywhere in the name will be selected\n"
           "        !diagnose -t *LOG* -o Timestamp : Same as above, but the output will have the entries\n"
           "                                       : sorted by the column Timestamp. Any numeric column\n"
           "                                       : name is alowed for sorting. Strings not yet ...\n"
           "        !diagnose -t *LOG* -f Msg=\"*alarm*\" : Filter all entries of type containing LOG\n"
           "                                       : and arguments defined as Msg to contain alarm\n"
           "                                       : substring. The output can be combined with\n"
           "                                       : the sort option or other filtering options\n"
           "        !diagnose -t *LOG* -f Size>10 -f Size<40: Filter all entries of size between\n"
           "                                       : (10,40). Multiple conditions on the same field\n"
           "                                       : are allowed\n"
           "    Garbage collector commands:\n"
           "    -g <prefix>           : Write all profile logs that have been collected in files\n"
           "                            named based upon provided prefix\n"
           "    -ek <MemSize> [break] : Enable kernel GC profiling with a buffer of specified size in MBytes.\n"
           "                            Optionally break into the debugger before recycling buffers\n"
           "    -es <MemSize> [break] : As above, but for SIP GC profiling rather than Kernel GC profiling\n"
           "    -dk                   : Disable the kernel GC profiling\n"
           "    -ds                   : Disable the SIP GC profiling. Applies only for new SIPs\n"
          );
    return S_FALSE;
}

//
//  EVENTING AND TRACING SUPPORT
//  To keep consistency with the Singularity structures
//  the code leverages the same definitions present in the SystemEvents.inl file
//  TODO: This can be improved further to take less dependencies with valid symbols for kernel

#define TYPE_UIntPtr ULONG64
#define TYPE_uint8 ULONG64
#define TYPE_uint16 ULONG64
#define TYPE_uint32 ULONG64
#define TYPE_uint64 ULONG64
#define TYPE_PCHAR ULONG64
#define TYPE_BOOL ULONG64

//  Define the structure

#define DECLARE_STRUCTURE_BEGIN(x,d) struct S##x {
#define DECLARE_STRUCTURE_END(x)   };
#define DECLARE_FIELD(c,t,n)   t n;
#define DECLARE_SPECIAL_FIELD(c,t,n) ULONG64 n;
#define _CONSTANT_DEFINITIONS 1
#define DECLARE_EXTENDED_ARRAY_FIELD(c,t,n) ULONG64 n;
#define DECLARE_GENERIC_FIELD(s,t,sz,t1,n) ULONG64 n;

    #include "..\..\Kernel\native\SystemEvents.inl"

// Declare the fields descriptors

#define DECLARE_STRUCTURE_BEGIN(x,d) FieldType _Fields##x[] = {
#define DECLARE_STRUCTURE_END(x)    FIELDEND(), };

#define DECLARE_FIELD(c,t,n) { NULL, #n, offsetof(S##c,##n), 0, 0, 0, 0 },
#define DECLARE_GENERIC_FIELD(c,t,sz,t1,n) { NULL, #n, offsetof(S##c,##n), 0, 0, 0, 0 },
#define DECLARE_SPECIAL_FIELD DECLARE_FIELD
#define DECLARE_EXTENDED_ARRAY_FIELD DECLARE_FIELD

    #include "..\..\Kernel\native\SystemEvents.inl"


// Instantiate the log object for each defined structure.

#define DECLARE_STRUCTURE_BEGIN(x,d) StructType Struct##x= StructType("_"#x,sizeof(S##x), _Fields##x);

    #include "..\..\Kernel\native\SystemEvents.inl"


int gFieldTypeSizes[] = {0,1,1, 2, 2, 4, 4, 8, 8, 4, 4, 0};

char * gTypeNames[] = {
    "unknown",
    "int8",
    "uint8",
    "int16",
    "uint16",
    "int32",
    "uint32",
    "int64",
    "uint64",
    "IntPtr",
    "UIntPtr",
    "OutOfRangeType"};


//  Utility functions to access the fields and types definitions

int GetPtrSize()
{
    if (g_ExtControl->IsPointer64Bit() == S_OK) {

        return 8;
    }
    return 4;
}

int GetFieldSize(int type)
{
    if (type < sizeof(gFieldTypeSizes) / sizeof(gFieldTypeSizes[0])) {

        if ((type == FIELD_TYPE__IntPtr) || (type == FIELD_TYPE__UIntPtr)) {

            return GetPtrSize();
        }

        return gFieldTypeSizes[type];
    }

    if (type & FIELD_TYPE_VARIABLE_SIZE) {

        return sizeof(USHORT);
    }

    return 0;
}

char * GetFieldTypeName(int type)
{
    if (type < sizeof(gTypeNames) / sizeof(gTypeNames[0])) {

        return gTypeNames[type];
    }

    if (type & FIELD_TYPE_VARIABLE_ANY_STRING) {

        return "String";
    }

    if (type & FIELD_TYPE__arrayType) {

        return "Array";
    }

    return "";
}

bool MatchPatternString(PatternMatch matchMode, char * p, char* pattern)
{
    switch (matchMode) {

        case exact:
            return (_stricmp(p, pattern) == 0);
            break;
        case anywhere:
            return (strstr(p, pattern) != NULL);
            break;
        case begin:
            return (strstr(p, pattern) == p);
            break;
    }

    return FALSE;
}

char * ReadToken(PCSTR& args)
{

    char * arg = (char *)args;
    char fn[256];
    char *tmpChar = fn;
    char *limit = fn + sizeof(fn) - 1;

    SKIP_WHITESPACES(arg);

    while (*arg && (strchr("=<>! ",*arg) == NULL) && (tmpChar < limit)) {

        *tmpChar++ = *arg++;
    }
    *tmpChar = 0;

    SKIP_WHITESPACES(arg);
    args = arg;
    return _strdup(fn);
}


//  Local buffers and constants for extension


char EntryBuffer[4096];
ULONG_PTR HeaderSize = 0;
ULONG_PTR Stacksize = 0;
ULONG_PTR MetadataSize = 0;
ULONG64 ReadSize;
EventTypeEntry * SystemHeaderType = NULL;
EventTypeEntry * SystemTypeDescriptor = NULL;

UINT64 GetStackTrace(int index) {

    if (Stacksize == 0) return 0;

    if (pointerSize == sizeof(ULONG)) {

        int pos = index * sizeof(ULONG);

        if ((pos + sizeof(ULONG)) > Stacksize) return 0;

        ULONG * ptr = (ULONG * )(EntryBuffer + StructMEMORY_HEADER.size + pos);

        return *ptr;

    } else {

        int pos = index * sizeof(ULONG64);

        if ((pos + sizeof(ULONG64)) > Stacksize) return 0;

        ULONG64 * ptr = (ULONG64 * )(EntryBuffer + StructMEMORY_HEADER.size + pos);

        return *ptr;
    }

    return 0;
}

//
//  VariableArray class implementation
//

VariableArray::VariableArray(){

    Size = 1024;
    Array = (UINT64 *)malloc(Size * sizeof(UINT64));
    InUse = 0;
}

VariableArray::~VariableArray()
{
    if (Array != NULL) {

        free(Array);
    }
}

bool VariableArray::Extend()
{
    int newSize = Size * 2;
    if (newSize > 1024*1024) {

        newSize = Size + 1024*1024;
    }

    UINT64 *newArray = (UINT64 *)malloc(newSize * sizeof(UINT64));

    if (newArray == NULL) {

        return FALSE;
    }

    memcpy(newArray, Array, sizeof(UINT64) * Size);

    Size = newSize;
    free(Array);
    Array = newArray;
    return TRUE;
}

bool VariableArray::Add(UINT64 value) {

    if (InUse >= Size) {

        if (!Extend()) return FALSE;
    }

    Array[InUse++] = value;
    return TRUE;
}

//
//  Symbolic enum and flag support
//

EnumType::~EnumType()
{
    while (ValuesLists) {
        SymbolicValue * crt = ValuesLists;
        ValuesLists = ValuesLists->Next;
        delete crt;
    }

    if (Name) free (Name);
}

void EnumType::AddSymbolicValue(SymbolicValue * symValue)
{
    if (symValue->FlagChar) {
        NumFlags += 1;
        FlagsMask += symValue->Value;
    } else {

        int len = (int)strlen(symValue->Name);
        if (PrintWidth < len) {

            PrintWidth = len;
        }
    }

    symValue->Next = ValuesLists;
    ValuesLists = symValue;
}

int EnumType::GetFieldPrintWidth()
{
    if (FlagsMask) {

        return NumFlags + 2 + PrintWidth;

    } else {
        return PrintWidth;
    }
}

ULONG64 EnumType::GetFieldNumericValue(int offset) {

    switch (BasicType) {

        case FIELD_TYPE__int8:
        case FIELD_TYPE__uint8:
            return *((BYTE *)(EntryBuffer + MetadataSize + offset));

        case FIELD_TYPE__int16:
        case FIELD_TYPE__uint16:
            return *((USHORT *)(EntryBuffer + MetadataSize + offset));

        case FIELD_TYPE__int32:
        case FIELD_TYPE__uint32:
            return *((UINT *)(EntryBuffer + MetadataSize + offset));

        case FIELD_TYPE__int64:
        case FIELD_TYPE__uint64:
            return *((UINT64 *)(EntryBuffer + MetadataSize + offset));

        case FIELD_TYPE__IntPtr:
        case FIELD_TYPE__UIntPtr:
            return *((UINT_PTR *)(EntryBuffer + MetadataSize + offset));

    }

    // Non-numeric values return 0
    return 0;
}


int EnumType::PrintValue(int printWidth, int offset)
{
    ULONG64 value;

    value = GetFieldNumericValue(offset);
    ExtOut("  ");

    if (FlagsMask) {

        for (SymbolicValue * crt = ValuesLists; crt != NULL; crt = crt->Next) {

            if (crt->Value & value) {

                ExtOut("%c",crt->FlagChar);
            } else {
                ExtOut(".",crt->FlagChar);
            }
        }
    }

    if (PrintWidth > 0) {

        value &= ~FlagsMask;

        for (SymbolicValue * crt = ValuesLists; crt != NULL; crt = crt->Next) {

            if (crt->Value == value) {

                char buff[20];
                _snprintf(buff, sizeof(buff), "%%%lds", printWidth);
                ExtOut(buff, crt->Name);
            }
        }
    }

    return 0;
}

PCHAR EnumType::GetStringSymbol(int offset)
{
    ULONG64 value;

    value = GetFieldNumericValue(offset);

    if (FlagsMask) {

        CHAR buffer[65];
        int crtPos = 0;

        for (SymbolicValue * crt = ValuesLists; crt != NULL; crt = crt->Next) {

            if (crt->Value & value) {

                buffer[crtPos++] = crt->FlagChar;

            } else {
                buffer[crtPos++] = '.';
            }
        }

        buffer[crtPos] = 0;
        return _strdup(buffer);
    }

    if (PrintWidth > 0) {

        value &= ~FlagsMask;

        for (SymbolicValue * crt = ValuesLists; crt != NULL; crt = crt->Next) {

            if (crt->Value == value) {

                return _strdup(crt->Name);
            }
        }
    }

    return _strdup("???");
}

//
//  FieldEntry class implementation
//

FieldEntry::FieldEntry()
{
    Name=NULL;
    PrintWidth = 0;
    SymType = NULL;
}

FieldEntry::~FieldEntry()
{
    if (Name) {
        free(Name);
    }
}

int FieldEntry::GetArraySize(void * buffer)
{
    if ((Type & FIELD_TYPE_VARIABLE_SIZE) == 0) {

        //  Not a variable size array. return size 0

        return 0;
    }

    USHORT length = *(USHORT *)buffer;
    int basicType = Type & ~FIELD_TYPE_VARIABLE_SIZE;

    return length / GetFieldSize(basicType);
}

ULONG64 FieldEntry::GetFieldNumericValue(void * buffer, int index) {

    if ((Type & FIELD_TYPE_VARIABLE_SIZE) == 0) {

        //  Not a variable size array. return size 0

        return 0;
    }

    USHORT length = *(USHORT *)buffer;
    int basicType = Type & ~FIELD_TYPE_VARIABLE_SIZE;

    int count = length / GetFieldSize(basicType);

    if ((index < 0) || (index >= count)) {
        return 0;
    }

    buffer = (UCHAR*)buffer + sizeof(USHORT) + index * GetFieldSize(basicType);

    switch (basicType) {

        case FIELD_TYPE__int8:
        case FIELD_TYPE__uint8:
            return *((BYTE *)(buffer));

        case FIELD_TYPE__int16:
        case FIELD_TYPE__uint16:
            return *((USHORT *)(buffer));

        case FIELD_TYPE__int32:
        case FIELD_TYPE__uint32:
            return *((UINT *)(buffer));

        case FIELD_TYPE__int64:
        case FIELD_TYPE__uint64:
            return *((UINT64 *)(buffer));

        case FIELD_TYPE__IntPtr:
        case FIELD_TYPE__UIntPtr:
            return *((UINT_PTR *)(buffer));

    }

    // Non-numeric values return 0
    return 0;
}



ULONG64 FieldEntry::GetFieldNumericValue() {

    if ((Type != FIELD_TYPE_GENERIC_TYPE) && (Type & FIELD_TYPE_VARIABLE_ANY_STRING)) {

        return *((USHORT *)(EntryBuffer + MetadataSize + Offset));
    }

    switch (Type) {

        case FIELD_TYPE__int8:
        case FIELD_TYPE__uint8:
            return *((BYTE *)(EntryBuffer + MetadataSize + Offset));

        case FIELD_TYPE__int16:
        case FIELD_TYPE__uint16:
            return *((USHORT *)(EntryBuffer + MetadataSize + Offset));

        case FIELD_TYPE__int32:
        case FIELD_TYPE__uint32:
            return *((UINT *)(EntryBuffer + MetadataSize + Offset));

        case FIELD_TYPE__int64:
        case FIELD_TYPE__uint64:
            return *((UINT64 *)(EntryBuffer + MetadataSize + Offset));

        case FIELD_TYPE__IntPtr:
        case FIELD_TYPE__UIntPtr:
            return *((UINT_PTR *)(EntryBuffer + MetadataSize + Offset));

        case FIELD_TYPE_GENERIC_TYPE:
        {
            if (SymType == NULL) {

                SymType = Controller->FindEnum(TypeKey);

                EventTypeEntry * desc = Controller->FindType(ParentKey);

                if (desc) {

                    desc->UpdateFieldsOffsets();
                }
            }

            if (SymType != NULL) {

                return SymType->GetFieldNumericValue(Offset);
            }
        }
        break;

    }

    // Non-numeric values return 0
    return 0;
}

ULONG64 FieldEntry::PrintValue(EventTypeEntry * type)
{
    if (PrintWidth == 0) {

        GetFieldPrintWidth();
    }

    if (Type == FIELD_TYPE_GENERIC_TYPE) {

        if (SymType == NULL) {

            SymType = Controller->FindEnum(TypeKey);

            EventTypeEntry * desc = Controller->FindType(ParentKey);

            if (desc) {

                desc->UpdateFieldsOffsets();
            }
        }

        if (SymType != NULL) {

            SymType->PrintValue(PrintWidth, Offset);

        }
        return 0;
    }

    if (Type & FIELD_TYPE_VARIABLE_ANY_STRING) {

        int index = (int)GetFieldNumericValue();
        char * str = type->GetExtendedString(index);
        if (str) ExtOut(" \"%s\" ",str);
        return 0;
    }

    char format[20];


    switch (Type) {

        case FIELD_TYPE__int8:
        case FIELD_TYPE__uint8:
             _snprintf(format, sizeof(format), "%%%ldx", PrintWidth);
            ExtOut(format,(int)(*((byte *)(EntryBuffer + MetadataSize + Offset))));
        break;

        case FIELD_TYPE__int16:
        case FIELD_TYPE__uint16:
             _snprintf(format, sizeof(format), "%%%ldx", PrintWidth);
            ExtOut(format,(int)*((USHORT *)(EntryBuffer + MetadataSize + Offset)));
        break;

        case FIELD_TYPE__int32:
        case FIELD_TYPE__uint32:
             _snprintf(format, sizeof(format), "%%%ldx", PrintWidth);
            ExtOut(format, *((int *)(EntryBuffer + MetadataSize + Offset)));
        break;

        case FIELD_TYPE__IntPtr:
        case FIELD_TYPE__UIntPtr:
            ExtOut("  %p",*((UINT_PTR *)(EntryBuffer + MetadataSize + Offset)));
        break;

        case FIELD_TYPE__int64:
        case FIELD_TYPE__uint64:
             _snprintf(format, sizeof(format), "%%%ldI64x", PrintWidth);
            ExtOut(format, *((UINT64 *)(EntryBuffer + MetadataSize + Offset)));
        break;

    }

    // Non-numeric values return 0
    return 0;
}

int FieldEntry::GetFieldPrintWidth()
{
    if ((Type != FIELD_TYPE_GENERIC_TYPE) && (Type & FIELD_TYPE_VARIABLE_ANY_STRING)) {

        return 30;
    }

    if (PrintWidth > 0) return PrintWidth;

    switch (Type) {

        case FIELD_TYPE__int8:
        case FIELD_TYPE__uint8:
            PrintWidth = 4;
        break;

        case FIELD_TYPE__int16:
        case FIELD_TYPE__uint16:
            PrintWidth = 6;
        break;

        case FIELD_TYPE__int32:
        case FIELD_TYPE__uint32:
            PrintWidth = 10;
        break;

        case FIELD_TYPE__int64:
        case FIELD_TYPE__uint64:
            PrintWidth = 18;
        break;

        case FIELD_TYPE__IntPtr:
        case FIELD_TYPE__UIntPtr:
            PrintWidth = GetPtrSize() + 6;
        break;

        case FIELD_TYPE_GENERIC_TYPE:
        {
            if (SymType == NULL) {

                SymType = Controller->FindEnum(TypeKey);
                EventTypeEntry * desc = Controller->FindType(ParentKey);

                if (desc) {

                    desc->UpdateFieldsOffsets();
                }
            }

            if (SymType != NULL) {

                PrintWidth = SymType->GetFieldPrintWidth() + 2;
            }
        }
        break;

    }

    if ((PrintWidth > 0) && ((strlen(Name) + 1) > PrintWidth)) {

        PrintWidth = (unsigned int)strlen(Name) + 1;
    }

    return PrintWidth;
}


//
//  StringPattern class implementation
//

StringPattern::StringPattern()
{
    Pattern = NULL;
}

StringPattern::~StringPattern()
{
    Cleanup();
}

void StringPattern::Cleanup()
{
    if (Pattern) {

        free(Pattern);
    }
    Pattern = NULL;
}

bool StringPattern::IsMatch(char * p)
{
    return MatchPatternString(MatchMode, p, Pattern);
}

char * StringPattern::ParseInput(char * arg)
{
    char fn[256];
    char *tmpChar = fn;
    char *limit = fn + sizeof(fn) - 1;
    char endChar = ' ';

    Cleanup();

    SKIP_WHITESPACES(arg);

    MatchMode = exact;

    if (*arg == '\"') {

        endChar = '\"';
        arg++;
    }

    if (*arg == '*') {

        MatchMode = anywhere;
        arg++;
    }

    while (*arg && (*arg != endChar) && (tmpChar < limit)) {

        if (*arg != '*') {

            *tmpChar++ = *arg++;

        } else {
            arg++;

            if (MatchMode == exact) {

                MatchMode = begin;
            }
        }
    }

    *tmpChar = 0;

    Pattern = _strdup(fn);

    if (*arg == '\"') {

        arg++;
    }

    SKIP_WHITESPACES(arg);

    return arg;
}

//
//  FieldFilter class implementation
//

FieldFilter::FieldFilter()
{
    FieldNamePattern = NULL;
    StringValuePattern = NULL;
}

FieldFilter::~FieldFilter()
{
    Cleanup();
}

void FieldFilter::Cleanup()
{
    if (FieldNamePattern) free(FieldNamePattern);
    if (StringValuePattern) free(StringValuePattern);

    FieldNamePattern= NULL;
    StringValuePattern = NULL;
    NumericValuePattern = 0;
}

FieldFilter::FieldFilter(PatternMatch matchMode,
            char * fieldPattern,
            FilterOperation op,
            UINT64 value,
            char * strValue)
{
    FieldMatchMode = matchMode;
    Operation = op;
    FieldNamePattern = fieldPattern;
    NumericValuePattern = value;
    StringValuePattern = strValue;
}


bool FieldFilter::MatchFieldName(char * p)
{
    return MatchPatternString(FieldMatchMode, p, FieldNamePattern);
}

bool FieldFilter::MatchFieldValue(INT64 value)
{
    switch (Operation) {
        case all:
            return TRUE;
        case equal:
            return (NumericValuePattern == value);
        case less:
            return (NumericValuePattern > value);
        case greater:
            return (NumericValuePattern < value);
        case different:
            return (value != NumericValuePattern);
    }

    return FALSE;
}

bool FieldFilter::MatchFieldValue(char * value)
{
    switch (Operation){
        case all:
            return TRUE;
        case equal:
            return (StringValuePattern != NULL) && (_stricmp(value, StringValuePattern) == 0);
        case less:
            return (StringValuePattern != NULL) && (_stricmp(value, StringValuePattern) < 0);
        case greater:
            return (StringValuePattern != NULL) && (_stricmp(value, StringValuePattern) > 0);
        case contains:
            return (StringValuePattern != NULL) && (strstr(value, StringValuePattern) != NULL);
        case different:
            return (StringValuePattern != NULL) && (strstr(value, StringValuePattern) == NULL);
    }

    return FALSE;
}

char * FieldFilter::ParseInput(char * arg)
{
    char fn[256];
    char *tmpChar = fn;
    char *limit = fn + sizeof(fn) - 1;

    Cleanup();

    SKIP_WHITESPACES(arg);

    FieldMatchMode = exact;
    Operation = all;

    if (*arg == '*') {

        FieldMatchMode = anywhere;
        arg++;
    }

    while (*arg && (strchr("=<>!",*arg) == NULL) && (tmpChar < limit)) {

        if (*arg != '*') {

            *tmpChar++ = *arg++;

        } else {
            arg++;

            if (FieldMatchMode == exact) {

                FieldMatchMode = begin;
            }
        }
    }
    *tmpChar = 0;

    FieldNamePattern = _strdup(fn);

    SKIP_WHITESPACES(arg);

    if (*arg == 0) {

        return arg;
    }

    if (strchr("=<>!",*arg)) {

        switch (*arg) {

            case '=' :
                Operation = equal;
                break;
            case '<' :
                Operation = less;
                break;
            case '>' :
                Operation = greater;
                break;
            case '!' :
                Operation = different;
                break;
        }

        arg++;

        if (*arg == '\"') {

            arg++;

            if (*arg == '*') {

                Operation = contains;
                arg++;
            }
            tmpChar = fn;

            while (*arg  && (*arg != '\"') && (tmpChar < limit)) {

                if (*arg != '*') {


                    *tmpChar++ = *arg++;

                } else {
                    arg++;
                    Operation = contains;
                }
            }
            *tmpChar = 0;
            if (*arg) arg++;
            StringValuePattern = _strdup(fn);
        } else if (*arg) {

            PCSTR tmpChar = (PCSTR)arg;

            NumericValuePattern = GetValue(tmpChar, true);
            arg = (char*)tmpChar;
        }
    }

    SKIP_WHITESPACES(arg);

    return arg;
}

//  EventTypeEntry class implementation

EventTypeEntry::EventTypeEntry()
{
    Name=NULL;
    Descriptor = NULL;
    size = 0;
    Key = 0;
    NumFields = 0;
    filterCount = 0;
    FilterApplied = FALSE;
}

EventTypeEntry::~EventTypeEntry() {

    for (int i = 0; i < NumFields; i++) {
        delete Fields[i];
    }

    if (Name) {
        free(Name);
    }

    if (Descriptor) {
        free(Descriptor);
    }
}

bool EventTypeEntry::TestFilter(FieldFilter * newFilter)
{
    FilterApplied = TRUE;

    if (filterCount >= MAX_FILTERS) {
        return false;
    }

    // Test whether any of the fields inside this type entry would match
    // at least the fieldNamePattern;

    for (int i = 0; i < NumFields; i++) {

        FieldEntry * field = Fields[i];

        if (newFilter->MatchFieldName(field->Name)) {

            return TRUE;
        }
    }

    return FALSE;
}

FieldEntry * EventTypeEntry::GetField(PCHAR name)
{
    for (int i = 0; i < NumFields; i++) {

        FieldEntry * field = Fields[i];

        if (_stricmp(field->Name, name) == 0) {

            return field;
        }
    }

    return NULL;
}

int EventTypeEntry::GetFieldIndex(PCHAR name)
{
    for (int i = 0; i < NumFields; i++) {

        FieldEntry * field = Fields[i];

        if (_stricmp(field->Name, name) == 0) {

            return i;
        }
    }

    return -1;
}


bool EventTypeEntry::ApplyFilter(FieldFilter * newFilter)
{
    FilterApplied = TRUE;

    if (filterCount >= MAX_FILTERS) {
        return false;
    }

    // Test whether any of the fields inside this type entry would match
    // at least the fieldNamePattern;

    for (int i = 0; i < NumFields; i++) {

        FieldEntry * field = Fields[i];

        if (newFilter->MatchFieldName(field->Name)) {

            fieldsFilterList[filterCount] = field;
            filterList[filterCount++] = newFilter;
            return TRUE;
        }
    }

    return FALSE;
}

void EventTypeEntry::ClearFilters()
{
    filterCount = 0;
}

void EventTypeEntry::AddNewField(FieldEntry * field) {
    if (NumFields < MAX_FIELDS) {

        Fields[NumFields++] = field;
    }
}

void EventTypeEntry::UpdateFieldsOffsets() {

    int offset = 0;
    ExtendedFieldsCount = 0;

    for (int i = 0; i < NumFields; i++) {

        FieldEntry * field = Fields[i];

        field->ExtendedFieldIndex = 0;


        if (field->Type == FIELD_TYPE_GENERIC_TYPE) {

            if (field->SymType != NULL) {

                if (field->Offset == 0) {
                    field->Offset = offset;
                }
                field->Size = GetFieldSize(field->SymType->BasicType);
                offset = field->Offset + GetFieldSize(field->SymType->BasicType);
            }

        } else {

            if (field->Offset == 0) {
                field->Offset = offset;
            }
            field->Size = GetFieldSize(field->Type);
            offset = field->Offset + GetFieldSize(field->Type);
        }

        if (field->Type & FIELD_TYPE_VARIABLE_SIZE) {

            field->ExtendedFieldIndex = ExtendedFieldsCount++;
        }
    }
    size = offset;
}

ULONG_PTR SWITCH_TO_METADATA_CURSOR()
{
    ULONG_PTR savedMetadataSize = MetadataSize;
    MetadataSize = 0;
    return savedMetadataSize;
}

void RESTORE_CURSOR(ULONG_PTR savedCursor)
{
    MetadataSize = savedCursor;
}


bool EventTypeEntry::FilterMatch()
{
    if ((SystemHeaderType != NULL) && (SystemHeaderType != this)) {

        ULONG_PTR savedMetadataSize = MetadataSize;
        MetadataSize = 0;
        bool success = SystemHeaderType->FilterMatch();
        MetadataSize = savedMetadataSize;

        if (success && (filterCount == 0)) {

            return TRUE;
        }
    }

    if (FilterApplied && (filterCount == 0)) {

        return FALSE;
    }


    for (int i = 0; i < filterCount; i++) {

        FieldEntry * field = fieldsFilterList[i];

        if (field->Type & FIELD_TYPE_VARIABLE_ANY_STRING) {

            int index = (int)field->GetFieldNumericValue();

            char * str = NULL;

            if (index) {

                str = GetExtendedString(index);
            }

            if (!filterList[i]->MatchFieldValue(str)) {
                return FALSE;
            }

        } else {

            if (!filterList[i]->MatchFieldValue(field->GetFieldNumericValue())) {
                return FALSE;
            }
        }
    }

    return TRUE;
}

static int argIndexOffset = 0;

int PrintEventField(void * context, char *pszOut, int bufferSize, int aln, int wid, char fmt, int argIdx)
{
    EventTypeEntry * typeEntry = (EventTypeEntry *) context;
    argIdx += argIndexOffset;

    if (argIdx >= typeEntry->NumFields) {

        return 0;
    }

    FieldEntry * field = typeEntry->Fields[argIdx];
    int retValue = 0;
    char * str = NULL;

    if (field->Type == FIELD_TYPE_GENERIC_TYPE) {

        //  Force fetching the symtype if needed
        field->GetFieldNumericValue();

        PCHAR str = field->SymType->GetStringSymbol(field->Offset);

        if (str != NULL) {

            if (wid > 0) {
                if (aln < wid) {
                    aln = wid;
                }
                retValue = _snprintf(pszOut, bufferSize, "%*.*s", aln, wid, str);
            }
            else {
                retValue = _snprintf(pszOut, bufferSize, "%*s", aln, str);
            }

            free(str);
        }

    } else if (field->Type & FIELD_TYPE_VARIABLE_ANY_STRING) {

        int index = (int)field->GetFieldNumericValue();
        char * str = typeEntry->GetExtendedString(index);

        if (wid > 0) {
            if (aln < wid) {
                aln = wid;
            }
            retValue = _snprintf(pszOut, bufferSize, "%*.*s", aln, wid, str);
        }
        else {
            retValue = _snprintf(pszOut, bufferSize, "%*s", aln, str);
        }

    } else {

        if (aln < wid) {
            aln = wid;
        }

        if (fmt == 'x') {
            if (wid > 0) {
                retValue = _snprintf(pszOut, bufferSize, "%0*x", aln,
                            field->GetFieldNumericValue());
            }
            else {
                retValue = _snprintf(pszOut, bufferSize, "%*x", aln,
                            field->GetFieldNumericValue());
            }
        }
        else {
            retValue = _snprintf(pszOut, bufferSize, "%*d", aln,
                        field->GetFieldNumericValue());
        }

    }

    return retValue;
}

void EventTypeEntry::Format(int formatStringIndex, int argOffset)
{
    CHAR msg[512];
    argIndexOffset = argOffset + 1;
    char * text = GetExtendedString(formatStringIndex);

    FormatCSOutput(this, text, msg, sizeof(msg),PrintEventField, NULL);
    ExtOut("%s", msg);
}


void EventTypeEntry::PrintDescription()
{
    if (Descriptor == NULL) return;

    CHAR msg[512];
    argIndexOffset = 0;

    FormatCSOutput(this, Descriptor, msg, sizeof(msg),PrintEventField, NULL);
    ExtOut("%s", msg);
}

void EventTypeEntry::WalkFields(EventingEnumerator * enumerator) {

    if ((SystemHeaderType != NULL) && (SystemHeaderType != this) && (MetadataSize != 0)) {

        ULONG_PTR savedMetadataSize = MetadataSize;
        MetadataSize = 0;
        SystemHeaderType->WalkFields(enumerator);
        MetadataSize = savedMetadataSize;
    }

    for (int i = 0; i < NumFields; i++) {

        enumerator->FieldCallout(this, Fields[i]);
    }
}

char * GetExtendedStringUnsafe(int offset, int index)
{
    offset = ROUND_UP_TO_POWER2(offset, pointerSize);

    for (int i = 1; i < index; i++) {

        USHORT length;

        // copy the structure localy since it may not be aligned.

        memcpy(&length, EntryBuffer + offset, sizeof(USHORT));
        offset += length + sizeof(USHORT);
    }

    char * ptr = EntryBuffer + offset + sizeof(USHORT); // skip also the size of the string
    return ptr;
}


char * EventTypeEntry::GetExtendedString(int index)
{
    if ((index > 0) && (index <= ExtendedFieldsCount)) {

        int offset = (int)MetadataSize + size;

        offset = ROUND_UP_TO_POWER2(offset, pointerSize);

        for (int i = 1; i < index; i++) {

            USHORT length;

            // copy the structure localy since it may not be aligned.

            memcpy(&length, EntryBuffer + offset, sizeof(USHORT));
            offset += length + sizeof(USHORT);
        }

        char * ptr = EntryBuffer + offset + sizeof(USHORT); // skip also the size of the string
        return ptr;
    }

    return NULL;
}

void * EventTypeEntry::GetFieldArray(int index)
{
    if ((index >= 0) && (index <= ExtendedFieldsCount)) {

        int offset = (int)MetadataSize + size;

        offset = ROUND_UP_TO_POWER2(offset, pointerSize);

        for (int i = 1; i < index; i++) {

            USHORT length;

            // copy the structure localy since it may not be aligned.

            memcpy(&length, EntryBuffer + offset, sizeof(USHORT));
            offset += length;
        }

        return (char *)EntryBuffer + offset;
    }

    return NULL;
}


void EventTypeEntry::EnumerateEntries(EventingEnumerator * enumerator, UINT64 address, ULONG count) {

    ULONG readSize = size;

    if (readSize > sizeof(EntryBuffer)) {

        readSize = sizeof(EntryBuffer);
    }

    for (ULONG j = 0; j < count; j++) {

        TraceRead(address, EntryBuffer, (ULONG)readSize);
        MetadataSize = 0;

        if (enumerator->ActiveEntryCallout(this, FALSE)) {

            for (int i = 0; i < NumFields; i++) {

                enumerator->FieldCallout(this, Fields[i]);
            }
            enumerator->ActiveEntryCallout(this, TRUE);
        }

        address += size;
    }
}

//
//  SourceEntry class implementation
//

SourceEntry::SourceEntry()
{
    Name=NULL;
}

SourceEntry::~SourceEntry()
{

    if (Name) {
        free(Name);
    }
}

void SourceEntry::EnumerateEntries(EventingEnumerator * enumerator, ControllerObject *controller) {

    if (StorageHandle == 0) {

        if (enumerator->ActiveSourceCallout(this, FALSE, controller)) {

            EventTypeEntry * typeEntry = controller->FindType(EventTypeHandle);

            if (typeEntry != NULL) {

                typeEntry->EnumerateEntries(enumerator,
                    DebuggerBufferAddress,
                    (ULONG)Count);
            }

            enumerator->ActiveSourceCallout(this, TRUE, controller);
        }
    }
}

//
//  EventingEnumerator class implementation
//


EventingEnumerator::EventingEnumerator()
{
    FiltersCount = 0;
    Filters = NULL;
    SourcePattern = NULL;
    usedStorages = 0;
}

bool EventingEnumerator::AddStorageFilter(ULONG64 storageHandle)
{
    if (usedStorages >= MAX_STORAGE_FILTERS) return false;

    StorageHandles[usedStorages++] = storageHandle;
    return true;
}

bool EventingEnumerator::MatchStorageHandle(ULONG64 storageHandle)
{
    if (SourcePattern == NULL) return true;

    for (int i = 0; i < usedStorages; i++) {

        if (StorageHandles[i] == storageHandle) return true;
    }

    return false;
}


bool EventingEnumerator::ApplyFilters(FieldFilter ** filters, int Count) {

    FiltersCount = Count;
    Filters = filters;
    return TRUE;
}

bool EventingEnumerator::ApplySourceSelector(StringPattern * sourcePattern) {

    SourcePattern = sourcePattern;

    return TRUE;
}

bool EventingEnumerator::TypeCallout(EventTypeEntry * entryDescriptor){

    for (int i = 0; i < FiltersCount; i++) {

        if (!entryDescriptor->ApplyFilter(Filters[i])) {

            // This filter does not apply for the basic type
            // test it against the header

            if (!SystemHeaderType->TestFilter(Filters[i])) {
                return FALSE;
            }
        }
    }

    return TRUE;
}

bool EventingEnumerator::MedataCallout(ControllerObject *controller)
{
    if (SourcePattern) {

        ClearStorageFilters();

        for (int i = 0; i < controller->SourcesCount; i++) {

            SourceEntry *src = controller->RegisteredSources[i];

            if (SourcePattern->IsMatch(src->Name)) {

                AddStorageFilter(src->StorageHandle);
            }
        }
    }

    return TRUE;
}

bool EventingEnumerator::StorageCallout(UINT64 storageAddress, bool finished)
{
    if ((SourcePattern == NULL) || MatchStorageHandle(storageAddress)) return TRUE;

    return FALSE;
}



//
//  Controller objects managements
//

ControllerObject * Controllers[MAX_CONTROLLERS];
int ControllersCount = 0;

ControllerObject * AllocateController(UINT64 handle,
                                      UINT64 contextHandle,
                                      UINT64 storageAddress,
                                      UINT64 storageListHead)
{
    if (ControllersCount >= MAX_CONTROLLERS) {

        return NULL;
    }

    ControllerObject * ctrl = new ControllerObject(handle,
                                                   contextHandle,
                                                   storageAddress,
                                                   storageListHead);

    Controllers[ControllersCount++] = ctrl;
    return ctrl;
}

void FlushControllers()
{
    for (int i = 0; i < ControllersCount; i++) {

        delete Controllers[i];
        Controllers[i] = NULL;
    }

    ControllersCount = 0;
}
ControllerObject::ControllerObject(UINT64 handle,
                                   UINT64 contextHandle,
                                   UINT64 storageAddress,
                                   UINT64 storageListHead)
{
    TypesCount = 0;
    EnumCount = 0;
    SourcesCount = 0;
    ControllerHandle = handle;
    RepositoryAddress = storageAddress;
    StorageListHead = storageListHead;
    ContextHandle = contextHandle;

    for (int i = 0; i < MAX_FIELDS; i++) {

        RegisteredFieldsTypes[i] = NULL;
        RegisteredSymbolicValues[i] = NULL;
    }
}

ControllerObject::~ControllerObject() {

    FlushTypeArray();
    FlushSourceArray();
}

void ControllerObject::AddTempField(FieldEntry * field)
{
    for (int i = 0; i < MAX_FIELDS; i++) {

        if (RegisteredFieldsTypes[i] == NULL) {

            RegisteredFieldsTypes[i] = field;
            return;
        }
    }
    ERRORBREAK("Registering field failed\n");
}

void ControllerObject::AddTempField(SymbolicValue * field)
{
    for (int i = 0; i < MAX_FIELDS; i++) {

        if (RegisteredSymbolicValues[i] == NULL) {

            RegisteredSymbolicValues[i] = field;
            return;
        }
    }
    ERRORBREAK("Registering field failed\n");
}

void ControllerObject::PopulateFields(EnumType * type)
{
    for (int i = MAX_FIELDS - 1; i >= 0 ; i--) {

        if ((RegisteredSymbolicValues[i] != NULL) &&
            (RegisteredSymbolicValues[i]->ParentKey == type->Key)) {

            type->AddSymbolicValue(RegisteredSymbolicValues[i]);
            RegisteredSymbolicValues[i] = NULL;
        }
    }
}


void ControllerObject::PopulateFields(EventTypeEntry * type)
{
    for (int i = MAX_FIELDS - 1; i >= 0 ; i--) {

        if ((RegisteredFieldsTypes[i] != NULL) &&
            (RegisteredFieldsTypes[i]->ParentKey == type->Key)) {

            type->AddNewField(RegisteredFieldsTypes[i]);
            RegisteredFieldsTypes[i] = NULL;
        }
    }

    type->UpdateFieldsOffsets();
}


EventTypeEntry * ControllerObject::FindType(ULONG64 Key)
{
    for (int i = 0; i < TypesCount; i++) {

        if (RegisteredTypes[i]->Key == Key) {
            return RegisteredTypes[i];
        }
    }
    return NULL;
}

void ControllerObject::AddewType(EventTypeEntry * newType)
{
    if (TypesCount < MAX_TYPES) {

        RegisteredTypes[TypesCount++] = newType;
    }
}


EnumType * ControllerObject::FindEnum(ULONG64 Key)
{
    for (int i = 0; i < EnumCount; i++) {

        if (RegisteredEnums[i]->Key == Key) {
            return RegisteredEnums[i];
        }
    }
    return NULL;
}

void ControllerObject::AddNewEnum(EnumType * newEnum)
{
    if (EnumCount < MAX_TYPES) {

        RegisteredEnums[EnumCount++] = newEnum;
    }
}


void ControllerObject::FlushTypeArray()
{

    for (int i = 0; i < TypesCount; i++) {

        delete RegisteredTypes[i];
    }
    TypesCount = 0;

    for (int i = 0; i < EnumCount; i++) {

         delete RegisteredEnums[i];
    }
    EnumCount = 0;

    for (int i = 0; i < MAX_FIELDS; i++) {

         RegisteredFieldsTypes[i] = NULL;
    }


    SystemHeaderType = NULL;
}

SourceEntry * ControllerObject::FindSource(ULONG64 Key)
{
    for (int i = 0; i < SourcesCount; i++) {

        if (RegisteredSources[i]->Key == Key) {
            return RegisteredSources[i];
        }
    }
    return NULL;
}

char * ControllerObject::GetControllerName()
{
    #define CONTROLLER_NAME_PREFIX "ControllerLog{"
    for (int i = 0; i < SourcesCount; i++) {
        if (strstr(RegisteredSources[i]->Name, "ControllerLog{") == RegisteredSources[i]->Name) {

            char * crt = RegisteredSources[i]->Name + strlen("ControllerLog{");
            char tmpname[128];
            char * cursor = tmpname;
            char * end = cursor + sizeof(tmpname) - 1;
            while (*crt && (cursor < end)) {

                if (isalnum(*crt)) {
                    *cursor = *crt;
                } else {
                    if (*crt == '}') {

                        if (char * pos = strchr(crt, ':')) {
                            crt = pos;

                        } else {
                            break;
                        }
                    }
                    *cursor = '_';
                }

                crt++;
                cursor++;
            }
            *cursor = 0;
            return _strdup(tmpname);
        }
    }
    return NULL;
}


void ControllerObject::AddNewSource(SourceEntry * newSource)
{
    if (SourcesCount < MAX_SOURCES) {

        RegisteredSources[SourcesCount++] = newSource;
    }
}

void ControllerObject::FlushSourceArray()
{

    for (int i = 0; i < SourcesCount; i++) {

        delete RegisteredSources[i];
    }

    SourcesCount = 0;
}

void ControllerObject::WalkTypes(EventingEnumerator * enumerator)
{
    for (int i = 0; i < TypesCount; i++) {

        enumerator->TypeCallout(RegisteredTypes[i]);
    }
}

void ControllerObject::WalkSources(EventingEnumerator * enumerator)
{
    for (int i = 0; i < SourcesCount; i++) {

        enumerator->SourcesCallout(RegisteredSources[i]);
    }
}

void ControllerObject::WalkActiveSourcesEntries(EventingEnumerator * enumerator)
{
    for (int i = 0; i < SourcesCount; i++) {

        RegisteredSources[i]->EnumerateEntries(enumerator, this);
    }
}

void ControllerObject::ReadSource(UINT64 entryAddress)
{
    HRESULT status;

    SSOURCE_DESCRIPTOR log;

    EXT_CHECK(StructSOURCE_DESCRIPTOR.Read(entryAddress, &log));

    SourceEntry * sourceEntry;
    sourceEntry = new SourceEntry();

    if (sourceEntry != NULL) {

        sourceEntry->Name = _strdup(EntryBuffer + StructMEMORY_HEADER.size + StructSOURCE_DESCRIPTOR.size);
        sourceEntry->Key = entryAddress - StructMEMORY_HEADER.size;
        sourceEntry->StorageHandle = log.StorageHandle;
        sourceEntry->ControlFlags = (ULONG)log.ControlFlags;
        sourceEntry->EventTypeHandle = log.EventTypeHandle;
        sourceEntry->DebuggerBufferAddress = log.DebuggerBufferAddress;
        sourceEntry->Count = log.Count;
        sourceEntry->EntrySize = log.EntrySize;

        AddNewSource(sourceEntry);
    }

    return ;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information for reading source structures\n");
    return ;
}

void ControllerObject::ReadEventDescriptor(UINT64 entryAddress)
{
    HRESULT status;

    SEVENT_DESCRIPTOR log;

    EXT_CHECK(StructEVENT_DESCRIPTOR.Read(entryAddress, &log));

    EventTypeEntry * TypeEntry;
    TypeEntry = new EventTypeEntry();

    if (TypeEntry != NULL) {

        TypeEntry->Key = entryAddress - StructMEMORY_HEADER.size;
        TypeEntry->NumFields = 0;
        TypeEntry->size = StructEVENT_DESCRIPTOR.size;
        TypeEntry->ExtendedFieldsCount = 2;
        TypeEntry->Name = _strdup(TypeEntry->GetExtendedString((int)log.Name));

        if (log.Description > 0) {

            TypeEntry->Descriptor = _strdup(TypeEntry->GetExtendedString((int)log.Description));
        }

        if (SystemHeaderType == NULL) {

            if (_stricmp(TypeEntry->Name, "System.MEMORY_HEADER") == 0) {
                SystemHeaderType = TypeEntry;
            }

        }

        AddewType(TypeEntry);
        PopulateFields(TypeEntry);
    }

    return ;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
    return ;
}

void ControllerObject::ReadEnumDescriptor(UINT64 entryAddress)
{
    HRESULT status;

    SENUM_DESCRIPTOR log;

    EXT_CHECK(StructENUM_DESCRIPTOR.Read(entryAddress, &log));

    EnumType * TypeEntry;
    TypeEntry = new EnumType();

    if (TypeEntry != NULL) {

        TypeEntry->Key = entryAddress - StructMEMORY_HEADER.size;

        TypeEntry->BasicType = (int)log.Type;
        TypeEntry->Name = _strdup(GetExtendedStringUnsafe(
                                    StructMEMORY_HEADER.size + StructENUM_DESCRIPTOR.size,
                                    (int)log.Name));

        AddNewEnum(TypeEntry);
        PopulateFields(TypeEntry);
    }

    return ;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
    return ;
}

void ControllerObject::ReadValueDescriptor(UINT64 entryAddress, UINT64 parent)
{
    HRESULT status;

    SEVENT_VALUE_DESCRIPTOR log;

    EXT_CHECK(StructEVENT_VALUE_DESCRIPTOR.Read(entryAddress, &log));

    SymbolicValue * fieldEntry;
    fieldEntry = new SymbolicValue;

    if (fieldEntry != NULL) {

        fieldEntry->Name = _strdup(GetExtendedStringUnsafe(
                                    StructMEMORY_HEADER.size + StructEVENT_VALUE_DESCRIPTOR.size,
                                    (int)log.Name));
        fieldEntry->Value = (int)log.Value;
        fieldEntry->FlagChar = (UCHAR)log.FlagLetter;
        fieldEntry->ParentKey = parent;

        EnumType * parentType = FindEnum(parent);

        if (parentType == NULL) {

            AddTempField(fieldEntry);

        } else {

            parentType->AddSymbolicValue(fieldEntry);
        }
    }

    return;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
}


void ControllerObject::ReadFieldDescriptor(UINT64 entryAddress, UINT64 parent)
{
    HRESULT status;

    SEVENT_FIELD_DESCRIPTOR log;

    EXT_CHECK(StructEVENT_FIELD_DESCRIPTOR.Read(entryAddress, &log));

    FieldEntry * fieldEntry;
    fieldEntry = new FieldEntry;

    if (fieldEntry != NULL) {

        fieldEntry->Name = _strdup(GetExtendedStringUnsafe(
                                    StructMEMORY_HEADER.size + StructEVENT_FIELD_DESCRIPTOR.size,
                                    (int)log.Name));

        fieldEntry->Offset = (int)log.Offset;
        fieldEntry->Type = (int)log.Type;
        fieldEntry->ParentKey = parent;

        EventTypeEntry * parentType = FindType(parent);

        if (parentType == NULL) {

            AddTempField(fieldEntry);

        } else {

            parentType->AddNewField(fieldEntry);
        }
    }

    return;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
}

void ControllerObject::ReadGenericFieldDescriptor(UINT64 entryAddress, UINT64 parent)
{
    HRESULT status;

    SEVENT_GENERIC_TYPE_DESCRIPTOR log;

    EXT_CHECK(StructEVENT_GENERIC_TYPE_DESCRIPTOR.Read(entryAddress, &log));

    FieldEntry * fieldEntry;
    fieldEntry = new FieldEntry;

    if (fieldEntry != NULL) {

        fieldEntry->Name = _strdup(GetExtendedStringUnsafe(
                                    StructMEMORY_HEADER.size + StructEVENT_GENERIC_TYPE_DESCRIPTOR.size,
                                    (int)log.Name));

        fieldEntry->Offset = (int)log.Offset;
        fieldEntry->Type = FIELD_TYPE_GENERIC_TYPE;
        fieldEntry->ParentKey = parent;
        fieldEntry->TypeKey = log.GenericTypeHandle;
        fieldEntry->SymType = FindEnum(log.Type);
        fieldEntry->Controller = this;

        EventTypeEntry * parentType = FindType(parent);

        if (parentType == NULL) {

            AddTempField(fieldEntry);

        } else {

            parentType->AddNewField(fieldEntry);
        }
    }

    return;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
}


UINT64 ControllerObject::ReadMemoryHeader(EventingEnumerator * enumerator,
                                          UINT64 entryAddress)
{
    HRESULT status;

    SMEMORY_HEADER log;
    ULONG64 CrtOffset;

    EntryHeader header;

    ReadSize = sizeof(EntryBuffer);

    EXT_CHECK(StructMEMORY_HEADER.Read(entryAddress, &log));

    header.address = entryAddress;
    header.size = (int)log.Size;
    header.timestamp = log.Timestamp;
    header.Flags = (int)log.Flags;
    header.TID = (int)log.TID;
    header.Cpu = (int)log.Cpu;

    header.StackSize = 0;
    header.StackAddress = 0;;

    CrtOffset = StructMEMORY_HEADER.size;

    if ((log.Size) < ReadSize) {

        ReadSize = log.Size;
    }

    Stacksize = 0;
    MetadataSize = (ULONG_PTR)CrtOffset;
    EXT_CHECK(TraceRead(entryAddress, EntryBuffer, (ULONG)ReadSize));


    if (log.Flags & RECORD_STACK_TRACES) {

        Stacksize = *(ULONG_PTR*)(EntryBuffer + (ULONG_PTR)CrtOffset) + 1;

        header.StackSize = (int)Stacksize;
        header.StackAddress = entryAddress + CrtOffset;

        Stacksize *= sizeof(ULONG_PTR);
        CrtOffset += Stacksize;
        MetadataSize = (ULONG_PTR)CrtOffset;
    }

    if (log.Flags == RECORD_EVENT_TYPE) {


        // Ignore the other internal structures that are not relevant for this extension

    } else if (log.Flags == RECORD_EVENT_FIELD) {

        // Ignore the other internal structures that are not relevant for this extension


    } else if (log.Flags == RECORD_EVENT_SOURCE) {

        // Ignore the other internal structures that are not relevant for this extension

    } else if (log.Flags & RECORD_EVENT_METADATA_FLAG) {

        // Ignore the other internal structures that are not relevant for this extension

    } else if (log.Flags & RECORD_EVENT_TYPE_ARRAY_FLAG) {

        EventTypeEntry * type = FindType(log.Type);

        if (type != NULL) {
            type->EnumerateEntries(enumerator, entryAddress + CrtOffset, (ULONG)log.TID);
        }

    } else {
        EventTypeEntry * type = FindType(log.Type);
        enumerator->EntryCallout(&header, type);
    }

    return log.Link;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
    return 0;
}

UINT64 ControllerObject::ReadMetadataMemoryHeader(EventingEnumerator * enumerator,
                                                  UINT64 entryAddress)
{
    HRESULT status;

    SMEMORY_HEADER log;
    ULONG64 CrtOffset;

    EntryHeader header;

    ReadSize = sizeof(EntryBuffer);

    EXT_CHECK(StructMEMORY_HEADER.Read(entryAddress, &log));

    header.address = entryAddress;
    header.size = (int)log.Size;
    header.timestamp = log.Timestamp;
    header.Flags = (int)log.Flags;
    header.TID = (int)log.TID;
    header.Cpu = (int)log.Cpu;

    CrtOffset = StructMEMORY_HEADER.size;

    if ((log.Size) < ReadSize) {

        ReadSize = log.Size;
    }

    Stacksize = 0;
    MetadataSize = (ULONG_PTR)CrtOffset;
    EXT_CHECK(TraceRead(entryAddress, EntryBuffer, (ULONG)ReadSize));

    ExtVerb("Reading entry %p\n", entryAddress);

    if (log.Flags & RECORD_STACK_TRACES) {

        Stacksize = *(ULONG_PTR*)(EntryBuffer + (ULONG_PTR)CrtOffset) + 1;
        Stacksize *= sizeof(ULONG_PTR);
        CrtOffset += Stacksize;
        MetadataSize = (ULONG_PTR)CrtOffset;
    }

    if (log.Flags == RECORD_EVENT_TYPE) {

        ReadEventDescriptor(entryAddress + CrtOffset);

    } else if (log.Flags == RECORD_EVENT_FIELD) {

        ReadFieldDescriptor(entryAddress + CrtOffset, log.Type);

    } else if (log.Flags == RECORD_EVENT_SOURCE) {

        ReadSource(entryAddress + CrtOffset);

    } else if (log.Flags == RECORD_EVENT_GENERIC_FIELD) {

        ReadGenericFieldDescriptor(entryAddress + CrtOffset, log.Type);

    } else if (log.Flags == RECORD_EVENT_ENUM) {

        ReadEnumDescriptor(entryAddress + CrtOffset);

    } else if (log.Flags == RECORD_EVENT_VALUE) {

        ReadValueDescriptor(entryAddress + CrtOffset, log.Type);
    }

    return log.Link;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
    return 0;
}


UINT64 ControllerObject::ReadMemoryZone(EventingEnumerator * enumerator, UINT64 zoneAddress)
{
    HRESULT status;

    SMEMORY_ZONE log;

    EXT_CHECK(StructMEMORY_ZONE.Read(zoneAddress, &log));
    UINT64 Blocks = (USHORT)log.ReadyList;

    while (Blocks) {

        Blocks = ReadMetadataMemoryHeader(enumerator, zoneAddress + Blocks);
    }

    Blocks = (USHORT)log.ReadyList;

    while (Blocks) {

        Blocks = ReadMemoryHeader(enumerator, zoneAddress + Blocks);
    }

    return log.Link;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
    return 0;
}

UINT64 ControllerObject::ReadStorage(EventingEnumerator * enumerator,
                                     UINT64 storageAddress,
                                     bool isRepository)
{
    HRESULT status;
    SMEMORY_STORAGE log;

    if (storageAddress == 0) {

        return 0;
    }

    EXT_CHECK(StructMEMORY_STORAGE.Read(storageAddress, &log));

    ULONG64 CrtZone = log.MemoryZoneLink;

    //
    //  We need to walk the repository storages anyway, regardless the
    //  the aditional filtering on storages.
    //

    if (enumerator->StorageCallout(storageAddress, FALSE) || isRepository) {

        ExtVerb("Walking storage %p\n", storageAddress);

        while (CrtZone) {

            if (enumerator->ZoneCallout(CrtZone, FALSE)) {

                ULONG64 NextZone = ReadMemoryZone(enumerator, CrtZone);

                enumerator->ZoneCallout(CrtZone, TRUE);

                if (CrtZone == NextZone) {

                    break;
                }

                CrtZone = NextZone;

            } else {

                break;
            }
        }

        enumerator->StorageCallout(storageAddress, TRUE);
    } else {
        ExtVerb("Skipping storage %p\n", storageAddress);
    }


    return log.Link;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
    return 0;
}


ULONG64 SwitchToDomainAddressSpace(ULONG64 Context)
{
    if (Context == 0) {

        // Nothing to do if paging is not enabled

        return 0;
    }

    //  TODO: Implement me to handle the paging case

    return 0;
}

void RevertToSystemDomainAddressSpace(ULONG64 Context)
{
    if (Context == 0) {

        // Nothing to do if paging is not enabled

        return;
    }

    //  TODO: Implement me to handle the paging case
}


void ControllerObject::FetchMetadata(EventingEnumerator * enumerator)
{
    ReadStorage(enumerator, RepositoryAddress, true);
    WalkTypes(enumerator);
    WalkSources(enumerator);
    WalkActiveSourcesEntries(enumerator);
}

void ControllerObject::WalkEntries(EventingEnumerator * enumerator)
{
    UINT64 CrtStorage;

    CrtStorage = StorageListHead;

    while (CrtStorage) {

        CrtStorage = ReadStorage(enumerator, CrtStorage, false);
    }
}


void WalkTracingDatabase(EventingEnumerator * enumerator, bool typesOnly)
{
    HRESULT status;
    UINT64 controllerAddress = 0;
    SSOURCE_CONTROLLER log;
    ULONG64 SystemContextHandle;
    ULONG64 ControllerLink;

    FlushControllers();

    if (!enumerator->SystemCallout(FALSE)) {

        return;
    }

    EXT_CHECK(g_ExtSymbols->GetOffsetByName(kernel_SourceController, &controllerAddress));

    EXT_CHECK(StructSOURCE_CONTROLLER.Read(controllerAddress, &log));

    ControllerLink = log.ExternalControllers;

    ControllerObject * ctrl = AllocateController(controllerAddress,
                                                 0,
                                                 log.SourceRepository,
                                                 log.StorageList);

    if (enumerator->ControllerCallout(ctrl, FALSE)) {


        if (ctrl != NULL) {

            ctrl->FetchMetadata(enumerator);

            if (enumerator->MedataCallout(ctrl) && !typesOnly) {

                ctrl->WalkEntries(enumerator);
            }
        }

        enumerator->ControllerCallout(ctrl, TRUE);
    }

    while ((DumpKernelOnly == FALSE) && (ControllerLink != 0)){

        SEXTERNAL_CONTROLLER_DESCRIPTOR extController;
        EXT_CHECK(StructEXTERNAL_CONTROLLER_DESCRIPTOR.Read(ControllerLink, &extController));

        ControllerLink = extController.Link;

        controllerAddress = extController.ControllerHandle;
        SystemContextHandle = SwitchToDomainAddressSpace(extController.ContextHandle);

        EXT_CHECK(StructSOURCE_CONTROLLER.Read(controllerAddress, &log));

        ControllerObject * ctrl = AllocateController(controllerAddress,
                                                     extController.ContextHandle,
                                                     log.SourceRepository,
                                                     log.StorageList);

        if (enumerator->ControllerCallout(ctrl, FALSE)) {

            if (ctrl != NULL) {

                ctrl->FetchMetadata(enumerator);

                if (enumerator->MedataCallout(ctrl) && !typesOnly) {

                    ctrl->WalkEntries(enumerator);
                }
            }

            enumerator->ControllerCallout(ctrl, TRUE);
        }

        RevertToSystemDomainAddressSpace(SystemContextHandle);

    }

    enumerator->SystemCallout(TRUE);
    return;

Exit:
    //  Error path

    ERRORBREAK("Invalid symbols information\n");
    return;
}


UINT64 eventTypeHandle;
FieldFilter * filters[MAX_FILTERS];
int filtersCount = 0;

void CleanupFilters()
{
    for (int i = 0; i < filtersCount; i++) {
        delete (filters[i]);
    }
    filtersCount = 0;
}


class SourceFlagsEnumerator : public EventingEnumerator
{

    StringPattern * FilterCollector;
    StringPattern * FilterSource;
    UINT Flags;

public:

    SourceFlagsEnumerator(StringPattern * filterCollector, StringPattern * filterSource, UINT flags) {
        FilterCollector = filterCollector;
        FilterSource = filterSource;
        Flags = flags;
    }

    bool virtual MedataCallout(ControllerObject *controller);
};


void
WriteULONG(ULONG64 address, ULONG value)
{
    g_ExtData->WriteVirtualUncached(address, &value, sizeof(value), NULL);
}


bool SourceFlagsEnumerator::MedataCallout(ControllerObject *controller)
{
    if (FilterCollector) {

        if (!FilterCollector->IsMatch(controller->GetControllerName())) {

            return FALSE;
        }
    }

    if (FilterSource) {

        for (int i = 0; i < controller->SourcesCount; i++) {

            SourceEntry *src = controller->RegisteredSources[i];

            if (FilterSource->IsMatch(src->Name)) {

                ExtOut("Matched source (%s) (%s) %p %p\n",
                    controller->GetControllerName(),
                    src->Name,
                    src->Key,
                    (src->Key + _FieldsSOURCE_DESCRIPTOR[5].offset + StructMEMORY_HEADER.size));

                WriteULONG((src->Key + _FieldsSOURCE_DESCRIPTOR[5].offset + StructMEMORY_HEADER.size),
                            Flags);
            }
        }
    }

    return FALSE;
}


void Tracing(PCSTR args)
{
    PCSTR defaultVisibleFields = "|Timestamp|Cpu|TID|";
    HRESULT status;
    TypeFilterEnumerator * typeFilter = NULL;
    CleanupFilters();
    FlushTransforms();
    eventTypeHandle = 0;
    TypeEntryCollector * collector = NULL;
    char * sortField = NULL;
    EventingEnumerator * dump = NULL;
    StringPattern * sourcePattern = NULL;
    bool DumpSummary = false;

    //
    //  Parse the remaining arguments. This stuff needs to be cleaned up or moved
    //  to dscript at some point.
    //

    DumpAllEvents = FALSE;
    DumpStackTraces = FALSE;
    DumpKernelOnly = FALSE;
    DumpDescriptions = FALSE;
    SKIP_WHITESPACES(args);

    while (*args != '\0') {

        SKIP_WHITESPACES(args);

        // process argument
        if (*args == '-' || *args == '/') {
            args++;
            switch (toupper(*args++)) {
              case 'G':{

                if ((*args == 'c') || (*args == 'C'))
                {
                    EXT_CHECK(SetBound("Microsoft_Singularity_V1_Services_DiagnosisService::DeferedCommand", 2));
                    ExtOut("Kernel GC collection triggered. Press \'g\' to resume the execution.\n"
                        "It will break in debugger when GS collection completes\n");
                }
                else
                {
                    SKIP_WHITESPACES(args);

                    //  Write the GC logs buffer, with the memory size in MBytes
                    WriteCLRProfileFile(args, false);
                }
                goto CleanupAndExit;
              }
              break;

              case 'E':{
                bool enableKernel;
                bool breakOnRecycle = false;
                if ((*args == 'k') || (*args == 'K'))
                {
                    enableKernel = true;
                }
                else if ((*args == 's') || (*args == 'S'))
                {
                    enableKernel = false;
                }
                else
                {
                    Usage();
                    goto CleanupAndExit;
                }
                //  Consume the 'k' or 's' and skip whitespaces to the memory value
                args += 1;
                SKIP_WHITESPACES(args);
                int MemorySize = (int)GetValue(args, false);

                // There is an optional 'break' keyword
                SKIP_WHITESPACES(args);
                if (_stricmp(args, "break") == 0)
                {
                    breakOnRecycle = true;
                }

                //  Set the appropriate profiler buffer, with the memory size in MBytes & flags
                if (enableKernel)
                {
                    EnableKernelGCProfiler(MemorySize * 1024 * 1024, breakOnRecycle);
                }
                else
                {
                    //  Set the SIP profiler buffer, with the memory size in MBytes
                    EnableSIPGCProfiler(MemorySize * 1024 * 1024, breakOnRecycle);
                }
                goto CleanupAndExit;
              }
              break;

              case 'D':{

                if ((*args == 'k') || (*args == 'K'))
                {
                    //  Consume the k and skip whitespaces to the memory value
                    args += 1;
                    SKIP_WHITESPACES(args);

                    //  Disable the profiler by setting the buffer size to 0
                    DisableKernelGCProfiler();
                }
                else if ((*args == 's') || (*args == 'S'))
                {
                    //  Consume the s and skip whitespaces to the memory value
                    args += 1;
                    SKIP_WHITESPACES(args);
                    int MemorySize = (int)GetValue(args, true);

                    //  Disable the SIP profiler by resetting the buffer size
                    EnableSIPGCProfiler(0, false);
                }
                else
                {
                    Usage();
                }
                goto CleanupAndExit;
              }
              break;

              case 'M':
              break;

              case 'N':

                DumpSummary = true;
              break;

              case 'A':{
                DumpAllEvents = TRUE;
              }
              break;

              case 'P':{
                  DumpDescriptions = TRUE;
              }
              break;

              case 'K':{
                DumpStackTraces= TRUE;
              }
              break;

              case 'X':{
                DumpKernelOnly = TRUE;
              }
              break;

              case 'Y':{
                ParseStringFormatTransform(args);
              }
              break;

              case 'L':{
                ParseSymbolLookupTransform(args);
              }
              break;

              case 'R':{

                defaultVisibleFields = NULL;
                ParseVisibleFields(args);
              }
              break;

              case 'T':{
                SKIP_WHITESPACES(args);

                DumpAllEvents = TRUE;
                StringPattern * filter = new StringPattern();
                if (filter == NULL) {
                    goto CleanupAndExit;
                }

                args = filter->ParseInput((char*)args);

                typeFilter = new TypeFilterEnumerator();

                if (typeFilter == NULL) {

                    delete filter;
                    goto CleanupAndExit;
                }

                typeFilter->SetPattern(filter);
                WalkTracingDatabase(typeFilter, TRUE);

              }
              break;
              case 'O':{

                SKIP_WHITESPACES(args);

                DumpAllEvents = TRUE;
                char * sortField = ReadToken(args);

                if (sortField != NULL) {

                    collector = new TypeEntryCollector(0, sortField);
                }

              }
              break;
              case 'Z':{

                SKIP_WHITESPACES(args);

                StringPattern * filterCollector = new StringPattern();

                if (filterCollector == NULL) {
                    goto CleanupAndExit;
                }

                StringPattern * filterSource = new StringPattern();

                if (filterSource == NULL) {

                    delete filterCollector;
                    goto CleanupAndExit;
                }

                args = filterCollector->ParseInput((char*)args);
                args = filterSource->ParseInput((char*)args);

                ULONG Flags = (int)GetValue(args, true);

                SourceFlagsEnumerator *enumerator = new SourceFlagsEnumerator(filterCollector,
                                                                              filterSource,
                                                                              Flags);

                if (enumerator != NULL) {

                    WalkTracingDatabase(enumerator, TRUE);
                    delete enumerator;
                }

                delete filterSource;
                delete filterCollector;
                goto CleanupAndExit;
              }

              break;
              case 'S':{

                SKIP_WHITESPACES(args);
                DumpAllEvents = TRUE;

                sourcePattern = new StringPattern();

                if (sourcePattern == NULL) {

                    goto CleanupAndExit;
                }

                args = sourcePattern->ParseInput((char*)args);
              }

              break;
              case 'F':{
                SKIP_WHITESPACES(args);

                DumpAllEvents = TRUE;
                FieldFilter * filter = new FieldFilter();
                if (filter == NULL) {
                    goto CleanupAndExit;
                }

                args = filter->ParseInput((char*)args);

                filters[filtersCount++] = filter;
              }
              break;
            }
            SKIP_WHITESPACES(args);
        } else {
            Usage();
            break;
        }
    }

    if (defaultVisibleFields != NULL) {

        defaultVisibleFields = NULL;
        ParseVisibleFields(args);
    }

    if (typeFilter != 0) {

        for (int i = 0; i < typeFilter->Array->InUse; i++) {

            dump = new DumpType(typeFilter->Array->Array[i]);

            if (dump) {

                dump->ApplyFilters(filters, filtersCount);
                dump->ApplySourceSelector(sourcePattern);

                if (collector == NULL) {

                    //
                    //  If no other order criteria has been established
                    //  default to sort by timestamp
                    //

                    collector = new TypeEntryCollector(0, "Timestamp");
                }

                if (collector) {

                    collector->TypeHandle = typeFilter->Array->Array[i];
                    collector->cascadeEnumerator = dump;
                    collector->GroupByController = TRUE;

                    WalkTracingDatabase(collector, FALSE);
                } else {
                    WalkTracingDatabase(dump, FALSE);
                }

                delete dump;
                dump = NULL;
            }
        }

    } else {

        dump = new DumpTracing();
        if (dump) {

            ((DumpTracing*)dump)->DumpSummary = DumpSummary;

            dump->ApplyFilters(filters, filtersCount);
            dump->ApplySourceSelector(sourcePattern);

            if (collector == NULL) {

                //
                //  If no other order criteria has been established
                //  default to sort by timestamp
                //

                collector = new TypeEntryCollector(0, "Timestamp");
            }

            if (collector) {

                collector->TypeHandle = 0;
                collector->cascadeEnumerator = dump;
                if (DumpSummary) {
                    collector->GroupByController = TRUE;
                }

                WalkTracingDatabase(collector, FALSE);

            } else {

                WalkTracingDatabase(dump, !DumpAllEvents);
            }
        }
    }

Exit:
CleanupAndExit:

    if (sortField) free(sortField);
    if (dump) delete dump;
    if (typeFilter) delete typeFilter;
    if (sourcePattern) delete sourcePattern;

    return;
}



EXT_DECL(diagnose) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    bool KernelProfile = true;
    pointerSize = (g_ExtControl->IsPointer64Bit() == S_OK) ? 8 : 4;

    SKIP_WHITESPACES(args);

    if (*args == '\0')
    {
        Usage();

    } else {

        Tracing(args);
    }

    EXT_LEAVE();    // Macro includes: return status;
}

