/////////////////////////////////////////////////////////////////////////////
//
//  diagnose.h - Definitions for diag.cpp
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

//  Some arbitrary constants to simplify dealing with variable size arrays.
//  Some cleanup would be necessary

#define MAX_FIELDS 32
#define MAX_TYPES 1024
#define MAX_FILTERS 8
#define MAX_SOURCES 1024
#define MAX_CONTROLLERS 1024

#define ROUND_UP_TO_POWER2( x, n ) (((x) + ((n)-1)) & ~((n)-1))
#define ROUND_DOWN_TO_POWER2( x, n ) ((x) & ~((n)-1))

extern volatile BOOL BreakOnInternalError;

void inline ERRORBREAK(char * msg)
{
    ExtVerb(msg);

#ifdef ISA_IX86
    if (BreakOnInternalError) {

        __asm int 3;
    }
#endif
}

struct FieldEntry;
struct EventTypeEntry;
struct SourceEntry;
struct FieldFilter;
struct ControllerObject;

//  Structure to cache information for entry enumeration. The values are retrieved from the
//  entry header

struct EntryHeader {
    UINT64 address;
    int size;
    int Flags;
    UINT64 timestamp;
    int TID;
    int Cpu;
    int StackSize;
    UINT64 StackAddress;
};

struct StringPattern;

#define MAX_STORAGE_FILTERS 256

class EventingEnumerator
{

public:

    FieldFilter ** Filters;
    int FiltersCount;
    StringPattern * SourcePattern;

    ULONG64 usedStorages;
    ULONG64 StorageHandles[MAX_STORAGE_FILTERS];

    EventingEnumerator();

    bool virtual ApplyFilters(FieldFilter ** filters, int Count);
    bool ApplySourceSelector(StringPattern * sourcePattern);

    void ClearStorageFilters(){usedStorages = 0;}
    bool AddStorageFilter(ULONG64 storageHandle);
    bool MatchStorageHandle(ULONG64 storageHandle);

    //  System enumeration callout. The function is called twice, one before enumeration of all
    //  controllers begin, and ones after the last controller has been parsed.

    bool virtual SystemCallout(bool finished)
    { return TRUE;}

    //  Controler enumeration callout. The function is called twice, one before enumeration of sources,
    //  storages andtypes begin. If override, by returning false, will inform the enumeration
    //  that wlaking the controller's structures must be skipped for this controller. In that case
    //  there will be no second call to notify enumeration complete

    bool virtual ControllerCallout(ControllerObject *controller, bool finished)
    {     usedStorages = 0; return TRUE;}

    //  Metadata callout. The function is called after all metadata has been loaded in controller
    //  Return TRUE if also walking entries is needed, false if no walk is further
    //  necessary on this controller.

    bool virtual MedataCallout(ControllerObject *controller);


    //  Storage enumeration callout. The function is called twice, one before enumeration zones
    //  inside the storage. If override, by returning false, will inform the enumeration that
    //  walking the storage's structures must be skipped. In that case there will be no
    //  second call to notify enumeration complete

    bool virtual StorageCallout(UINT64 storageAddress, bool finished);

    //  Zone enumeration callout. The function is called twice, one before enumeration zones
    //  inside the storage. If override, by returning false, will inform the enumeration that
    //  walking the storage's structures must be skipped. In that case there will be no
    //  second call to notify enumeration complete.

    bool virtual ZoneCallout(UINT64 zoneAddress, bool finished)
    { return TRUE;}

    //  Sources enumeration callout. There are two type of sources:
    //      a. Sources which log to regular memory storages.
    //      b. Sources which manages the updates in their's private maner (active sources)

    //  SourcesCallout is called to enumerate very source inside a controller. This is a leaf
    //  enumeration point, no other internal structures will follow this callback.

    void virtual SourcesCallout(SourceEntry * source){}

    //  Active sources will go through an enumeration also of the internal elements.
    //  They respect the same semantics as explained in controller, wrt. overriding the
    //  function. The second call when entries enumeration is completed does not occur if the
    //  override explicitely rejected the enumeration by returning false.

    bool virtual ActiveSourceCallout(SourceEntry * source, bool finished, ControllerObject *controller)
    { return TRUE;}

    //  Leaf enumeration point to notify about the presence of a new type that has been read
    //  from the corrent controller's repository

    bool virtual TypeCallout(EventTypeEntry * entryDescriptor);

    //  Callout for every entry in the storage, as they are parsed. Internally the override
    //  may also choose to walk the fields inside with a call to the method:
    //            entryDescriptor->WalkFields(this);
    //  Otherwise this is also a leaf call, the value of the entry is already loaded
    //  in the buffer so querying values, properties will assume the right context

    bool virtual EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor)
    { return TRUE;}

    //  Callout for active entries. The active entries to not have a the usual ENTRY_HEADER
    //  that everything else has, because the storage of such events are really the responsibility
    //  of the source. To also force the enumeration of fields for each entry the following call
    //  must be made in the override:
    //            entryDescriptor->WalkFields(this);

    bool virtual ActiveEntryCallout(EventTypeEntry * entryDescriptor, BOOL finished)
    { return TRUE;}

    //  The following callout is to notify about every field in a type / entry that gets enumerated.
    //  for regular entries these will not be invoked, unless in the EntryCallout or in
    //  ActiveEntryCallout the entryDescriptor->WalkFields(this) call is done.

    bool virtual FieldCallout(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor)
    { return TRUE;}
};


// TODO: redefinition of constants. Must be moved to a common place

#define RECORD_STACK_TRACES 0x0001

#define RECORD_LAYOUT_FLAGS (RECORD_STACK_TRACES)

#define FIELD_TYPE__int8 0x1    // 1
#define FIELD_TYPE__uint8 0x2    // 2
#define FIELD_TYPE__byte 0x2    // 2
#define FIELD_TYPE__int16 0x3    // 3
#define FIELD_TYPE__uint16 0x4    // 4
#define FIELD_TYPE__int32 0x5    // 5
#define FIELD_TYPE__int 0x5    // 5
#define FIELD_TYPE__uint32 0x6    // 6
#define FIELD_TYPE__int64 0x7    // 7
#define FIELD_TYPE__uint64 0x8    // 8
#define FIELD_TYPE__IntPtr 0x9    // 9
#define FIELD_TYPE__UIntPtr 0xa    // 10
#define FIELD_TYPE_GENERIC_TYPE 0xff

#define FIELD_TYPE__arrayType 0x8000
#define FIELD_TYPE__string 0x4000
#define FIELD_TYPE__szChar 0x2000

#define FIELD_TYPE_VARIABLE_SIZE (FIELD_TYPE__arrayType | FIELD_TYPE__string | FIELD_TYPE__szChar)
#define FIELD_TYPE_VARIABLE_ANY_STRING (FIELD_TYPE__string | FIELD_TYPE__szChar)

struct ArrayType
{
    USHORT Length;
    USHORT ItemSize;
    UINT Type;
    PVOID Buffer;
};


//
//  Filtering operations
//

enum PatternMatch{
    anywhere = 1,
    exact = 2,
    begin = 3
};

enum FilterOperation{
    all = 0,  // no test on value
    equal = 1,
    less = 2,
    greater = 3,
    different = 4,

    contains = 5 // for strings only
};

struct ControllerObject;

// Utility class for simple string pattern matching

struct StringPattern
{
    char * Pattern;
    PatternMatch MatchMode;

    StringPattern();
    ~StringPattern();

    void Cleanup();
    bool IsMatch(char * p);
    char * ParseInput(char * arg);
};

struct SymbolicValue {
    struct SymbolicValue * Next;
    PCHAR Name;
    ULONG64 Value;
    UCHAR FlagChar;
    ULONG64 ParentKey;

    SymbolicValue() {
        Name = NULL;
        Value = 0;
        FlagChar = 0;
        Next = NULL;
    }
    ~SymbolicValue(){ if (Name) free (Name);}
};

struct EnumType {

    UINT64 Key;
    int BasicType;
    ULONG64 FlagsMask;
    struct SymbolicValue * ValuesLists;
    int NumFlags;
    int PrintWidth;
    PCHAR Name;

    EnumType()
    {
        Key = 0;
        FlagsMask = 0;
        ValuesLists = NULL;
        NumFlags = 0;
        PrintWidth = 0;
        Name = NULL;
    }

    ~EnumType();

    void AddSymbolicValue(SymbolicValue * symValue);
    int GetFieldPrintWidth();
    int PrintValue(int printWidth, int offset);
    ULONG64 GetFieldNumericValue(int offset);
    PCHAR GetStringSymbol(int offset);

};

struct FieldEntry {

    int Offset;
    int Type;
    int Size;
    PCHAR Name;
    UINT64 ParentKey;
    int ExtendedFieldIndex;
    unsigned int PrintWidth;
    UINT64 TypeKey;
    EnumType * SymType;
    ControllerObject * Controller;

    FieldEntry();
    ~FieldEntry();

    ULONG64 GetFieldNumericValue();
    ULONG64 PrintValue(EventTypeEntry * type);
    int GetFieldPrintWidth();

    int GetArraySize(void * buffer);
    ULONG64 GetFieldNumericValue(void * buffer, int index);

};

//
//  Utility class used in searching and filtering of entries in
//  either regular or active sources.
//
struct FieldFilter
{
    char * FieldNamePattern;
    char * StringValuePattern;
    INT64 NumericValuePattern;

    PatternMatch FieldMatchMode;
    FilterOperation Operation;

    FieldFilter();
    ~FieldFilter();

    void Cleanup();

    FieldFilter(PatternMatch matchMode,
                char * fieldPattern,
                FilterOperation op,
                UINT64 value,
                char * strValue);

    bool MatchFieldName(char * p);

    bool MatchFieldValue(INT64 value);
    bool MatchFieldValue(char * value);

    char * ParseInput(char * arg);
};

//  Simple variable size array implementation

struct VariableArray
{

    UINT64 *Array;
    int InUse;
    int Size;

    VariableArray();
    ~VariableArray();
    bool Add(UINT64 value);

private:
    bool Extend();
};



struct EventTypeEntry {

    UINT64 Key;
    int NumFields;
    FieldEntry * Fields[MAX_FIELDS];
    PCHAR Name;
    PCHAR Descriptor;

    int size;
    int ExtendedFieldsCount;

    FieldFilter * filterList[MAX_FILTERS];
    FieldEntry * fieldsFilterList[MAX_FILTERS];
    int filterCount;
    bool FilterApplied;

    EventTypeEntry();
    ~EventTypeEntry();

    void AddNewField(FieldEntry * field);
    bool TestFilter(FieldFilter * newFilter);
    bool ApplyFilter(FieldFilter * newFilter);
    void ClearFilters();
    bool FilterMatch();

    void UpdateFieldsOffsets();
    void WalkFields(EventingEnumerator * enumerator);
    char * GetExtendedString(int index);
    void * GetFieldArray(int index);
    void Format(int formatStringIndex, int argIndex);
    void PrintDescription();

    FieldEntry * GetField(PCHAR name);
    int GetFieldIndex(PCHAR name);
    void EnumerateEntries(EventingEnumerator * enumerator, UINT64 address, ULONG count);
};

struct SourceEntry {

    UINT64 Key;
    PCHAR Name;
    UINT64 StorageHandle;
    ULONG ControlFlags;

    //
    //  For active sources
    //

    UINT64 EventTypeHandle;
    UINT64 DebuggerBufferAddress;
    UINT64 Count;
    UINT64 EntrySize;

    SourceEntry();
    ~SourceEntry();

    void EnumerateEntries(EventingEnumerator * enumerator, ControllerObject *controller);

};


struct ControllerObject {

    //  Enumeration support local variables and definitions

    EventTypeEntry * RegisteredTypes[MAX_TYPES];
    int TypesCount;

    FieldEntry * RegisteredFieldsTypes[MAX_FIELDS];

    SourceEntry * RegisteredSources[MAX_SOURCES];
    int SourcesCount;

    EnumType * RegisteredEnums[MAX_TYPES];
    int EnumCount;
    SymbolicValue * RegisteredSymbolicValues[MAX_FIELDS];

    UINT64 ControllerHandle;
    UINT64 ContextHandle;
    UINT64 RepositoryAddress;
    UINT64 StorageListHead;

    ControllerObject(UINT64 handle,
                     UINT64 contextHandle,
                     UINT64 storageAddress,
                     UINT64 storageListHead);
    ~ControllerObject();


    void FetchMetadata(EventingEnumerator * enumerator);
    void WalkEntries(EventingEnumerator * enumerator);
    EventTypeEntry * FindType(ULONG64 Key);
    UINT64 ReadMemoryHeader(EventingEnumerator * enumerator, UINT64 entryAddress);
    char * GetControllerName();
    EnumType * FindEnum(ULONG64 Key);

private:

    void AddTempField(FieldEntry * field);
    void PopulateFields(EventTypeEntry * type);
    void AddewType(EventTypeEntry * newType);
    SourceEntry * FindSource(ULONG64 Key);
    void AddNewSource(SourceEntry * newSource);
    void WalkTypes(EventingEnumerator * enumerator);
    void WalkSources(EventingEnumerator * enumerator);
    void WalkActiveSourcesEntries(EventingEnumerator * enumerator);
    void ReadSource(UINT64 entryAddress);
    void ReadEventDescriptor(UINT64 entryAddress);
    void ReadFieldDescriptor(UINT64 entryAddress, UINT64 parent);
    void ReadGenericFieldDescriptor(UINT64 entryAddress, UINT64 parent);
    UINT64 ReadMetadataMemoryHeader(EventingEnumerator * enumerator, UINT64 entryAddress);
    UINT64 ReadMemoryZone(EventingEnumerator * enumerator, UINT64 zoneAddress);
    UINT64 ReadStorage(EventingEnumerator * enumerator, UINT64 storageAddress, bool isRepository);

    void AddNewEnum(EnumType * newEnum);
    void PopulateFields(EnumType * type);
    void AddTempField(SymbolicValue * field);
    void ReadEnumDescriptor(UINT64 entryAddress);
    void ReadValueDescriptor(UINT64 entryAddress, UINT64 parent);

    void FlushTypeArray();
    void FlushSourceArray();

};




//
//  Generic utility prototypes
//

extern EventTypeEntry * SystemHeaderType;

int GetFieldSize(int type);
char * GetFieldTypeName(int type);
bool MatchPatternString(PatternMatch matchMode, char * p, char* pattern);
char * ReadToken(PCSTR& args);

void FlushTransforms();
void ParseStringFormatTransform(PCSTR & args);
void ParseVisibleFields(PCSTR & args);
void ParseSymbolLookupTransform(PCSTR & args);

#define SKIP_WHITESPACES(arg)                                  \
    while (*(arg) == ' ' || *(arg) == '\t') (arg)++;

extern ULONG64 GetValue(PCSTR& args, bool fHex);
HRESULT FindBound(const char *symbol, ULONG64 *ptrval);
HRESULT SetBound(const char *symbol, ULONG64 ptrval);

//
//  Classes support for filtering, sorting and content dump
//


class DumpTracing : public EventingEnumerator
{
    //  High level diagnosis enumeration. Each override will skip walking through actuall entries

public:
    bool DumpSummary;

    DumpTracing() {CrtEntryIndex = 0; DumpSummary = false;}

    //  Override callouts

    bool virtual TypeCallout(EventTypeEntry * entryDescriptor);
    void virtual SourcesCallout(SourceEntry * source);
    bool virtual ActiveSourceCallout(SourceEntry * source, bool finished, ControllerObject *controller);
    bool virtual ControllerCallout(ControllerObject *controller, bool finished);
    bool virtual FieldCallout(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor);
    bool virtual EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor);

private:
    enum Lastprinted {
        controller,
        type,
        source,
        activesource
    };

    int CrtEntryIndex;
    Lastprinted LastItem;
    int PrintPhase;
    int FieldIndex;

};

class DumpType : public EventingEnumerator
{

public:

    UINT64 typeHandle;
    int printHeader;
    UINT64 lastTimeStamp;
    int CrtEntryIndex;

    DumpType(UINT64 handle);

    bool virtual FieldCallout(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor);

    bool virtual EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor);
    bool virtual PrintHeader(EventTypeEntry * entryDescriptor);
    bool virtual TypeCallout(EventTypeEntry * entryDescriptor);
    bool virtual ActiveEntryCallout(EventTypeEntry * entryDescriptor, BOOL finished);
    bool virtual ActiveSourceCallout(SourceEntry * source, bool finished, ControllerObject *controller);
};

class TypeFilterEnumerator : public EventingEnumerator
{

public:

    VariableArray * Array;
    StringPattern * Pattern;

    TypeFilterEnumerator();
    ~TypeFilterEnumerator();
    void SetPattern(StringPattern * pattern);
    bool virtual TypeCallout(EventTypeEntry * entryDescriptor);
};

class TypeEntryCollector : public TypeFilterEnumerator
{

public:

    char * sortField;
    UINT64 crtHandle;
    UINT64 TypeHandle;
    BOOL GroupByController;
    EventingEnumerator *cascadeEnumerator;
    ControllerObject * currentController;
    static const int FieldsWidth = 3;

    TypeEntryCollector(UINT64 typeHandle, char * field);
    ~TypeEntryCollector();

    bool virtual FieldCallout(EventTypeEntry * entryDescriptor, FieldEntry * fieldDescriptor);
    bool virtual EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor);
    bool virtual TypeCallout(EventTypeEntry * entryDescriptor);
    bool virtual ControllerCallout(ControllerObject *controller, bool finished);
    bool virtual SystemCallout(bool finished);
    bool virtual MedataCallout(ControllerObject *controller);
    void virtual SourcesCallout(SourceEntry * source);
    bool virtual StorageCallout(UINT64 storageAddress, bool finished);

private:
    void SortItems();
    void WalkItems(EventingEnumerator * enumerator);
};

class SourceCollector : public TypeEntryCollector
{

public:
    StringPattern *SourcePattern;
    UINT64 storageHandle;

    SourceCollector(char * sourceName, char * field);
    void virtual SourcesCallout(SourceEntry * source);
    bool virtual StorageCallout(UINT64 storageAddress, bool finished);

};

//
//  Function support for GC profiling
//


void DumpMemory(PCSTR fname);
void WriteFileRange (int Base, int Size, PCSTR fname);
void WriteCLRProfileFile(PCSTR fname, bool Kernel);
void EnableKernelGCProfiler(ULONG64 MemorySize, bool breakOnRecycle);
void DisableKernelGCProfiler();
void EnableSIPGCProfiler(ULONG64 MemorySize, bool breakOnRecycle);
extern ULONG_PTR MetadataSize;
extern char * MetadataInfo;



class MemoryRagesCollection : public VariableArray {
    int DiscardedRanges;
    UINT64 PreviousAddress;
    UINT64 PreviousSize;

public:

    MemoryRagesCollection() : VariableArray(){DiscardedRanges=0; PreviousAddress = 0; PreviousSize = 0;};
    void AddRange(UINT64 startRVA, UINT64 rangeSize);

    int GetEffectiveRanges(){return GetRangesCount() - DiscardedRanges;}
    UINT64 GetStartAddress(int i){return Array[i * 2];}
    UINT64 GetRangeSize(int i){return Array[i * 2 + 1];}
    int GetRangesCount(){return InUse / 2;}
    void CompactItems();
    UINT64 GetRVA(UINT64 address);
};

extern ULONG pointerSize;

ULONG_PTR SWITCH_TO_METADATA_CURSOR();
void RESTORE_CURSOR(ULONG_PTR savedCursor);

void WalkTracingDatabase(EventingEnumerator * enumerator, bool typesOnly);
UINT64 GetStackTrace(int index) ;

