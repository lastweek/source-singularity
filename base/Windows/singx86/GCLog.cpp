/////////////////////////////////////////////////////////////////////////////
//
//  GCLog.cpp - GC diagnosis extension support
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

#include "singx86.h"
#include "diagnose.h"

static char szSymbol[512];

class GCTracing : public EventingEnumerator
{
    //  High level diagnosis enumeration. Each override will skip walking through actuall entries

public:

    GCTracing ();

    //  Override callouts

    bool virtual TypeCallout(EventTypeEntry * entryDescriptor);
    bool virtual ControllerCallout(ControllerObject *controller, bool finished);
    bool virtual EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor);
    bool virtual MedataCallout(ControllerObject *controller);
    void virtual SourcesCallout(SourceEntry * source);
    bool virtual StorageCallout(UINT64 storageAddress, bool finished);

private:
    void InitFile();

    FILE * f;

    ControllerObject * controller;

    char fname[128];

    UINT64 RootsHandle;
    UINT64 GenerationsHandle;
    UINT64 ObjectHandle;
    UINT64 StackHandle;
    UINT64 TypeHandle;
    UINT64 IntervalHandle;
    UINT64 AllocationHandle;
    UINT64 FunctionHandle;

    UINT64 EventStorageHandle;
    UINT64 TypeStorageHandle;
    bool ParsingMetadata;

};

#define MAX_PAGE_SIZE 4096

char PageBuffer[MAX_PAGE_SIZE];


void DumpMemory(PCSTR fname)
{
    HRESULT status;

    ULONG64 pageTable;
    ULONG64 pageCount;
    ULONG64 pageSize = MAX_PAGE_SIZE;

    EXT_CHECK(FindBound("FlatPages::pageTable", &pageTable));
    EXT_CHECK(FindBound("FlatPages::pageCount", &pageCount));
    // EXT_CHECK(FindBound("nt!MemoryManager::PageSize", &pageSize));  not available

    ExtOut("%p %p %p", pageTable, pageCount, pageSize);

    FILE * f;
    f = fopen( fname, "wb" );

    if (f != NULL)
    {

        for (ULONG64 i = 0; i < pageCount; i++) {

            ULONG Descriptor;

            if ((i % 1000) == 0) {
                ExtOut(".", pageSize * i, Descriptor);
            }

            if (g_ExtData->ReadVirtual(pageTable + i * sizeof(Descriptor),
                            &Descriptor, sizeof(Descriptor), NULL) != S_OK)
            {
                ExtOut("Error reading descriptor\n");
                break;
            }

            if (g_ExtData->ReadVirtual(pageSize * i, PageBuffer, (ULONG)pageSize, NULL) == S_OK)
            {
//                ExtOut("%p %lx\n", pageSize * i, Descriptor);
                fwrite(PageBuffer, (ULONG)pageSize, 1, f);
            } else {

                memset(PageBuffer, 0, (ULONG)pageSize);
                fwrite(PageBuffer, (ULONG)pageSize, 1, f);
                ExtOut("%p %lx error\n", pageSize * i, Descriptor);
            }

        }

        fclose(f);
    }
    return;

Exit:
    //  Error path

    ExtOut("Invalid symbols information\n");
    return;
}

void WriteFileRange (int Base, int Size, PCSTR fname) {
    FILE * f;
    f = fopen( fname, "wb" );

    if (f != NULL)
    {
        char buff[2048];

        while (Size)
        {
            int readsize = Size;
            if (readsize > sizeof(buff))
            {
                readsize = sizeof(buff);
            }

            if (g_ExtData->ReadVirtual(Base, buff, readsize, NULL) == S_OK)
            {
                fwrite(buff, readsize, 1, f);
            }
            Size -= readsize;
            Base += readsize;
        }

        fclose(f);
    }
}


void
EnableKernelGCProfiler(ULONG64 MemorySize, bool breakOnRecycle)
{
    HRESULT status;
    ULONG64 ExistingKernelBufferSize;
    ULONG64 KernelBufferAddress;
    BOOL OKSymbols = FALSE;

    EXT_CHECK(FindBound("Class_Microsoft_Singularity_GCProfilerLogger::c_StorageHandle",
        &KernelBufferAddress));

    if (KernelBufferAddress != 0)
    {
        ULONG64 isProfiling;
        EXT_CHECK(FindBound("Microsoft_Singularity_V1_Services_DiagnosisService::KernelBufferSize", &ExistingKernelBufferSize));
        OKSymbols = TRUE;
        ExtOut("GC Profiling is already in use for kernel (%ld MBytes buffer)\n",
            ExistingKernelBufferSize/ 1024 / 1024);
        ExtOut("The default value cannot be changed dynamically without rebooting the system\n");
        EXT_CHECK(FindBound("System_GC::isProfiling", &isProfiling));

        if (isProfiling == 0)
        {
            EXT_CHECK(SetBound("System_GC::isProfiling", 1));
            ExtOut("Re-enabling with the existing settings\n");
        }

        goto Exit;
    }

    ExtOut("Enabling kernel GC profiler with %ld MBytes buffer size and %sbreak on recycle\n",
           (long)(MemorySize/ 1024 / 1024),
           (breakOnRecycle ? "" : "NO "));
    EXT_CHECK(SetBound("Microsoft_Singularity_V1_Services_DiagnosisService::DeferedCommand", 1));
    EXT_CHECK(SetBound("Microsoft_Singularity_V1_Services_DiagnosisService::KernelBufferSize", MemorySize));
    EXT_CHECK(SetBound("Microsoft_Singularity_V1_Services_DiagnosisService::KernelProfileOptions", breakOnRecycle));
    OKSymbols = TRUE;

Exit:

    if (!OKSymbols)
    {
        ExtOut("Error accessing variables. Please check symbols for kernel\n");
    }

    return;
}

void
DisableKernelGCProfiler()
{
    HRESULT status;
    ULONG64 KernelBufferAddress;
    BOOL OKSymbols = FALSE;

    EXT_CHECK(FindBound("gKernelBufferStart", &KernelBufferAddress));
    OKSymbols = TRUE;

    if (KernelBufferAddress == 0)
    {
        ExtOut("GC profiling is not enabled\n");

        goto Exit;
    }

    EXT_CHECK(SetBound("System_GC::isProfiling", 0));
    OKSymbols = TRUE;
    ExtOut("Kernel GC profiling disabled\n");

Exit:

    if (!OKSymbols)
    {
        ExtOut("Error accessing variables. Please check symbols for kernel\n");
    }

    return;
}




void
EnableSIPGCProfiler(ULONG64 MemorySize, bool breakOnRecycle)
{
    HRESULT status;
    BOOL OKSymbols = FALSE;

    EXT_CHECK(SetBound("Microsoft_Singularity_V1_Services_DiagnosisService::SIPBufferSize", MemorySize));
    EXT_CHECK(SetBound("Microsoft_Singularity_V1_Services_DiagnosisService::SIPProfileOptions", breakOnRecycle));

    if (MemorySize == 0)
    {
        ExtOut("Disabling SIP GC profiler for new processes\n");
    }
    else
    {
        ExtOut("Enabling SIP GC profiler with %ld MBytes buffer size and %sbreak on recycle\n",
               (long)(MemorySize/ 1024 / 1024),
               (breakOnRecycle ? "" : "NO "));
        ExtOut("New processes starting from now on will have GC profiler enabled\n");
    }

    OKSymbols = TRUE;

Exit:

    if (!OKSymbols)
    {
        ExtOut("Error accessing variables. Please check symbols for kernel\n");
    }

    return;
}


//
//  GC CLR writter
//

PCSTR prefixName;

GCTracing::GCTracing ()
{
    f = NULL;
    EventStorageHandle = 0;
    TypeStorageHandle = 0;

}

void GCTracing::InitFile()
{
    if (f == NULL) {
        char fname[128];

        char * controllerName = controller->GetControllerName();

        _snprintf(fname, sizeof(fname), "%s_%s.LOG", prefixName, controllerName);

        free(controllerName);
        f = fopen( fname, "wt" );
    }
}
bool GCTracing::TypeCallout(EventTypeEntry * entryDescriptor)
{
    if (!EventingEnumerator::TypeCallout(entryDescriptor)) {

        if (!EventingEnumerator::TypeCallout(SystemHeaderType)) {
            return FALSE;
        }
    }

    if (_stricmp(entryDescriptor->Name, "System.GC_ROOTS") == 0) {

        RootsHandle = (UINT64)entryDescriptor->Key;

    } else if (_stricmp(entryDescriptor->Name, "System.GC_GENERATIONS") == 0) {

        GenerationsHandle = (UINT64)entryDescriptor->Key;

    } else if (_stricmp(entryDescriptor->Name, "System.GC_OBJECT") == 0) {

        ObjectHandle = (UINT64)entryDescriptor->Key;

    } else if (_stricmp(entryDescriptor->Name, "System.GC_STACK") == 0) {

        StackHandle = (UINT64)entryDescriptor->Key;

    } else if (_stricmp(entryDescriptor->Name, "System.GC_TYPE") == 0) {

        TypeHandle = (UINT64)entryDescriptor->Key;

    } else if (_stricmp(entryDescriptor->Name, "System.GC_INTERVAL") == 0) {

        IntervalHandle = (UINT64)entryDescriptor->Key;

    } else if (_stricmp(entryDescriptor->Name, "System.GC_ALLOCATION") == 0) {

        AllocationHandle = (UINT64)entryDescriptor->Key;

    } else if (_stricmp(entryDescriptor->Name, "System.GC_FUNCTION") == 0) {

        FunctionHandle = (UINT64)entryDescriptor->Key;
    }

    return TRUE;

}

bool GCTracing::ControllerCallout( ControllerObject *ctrl, bool finished)
{
    if (finished) {
        controller = NULL;
    } else {
        controller = ctrl;
    }
    if (f != NULL) fclose(f);
    f = NULL;
    EventStorageHandle = 0;
    TypeStorageHandle = 0;
    ParsingMetadata = TRUE;
    return TRUE;
}

bool GCTracing::MedataCallout(ControllerObject *controller)
{
    ParsingMetadata = FALSE;
    if (TypeStorageHandle == 0) return FALSE;
    return TRUE;
}

bool GCTracing::StorageCallout(UINT64 storageAddress, bool finished)
{
    if (ParsingMetadata) return TRUE;

    if (EventStorageHandle == storageAddress) {

        ExtOut("Walking event storage %p\n", storageAddress);
        return TRUE;
    }

    if (TypeStorageHandle == storageAddress) {

        ExtOut("Walking type storage %p\n", storageAddress);
        return TRUE;
    }

    return FALSE;
}


void GCTracing::SourcesCallout(SourceEntry * source)
{
    if (MatchPatternString(exact, source->Name, "GC.Events")) {
        EventStorageHandle = source->StorageHandle;
        ExtOut("GC source:    %s: (Key=%p, Storage=%p, ControlFlags=%lx)\n",
            source->Name,
            (UINT64)source->Key,
            source->StorageHandle,
            source->ControlFlags);
    } else if (MatchPatternString(exact, source->Name, "GC.TypeDefinitions")) {
        TypeStorageHandle = source->StorageHandle;
        ExtOut("GC source:    %s: (Key=%p, Storage=%p, ControlFlags=%lx)\n",
            source->Name,
            (UINT64)source->Key,
            source->StorageHandle,
            source->ControlFlags);
    }
}


bool GCTracing::EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor)
{
    HRESULT status;

    if (entryDescriptor == NULL) {

        return FALSE;
    }

    if (entryDescriptor->Key == TypeHandle) {

        InitFile();
        PCHAR str = entryDescriptor->GetExtendedString(1);

        fprintf(f, "t 0x%p 0 %s\n", (ULONG)entryDescriptor->GetField("TypeId")->GetFieldNumericValue(), str);

    } else if (entryDescriptor->Key == FunctionHandle) {
        InitFile();

        ULONG64 displacement = 0;
        ULONG64 funcPtr = entryDescriptor->GetField("IP")->GetFieldNumericValue();
        status = g_ExtSymbols->GetNameByOffset(funcPtr,
                                               szSymbol,
                                               arrayof(szSymbol),
                                               NULL,
                                               &displacement);
        if (status == S_OK) {
            fprintf(f, "f 0x%p %s+0x%I64x_0x%p (UNKNOWN ARGUMENTS) 0 0\n",
                (ULONG)entryDescriptor->GetField("FnIdx")->GetFieldNumericValue(),
                szSymbol,
                displacement,
                (ULONG)funcPtr);
        } else {

            fprintf(f, "f 0x%p FUNCTION_EIP 0x%p (UNKNOWN ARGUMENTS) 0 0\n",
                        (ULONG)entryDescriptor->GetField("FnIdx")->GetFieldNumericValue(),
                        (ULONG)funcPtr);
        }
    } else if (entryDescriptor->Key == IntervalHandle) {

        InitFile();
        fprintf(f, "i 0x%I64x\n", entryDescriptor->GetField("Delta")->GetFieldNumericValue());

    } else if (entryDescriptor->Key == AllocationHandle) {

        InitFile();

        ULONG tid;
        ULONG_PTR ctx = SWITCH_TO_METADATA_CURSOR();

            FieldEntry * field = SystemHeaderType->GetField("TID");
            tid = (ULONG)field->GetFieldNumericValue();

        RESTORE_CURSOR(ctx);

        fprintf(f, "! 0x%p 0x%p 0x%p\n",
                tid,
                (ULONG)entryDescriptor->GetField("Object")->GetFieldNumericValue(),
                (ULONG)entryDescriptor->GetField("StkNo")->GetFieldNumericValue());

    } else if (entryDescriptor->Key == StackHandle) {

        InitFile();
        fprintf(f, "n 0x%lx 1 0x%lx 0x%lx",
                (ULONG)entryDescriptor->GetField("StkNo")->GetFieldNumericValue(),
                (ULONG)entryDescriptor->GetField("TypeId")->GetFieldNumericValue(),
                (ULONG)entryDescriptor->GetField("Size")->GetFieldNumericValue());
        FieldEntry * array = entryDescriptor->GetField("fncList");
        void * buffer = entryDescriptor->GetFieldArray((int)array->GetFieldNumericValue());

        int count = array->GetArraySize(buffer);

        if (count >= 2) {

            for (int i = 0; i < count - 2; i++) {
                ULONG fnc = (ULONG)array->GetFieldNumericValue(buffer, i);
                fprintf(f, " 0x%lx", fnc);
            }
        }

        fprintf(f, "\n");
    } else if (entryDescriptor->Key == RootsHandle) {

        InitFile();
        fprintf(f, "r");

        FieldEntry * array = entryDescriptor->GetField("Roots");
        void * buffer = entryDescriptor->GetFieldArray((int)array->GetFieldNumericValue());

        int count = array->GetArraySize(buffer);

        for (int i = 0; i < count; i++) {

            ULONG Address = (ULONG)array->GetFieldNumericValue(buffer, i);
            fprintf(f, " 0x%lx", Address);
        }

        fprintf(f, "\n");
    } else if (entryDescriptor->Key == GenerationsHandle) {

        InitFile();
        fprintf(f, "g");

        FieldEntry * array = entryDescriptor->GetField("Genrations");
        void * buffer = entryDescriptor->GetFieldArray((int)array->GetFieldNumericValue());

        int count = array->GetArraySize(buffer);

        for (int i = 0; i < count; i++) {

            ULONG Address = (ULONG)array->GetFieldNumericValue(buffer, i);
            fprintf(f, " %ld", Address);
        }
        fprintf(f, "\n");

    } else if (entryDescriptor->Key == ObjectHandle) {

        InitFile();
        fprintf(f, "o");

        FieldEntry * array = entryDescriptor->GetField("ParameterList");
        void * buffer = entryDescriptor->GetFieldArray((int)array->GetFieldNumericValue());

        int count = array->GetArraySize(buffer);

        for (int i = 0; i < count; i++) {

            ULONG Address = (ULONG)array->GetFieldNumericValue(buffer, i);
            fprintf(f, " 0x%lx", Address);
        }

        fprintf(f, "\n");
    }

    return TRUE;

}


void
WriteCLRProfileFile(PCSTR fname, bool Kernel)
{
    prefixName = fname;

    TypeEntryCollector * collector = new TypeEntryCollector(0, "Timestamp");
    if (collector) {

        GCTracing * dump = new GCTracing();

        if (dump) {

            collector->TypeHandle = 0;
            collector->GroupByController = TRUE;
            collector->cascadeEnumerator = dump;

            WalkTracingDatabase(collector, FALSE);

            delete dump;
        }

        delete collector;
    }
}



