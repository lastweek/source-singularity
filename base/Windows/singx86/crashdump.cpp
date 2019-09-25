/////////////////////////////////////////////////////////////////////////////
//
//  crashdump.cpp - Extension to save a dumpfile from debugger for offline analysis
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

#include "singx86.h"
#include "diag.h"

//
//  Global states controlling the extension options
//

BOOL IncludeExecutables;
BOOL IncludeRegisterReferences;
void AddMemoryReference(UINT64 address);
BOOL FullMemoryDump;

//
//  Cross-platform utility functions
//

USHORT GetTargetContextSize()
{
    switch (TargetMachine) {

        case IMAGE_FILE_MACHINE_AMD64:
            return sizeof(X64_CONTEXT);
            break;

        case IMAGE_FILE_MACHINE_I386:
            return sizeof(X86_CONTEXT);
            break;

        case IMAGE_FILE_MACHINE_ARM:
            return sizeof(ARM_CONTEXT);
            break;
    }

    ExtOut("Unknown processor architecture. Exiting\n");
    return 0;
}

UINT64 GetStackPointer(VOID * threadContext)
{
    switch (TargetMachine) {

        case IMAGE_FILE_MACHINE_AMD64:
            return ((X64_CONTEXT*)threadContext)->Rsp;
            break;

        case IMAGE_FILE_MACHINE_I386:
            return ((X86_CONTEXT*)threadContext)->Esp;
            break;

        case IMAGE_FILE_MACHINE_ARM:
            return ((ARM_CONTEXT*)threadContext)->Pc;
            break;
    }

    return 0;
}

void FetchRegisterReferences(VOID * dbgCOntext)
{
    if (IncludeRegisterReferences) {

        switch (TargetMachine) {

            case IMAGE_FILE_MACHINE_AMD64: {

                X64_CONTEXT * ctx = (X64_CONTEXT *)dbgCOntext;

                AddMemoryReference(ctx->Rip);
                AddMemoryReference(ctx->Rsi);
                AddMemoryReference(ctx->Rbx);
                AddMemoryReference(ctx->Rcx);
                AddMemoryReference(ctx->Rdx);
                AddMemoryReference(ctx->Rax);
                AddMemoryReference(ctx->Rdi);
                AddMemoryReference(ctx->R8);
                AddMemoryReference(ctx->R9);
                AddMemoryReference(ctx->R10);
                AddMemoryReference(ctx->R11);
                AddMemoryReference(ctx->R12);
                AddMemoryReference(ctx->R13);
                AddMemoryReference(ctx->R14);
                AddMemoryReference(ctx->R15);
                break;
            }

            case IMAGE_FILE_MACHINE_I386: {

                X86_CONTEXT * ctx = (X86_CONTEXT *)dbgCOntext;

                AddMemoryReference(ctx->Eip);
                AddMemoryReference(ctx->Esi);
                AddMemoryReference(ctx->Ebx);
                AddMemoryReference(ctx->Ecx);
                AddMemoryReference(ctx->Edx);
                AddMemoryReference(ctx->Eax);
                AddMemoryReference(ctx->Edi);
                break;
            }

            case IMAGE_FILE_MACHINE_ARM: {

                ARM_CONTEXT * ctx = (ARM_CONTEXT *)dbgCOntext;

                AddMemoryReference(ctx->R0);
                AddMemoryReference(ctx->R1);
                AddMemoryReference(ctx->R2);
                AddMemoryReference(ctx->R3);
                AddMemoryReference(ctx->R4);
                AddMemoryReference(ctx->R5);
                AddMemoryReference(ctx->R6);
                AddMemoryReference(ctx->R7);
                AddMemoryReference(ctx->R8);
                AddMemoryReference(ctx->R9);
                AddMemoryReference(ctx->R10);
                AddMemoryReference(ctx->R11);
                AddMemoryReference(ctx->R12);
                AddMemoryReference(ctx->Lr);
                AddMemoryReference(ctx->Pc);
                break;
            }
        }
    }
}

void LoadThreadContext(void * dbgContext, SpillContext * context)
{
    switch (TargetMachine) {

        case IMAGE_FILE_MACHINE_AMD64: {

            X64_CONTEXT * ctx = (X64_CONTEXT *)dbgContext;

            ctx->ContextFlags = (CONTEXT_CONTROL | CONTEXT_INTEGER);

            ctx->Rdi = context->di;
            ctx->Rsi = context->si;
            ctx->Rbx = context->bx;
            ctx->Rdx = context->dx;
            ctx->Rcx = context->cx;
            ctx->Rax = context->ax;
            ctx->R8 = context->r8;
            ctx->R9 = context->r9;
            ctx->R10 = context->r10;
            ctx->R11 = context->r11;
            ctx->R12 = context->r12;
            ctx->R13 = context->r13;
            ctx->R14 = context->r14;
            ctx->R15 = context->r15;

            ctx->Rbp = context->bp;
            ctx->Rip = context->ip;
            ctx->EFlags = (ULONG32)context->fl;
            ctx->Rsp = context->sp;
            break;
        }

        case IMAGE_FILE_MACHINE_I386: {

            X86_CONTEXT * ctx = (X86_CONTEXT *)dbgContext;

            ctx->ContextFlags = (CONTEXT_CONTROL | CONTEXT_INTEGER);

            ctx->Edi = (ULONG32)context->di;
            ctx->Esi = (ULONG32)context->si;
            ctx->Ebx = (ULONG32)context->bx;
            ctx->Edx = (ULONG32)context->dx;
            ctx->Ecx = (ULONG32)context->cx;
            ctx->Eax = (ULONG32)context->ax;

            ctx->Ebp = (ULONG32)context->bp;
            ctx->Eip = (ULONG32)context->ip;
            ctx->EFlags = (ULONG32)context->fl;
            ctx->Esp = (ULONG32)context->sp;
            break;
        }

        case IMAGE_FILE_MACHINE_ARM: {

            ARM_CONTEXT * ctx = (ARM_CONTEXT *)dbgContext;

            ctx->ContextFlags = (CONTEXT_CONTROL | CONTEXT_INTEGER);

            ctx->R0 = (ULONG32)context->r0;
            ctx->R1 = (ULONG32)context->r0;
            ctx->R2 = (ULONG32)context->r0;
            ctx->R3 = (ULONG32)context->r0;
            ctx->R4 = (ULONG32)context->r0;
            ctx->R5 = (ULONG32)context->r0;
            ctx->R6 = (ULONG32)context->r0;
            ctx->R7 = (ULONG32)context->r0;
            ctx->R8 = (ULONG32)context->r0;
            ctx->R9 = (ULONG32)context->r0;
            ctx->R10 = (ULONG32)context->r0;
            ctx->R11 = (ULONG32)context->r0;
            ctx->R12 = (ULONG32)context->r0;

            ctx->Sp = (ULONG32)context->sp;
            ctx->Lr = (ULONG32)context->lr;
            ctx->Pc = (ULONG32)context->pc;
            ctx->Cpsr = (ULONG32)context->cpsr;
            break;
        }
    }
}


//
//  Define these for the SAL annotations in dbghelp.h
//

#define unknown
#define __out_xcount(x)

#include "dbghelp.h"

static HRESULT Usage()
{
    ExtOut("Usage:\n"
           "    !crashdump [options]\n"
           "Options:\n"
           "    -s <file_name> : Save the dump in the provided file\n"
           "    -f : Include all memory pages in the dump\n"
           "    -x : Include images in dumps\n"
           "    -r : Include register references\n"
           "    -t : Start tracing mode. All memory references used by compliant extensions are logged\n"
           "         to be available for offline usage\n"
          );

    return S_FALSE;
}


//
//  Never include a range larger than 100 M in the dumpfile
//

#define MAX_MEMORY_RANGE 100*1024*1024
#define MEMORY_PAGE_SIZE 4096

struct _MEMORY_STREAM {
    UINT32                  MemoryCount;
    MINIDUMP_MEMORY_DESCRIPTOR  Memory[1];
};

struct CRASH_DUMP_HEADER
{
    MINIDUMP_HEADER         Header;
    MINIDUMP_DIRECTORY      Directories[5];

    //
    //  Include the fixed size structures here to make it easier to deal with
    //

    MINIDUMP_SYSTEM_INFO    SystemInfo;
    MINIDUMP_EXCEPTION_STREAM ExceptionInfo;
};


//
//  The crashdump extension accesses PEImage and process information structures
//  Create the accessors for them
//

struct PEImage {

    ULONG64 VirtualAddress;
    ULONG64 loadedSize;
    ULONG64 timeDateStamp;
    ULONG64 checkSum;
};


FieldType PEImageFields[] = {
    FIELD(PEImage, VirtualAddress),
    FIELD(PEImage, loadedSize),
    FIELD(PEImage, timeDateStamp),
    FIELD(PEImage, checkSum),
    FIELDEND(),
};

StructType PEImageStruct = StructType(kernel_PEImage,
                                       sizeof(PEImage), PEImageFields);


struct ProcessInfo {

    ULONG64 image;
    ULONG64 imageName;
};


FieldType ProcessInfoFields[] = {
    FIELD(ProcessInfo, image),
    FIELD(ProcessInfo, imageName),
    FIELDEND(),
};

// kernel name is potentially fixed up in StructType::Initialize
StructType ProcessInfoStruct = StructType(kernel_Process,
                                       sizeof(ProcessInfo), ProcessInfoFields);


//
//  Implementation of the MemoryRagesCollection class.
//  This object is managing the arbitrary ranges that are being collected
//  to be included in the crashdump at various phases.
//  There is a strict requirement of the crashdump to never include overlapped
//  descriptors for the memory ranges. but practically, memory collected
//  from various areas may in fact partially or totally overlap
//  After the collection is done, CompactItems method takes care of
//  sanitazing and coalescing overlapped ranges
//

static int ItemCompare(const void * e1, const void * e2)
{
    UINT64 *ptr1 = (UINT64 *) e1;
    UINT64 *ptr2 = (UINT64 *) e2;

    if (ptr1[0] < ptr2[0]) {
        return -1;
    } else if (ptr1[0] == ptr2[0]) {
        return 0;
    }

    return 1;
}

void MemoryRagesCollection::AddRange(UINT64 startRVA, UINT64 rangeSize)
{
    if (startRVA > MEMORY_PAGE_SIZE * 16) {

        //  ExtVerb("Adding range %p %p ->", startRVA, rangeSize);

        UINT64 endRVA = ROUND_UP_TO_POWER2(startRVA + rangeSize, (UINT64)MEMORY_PAGE_SIZE);
        startRVA = ROUND_DOWN_TO_POWER2(startRVA, (UINT64)MEMORY_PAGE_SIZE);
        rangeSize = endRVA - startRVA;

        if ((PreviousAddress == startRVA) && (PreviousSize == rangeSize)) {

            // ExtVerb(" %p %p (skipped)\n", startRVA, rangeSize);

            return;
        }

        //  ExtVerb(" %p %p\n", startRVA, rangeSize);

        Add(startRVA);
        Add(rangeSize);
        PreviousAddress = startRVA;
        PreviousSize = rangeSize;
    }
}

void MemoryRagesCollection::CompactItems()
{
    //
    //  Sort all ranges by address to make easier searching for overlapped ranges
    //

    qsort(Array, GetRangesCount(), 2*sizeof(UINT64), ItemCompare);

    int lastValidRange = 0;
    UINT64 prevAddr = GetStartAddress(0);
    UINT64 prevSize = GetRangeSize(0);
    UINT64 prevLimit = prevAddr + prevSize;

    for (int i = 1; i < GetRangesCount(); i++) {

        //
        //  Itterate through ranges, and see if the current one
        //  has any non-empty intersection.
        //

        UINT64 addr = GetStartAddress(i);
        UINT64 size = GetRangeSize(i);
        UINT64 limit = addr + size;

        if (addr < (prevAddr + prevSize)) {

            //
            //  There is an overlap. If this range is completly included
            //  clear it completly from the array, otherwise adjust the
            //  previous range to capture this new limit.
            //

            ExtVerb("%p %p %p %p\n", prevAddr, prevLimit, addr, limit);

            if (limit > prevLimit) {

                prevSize += limit - prevLimit;
                Array[lastValidRange * 2 + 1] = prevSize;
                prevLimit = limit;
            }

            //
            //  This range has been already taken care of
            //  we need to exclude from the list
            //

            Array[i * 2] = 0;
            Array[i * 2 + 1] = 0;

            //
            //  Keep track of the discarded ranges to get an accurate value of
            //  the valid entries that will have to be copied
            //

            DiscardedRanges += 1;

        } else {

            //
            //  No overlap here, set the new current range values
            //

            lastValidRange = i;
            prevAddr = addr;
            prevSize = size;
            prevLimit = limit;
        }
    }
}


UINT64 MemoryRagesCollection::GetRVA(UINT64 address)
{
    UINT64 RVA = 0;

    //
    //  This function is getting the coresponding RVA in the crashdump,
    //  from a given address
    //

    for (int i = 0; i < GetRangesCount(); i++) {

        UINT64 addr = GetStartAddress(i);
        UINT64 size = GetRangeSize(i);
        UINT64 limit = addr + size;

        if ((address >= addr) && (address < limit)) {

            //
            //  Found it. return the value, including also the offset inside the
            //  current range
            //

            RVA += address - addr;
            return RVA;
        }

        //
        //  Keep track of the actual RVA as we walk the ranges
        //

        RVA += size;
    }

    return 0;
}


MemoryRagesCollection * MemoryRanges;


void ResetGlobals()
{
    IncludeExecutables = FALSE;
    IncludeRegisterReferences = FALSE;
    FullMemoryDump = FALSE;
}


//
//  Functions to support memory access references to include them in minidump
//  An extension would have to switch to use TraceRead instead of g_ExtData->ReadVirtual
//  if the memory accessed will be required in offline analysis
//

MemoryRagesCollection * TracingStore = NULL;

//
//  Define how much memory around that address needs to be captured to simplify and add more
//  context to dump files
//

#define TRACE_GRANULARITY MEMORY_PAGE_SIZE

HRESULT TraceRead(UINT64 address, void * buffer, ULONG size)
{
    if (TracingStore != NULL) {

        if (address > TRACE_GRANULARITY) {
            TracingStore->AddRange(address - TRACE_GRANULARITY, size + 2*TRACE_GRANULARITY);
        }
    }

    return g_ExtData->ReadVirtual(address, buffer, size, NULL);
}

HRESULT TraceReadPointer(int count, UINT64 address, PULONG64 buffer)
{
    if (TracingStore != NULL) {

        if (address > TRACE_GRANULARITY) {
            TracingStore->AddRange(address - TRACE_GRANULARITY, 2*TRACE_GRANULARITY);
        }
    }

    return g_ExtData->ReadPointersVirtual(count, address, buffer);
}


//
//  Support functions to build the module list part of the crashdump
//  W/o a proper list of modules loaded, the crashdumps will be useless since no debug
//  information can be loaded, nor any extension can work
//

WCHAR ImageNameBuffer[MEMORY_PAGE_SIZE];
PVOID CrtName;
UINT NameSizes[1024];

MINIDUMP_MODULE_LIST * ReadModuleInformation()
{
    HRESULT status;

    //
    //  Reset the name buffer cursor
    //

    CrtName = (PVOID)ImageNameBuffer;

    ULONG pointerSize = (g_ExtControl->IsPointer64Bit() == S_OK) ? 8 : 4;
    ULONG64 address = 0;
    ULONG64 procs = 0;
    ULONG type = 0;
    ULONG subtype = 0;
    ULONG64 module = 0;
    MINIDUMP_MODULE_LIST * moduleList = NULL;
    //
    //  Although Singularity does not maintain a list with the module loaded in the system
    //  this can be accessible via process enumeration, each process having
    //  a pointer to the image, as well as the image file name. It is also
    //  critical to have the actual base address of the image properly set
    //

    EXT_CHECK(g_ExtSymbols->GetOffsetByName(kernel_processTable, &address));
    EXT_CHECK(g_ExtSymbols->GetOffsetTypeId(address, &type, &module));
    EXT_CHECK(g_ExtData->ReadPointersVirtual(1, address, &procs));
    ExtVerb("processTable: %p\n", procs);

    CHAR name[512];

    EXT_CHECK(g_ExtSymbols->GetTypeName(module, type, name, arrayof(name), NULL));
    ExtVerb("  processTable type: %s\n", name);

    ULONG lengthOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "overall_length", &lengthOffset));

    ULONG valuesOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "values", &valuesOffset));

    //
    //  Read the size of the table and prepare for enumeration of the entries
    //

    ULONG length = 0;
    ULONG processCount = 0;

    if (procs != 0) {

        EXT_CHECK(TraceRead(procs + lengthOffset, &length, sizeof(length)));
        ExtVerb("processTable: %p [maximum %d entries]\n", procs, length);


        for (ULONG id = 0; id < length; id++) {
            ULONG64 process = 0;

            EXT_CHECK(g_ExtData->ReadPointersVirtual(1, procs + valuesOffset + id * pointerSize, &process));

            if (process != 0) {

                //
                //  Select only the valid entries in enumeration
                //

                processCount += 1;
            }
        }
    }

    //  The number of modules in the least can be at most the number of processes we enumerated. In fact
    //  the number is smaller since idle, kernel don't have a coresponding file. We do reserve
    //  a special slot for the kernel image in (processCount + 1), not relying that we'll always have something
    //  in the table would represent that one

    moduleList = (MINIDUMP_MODULE_LIST *)malloc(sizeof(MINIDUMP_MODULE_LIST)
        + (processCount + 1) * sizeof(MINIDUMP_MODULE));

    if (moduleList == NULL) goto Exit;

    moduleList->NumberOfModules = 0;

    if (moduleList == NULL)
        return NULL;
    //
    // Write first the kernel module. We fetch this from the static field of the PEImage
    //

    MINIDUMP_MODULE * moduleInfo = &moduleList->Modules[moduleList->NumberOfModules];

    RtlZeroMemory(moduleInfo, sizeof(*moduleInfo));

    UINT64 kernelImageAddress;
    EXT_CHECK(g_ExtSymbols->GetOffsetByName(kernel_PEImage_kernel, &kernelImageAddress));
    EXT_CHECK(g_ExtData->ReadPointersVirtual(1, kernelImageAddress, &kernelImageAddress));

    ExtVerb("KernelImage %p\n", kernelImageAddress);

    //
    //  Fill in now all fields from the structure
    //

    PEImage imageInfo;
    PEImageStruct.Read(kernelImageAddress, &imageInfo);

    ExtVerb("KernelImage info %p %p %p %p\n",
            imageInfo.VirtualAddress,
            imageInfo.loadedSize,
            imageInfo.checkSum,
            imageInfo.timeDateStamp);

    moduleInfo->BaseOfImage = imageInfo.VirtualAddress;
    moduleInfo->SizeOfImage = (ULONG32)imageInfo.loadedSize;
    moduleInfo->CheckSum = (ULONG32)imageInfo.checkSum;
    moduleInfo->TimeDateStamp = (ULONG32)imageInfo.timeDateStamp;
    moduleInfo->ModuleNameRva = (ULONG32)((UINT64)CrtName - (UINT64)ImageNameBuffer);

    //
    //  We know at this point the image base and size, we can include in the dump
    //  if the appropriate option has been specified. Otherwise we just include the
    //  first page so that the debugger can check the header information such as timestamp
    //  when debugged offline
    //

    MemoryRanges->AddRange(moduleInfo->BaseOfImage, IncludeExecutables ? moduleInfo->SizeOfImage : MEMORY_PAGE_SIZE);

    //
    //  Prepare now to save the kernel name to the crashdump. We have prepared
    //  a buffer holding all names, where we copy the strings to and set RVA references
    //

    UINT32 * Size = (UINT32 *)CrtName;
    CrtName = (PVOID)(Size + 1);

    //
    // For the kernel we just have a hardcoded name
    //

    wcscpy((WCHAR*)CrtName, L"kernel");

    *Size = (UINT32)wcslen((WCHAR*)CrtName) * sizeof(WCHAR);
    NameSizes[0] = sizeof(*Size) + (*Size) * sizeof(WCHAR);

    //
    //  Move the cursor to the next empty position
    //  TODO: test for buffer limits
    //

    CrtName = (PVOID)((WCHAR*)CrtName + *Size);

    moduleList->NumberOfModules += 1;

    //
    //  Enumerate now the processes and fetch for each process the module information
    //

    for (ULONG id = 0; id < length; id++) {
        ULONG64 process = 0;

        EXT_CHECK(g_ExtData->ReadPointersVirtual(1, procs + valuesOffset + id * pointerSize, &process));
        if (process != 0) {

            ProcessInfo pInfo;

            //
            //  Retrieve the process data, in order to get to the image information
            //

            ProcessInfoStruct.Read(process, &pInfo);
            ExtVerb("Process %p %p\n", process, pInfo.image);
            processCount += 1;

            if (pInfo.image != NULL) {

                MINIDUMP_MODULE * moduleInfo = &moduleList->Modules[moduleList->NumberOfModules];

                RtlZeroMemory(moduleInfo, sizeof(*moduleInfo));

                PEImage imageInfo;
                PEImageStruct.Read(pInfo.image, &imageInfo);

                ExtVerb("KernelImage info %p %p %p %p\n",
                        imageInfo.VirtualAddress,
                        imageInfo.loadedSize,
                        imageInfo.checkSum,
                        imageInfo.timeDateStamp);

                moduleInfo->BaseOfImage = imageInfo.VirtualAddress;
                moduleInfo->SizeOfImage = (ULONG32)imageInfo.loadedSize;
                moduleInfo->CheckSum = (ULONG32)imageInfo.checkSum;
                moduleInfo->TimeDateStamp = (ULONG32)imageInfo.timeDateStamp;
                moduleInfo->ModuleNameRva = 0;

                //
                //  Same as for the kernel, we can save the entire image in dump, or just
                //  the first page
                //

                MemoryRanges->AddRange(moduleInfo->BaseOfImage, IncludeExecutables ? moduleInfo->SizeOfImage : MEMORY_PAGE_SIZE);

                //
                //  Deal now with the image name. We have to read the string
                //  from the imagename field of the process informatio
                //

                UINT32 * Size = (UINT32 *)CrtName;
                CrtName = (PVOID)(Size + 1);

                String str;
                EXT_CHECK(StringStruct.Read(pInfo.imageName, &str));
                EXT_CHECK(g_ExtData->ReadVirtual(pInfo.imageName + StringFields[0].offset,
                                                 CrtName,
                                                 (ULONG)str.m_stringLength * sizeof(WCHAR),
                                                 NULL));

                *Size = (UINT32)str.m_stringLength * sizeof(WCHAR);
                NameSizes[moduleList->NumberOfModules] = sizeof(*Size) + (*Size) * sizeof(WCHAR);

                //
                // We are done with this module. Move the cursors for the next available slots
                //

                CrtName = (PVOID)((WCHAR*)CrtName + *Size);
                moduleList->NumberOfModules += 1;
            }
        }
    }

    return moduleList;

Exit:
    //  Error path
    if (moduleList) free (moduleList);

    ERRORBREAK("Invalid symbols information\n");
    return NULL;
}


//
//  Functions dealing with capturing the thread contexts
//

VOID * ThreadContexts = NULL;

RVA LocalOffset = 0;
ULONG64 excptThread = 0;

void AddMemoryReference(UINT64 address)
{
    if (address > TRACE_GRANULARITY) {
        MemoryRanges->AddRange(address - TRACE_GRANULARITY, 2*TRACE_GRANULARITY);
    }
}

BOOL IsCurrentStackRange(UINT64 stackReference, UINT64 stackValue)
{
    //  This is some hack to recognize from the threads list
    //  the one that is matching the current exception context

    return (stackValue > TRACE_GRANULARITY) &&
           (stackReference > TRACE_GRANULARITY) &&
           (stackValue > (stackReference - TRACE_GRANULARITY)) &&
           (stackValue < (stackReference + TRACE_GRANULARITY));
}

MINIDUMP_THREAD_LIST * ReadThreadInformation()
{
    HRESULT status;
    MINIDUMP_THREAD_LIST * threadList = NULL;
    ULONG pointerSize = (g_ExtControl->IsPointer64Bit() == S_OK) ? 8 : 4;
    ULONG64 address = 0;
    ULONG64 threads = 0;
    ULONG type = 0;
    ULONG subtype = 0;
    ULONG64 module = 0;
    excptThread = 0;

    //
    //  Fetch the thread table from the kernel
    //

    EXT_CHECK(g_ExtSymbols->GetOffsetByName(kernel_threadTable, &address));
    EXT_CHECK(g_ExtSymbols->GetOffsetTypeId(address, &type, &module));
    EXT_CHECK(g_ExtData->ReadPointersVirtual(1, address, &threads));
    ExtVerb("threadTable: %p\n", threads);

    //
    //  Prepare to enumerate the entries inside the thread table
    //

    ULONG lengthOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "overall_length", &lengthOffset));

    ULONG valuesOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "values", &valuesOffset));

    ULONG length = 0;
    EXT_CHECK(TraceRead(threads + lengthOffset, &length, sizeof(length)));
    ExtVerb("threadTable: %p [maximum %d entries]\n", threads, length);

    //
    //  Reserve one slot more to save the current debugger context, which may not match
    //  on win32 any of the threads that get enumerated. For consistency
    //  accross all platforms simulate a thread, and place it at the first index in the list
    //  ~0s will allow switching directly to it
    //

    length += 1;

    threadList = (MINIDUMP_THREAD_LIST *)malloc(sizeof(MINIDUMP_THREAD_LIST) + length * sizeof(MINIDUMP_THREAD));

    if (threadList == NULL) {
        goto Exit;
    }

    threadList->NumberOfThreads = 0;
    ThreadContexts = NULL;

    if (GetTargetContextSize() > 0) {

        ThreadContexts = malloc(length * GetTargetContextSize());
    }

    if (ThreadContexts == NULL) {
        goto Exit;
    }

    //
    //  Capture the current debugger context
    //


    MINIDUMP_THREAD * threadInfo = &threadList->Threads[threadList->NumberOfThreads];

    EXT_CHECK(g_ExtSymbols->GetScope(NULL, NULL, ThreadContexts, GetTargetContextSize()));
    UINT64 CurrentESPContext = GetStackPointer(ThreadContexts);

    threadInfo->ThreadId = 0xFFFF;

    threadInfo->SuspendCount = 0;
    threadInfo->PriorityClass = 0;
    threadInfo->Priority = 0;
    threadInfo->Teb = 0;
    threadInfo->ThreadContext.DataSize = GetTargetContextSize();

    threadInfo->Stack.StartOfMemoryRange = CurrentESPContext;
    threadInfo->Stack.Memory.DataSize = (ULONG32)4096;

    MemoryRanges->AddRange(threadInfo->Stack.StartOfMemoryRange, threadInfo->Stack.Memory.DataSize);
    FetchRegisterReferences(ThreadContexts);

    threadList->NumberOfThreads += 1;

    MINIDUMP_THREAD * dbgContextThreadInfo = threadInfo;

    //
    //  Walk now the rest of the rest of the threads
    //

    for (ULONG id = 0; id < length - 1; id++) {

        ULONG64 threadAddress = 0;

        //
        //  Fetch the pointer address from the table at the current index
        //

        threadInfo = &threadList->Threads[threadList->NumberOfThreads];

        EXT_CHECK(g_ExtData->ReadPointersVirtual(1, threads + valuesOffset + id * pointerSize, &threadAddress));

        if (threadAddress != 0) {

            //
            //  We have a valid entry. Continue to capture the thread context
            //

            Thread thread;
            ThreadEntry entry;

            EXT_CHECK(ThreadStruct->Read(threadAddress, &thread));
            EXT_CHECK(ThreadEntryStruct.Read(thread.schedulerEntry, &entry));

            threadInfo->ThreadId = (ULONG32)thread.context.threadIndex;

            if (threadInfo->ThreadId == 0) {

                //  The debugger does not accept threads IDs of 0
                // so we cannot preserve the exact translation.
                // Find a slot for the new thread that is not used by Singulrity

                threadInfo->ThreadId += 1024;
            }
            threadInfo->SuspendCount = 0;
            threadInfo->PriorityClass = 0;
            threadInfo->Priority = 0;
            threadInfo->Teb = threadAddress;

            VOID * ctx = (void *)((ULONG64)ThreadContexts +
                GetTargetContextSize() * threadList->NumberOfThreads);

            RtlZeroMemory(ctx, GetTargetContextSize());
            threadInfo->ThreadContext.DataSize = GetTargetContextSize();

            //
            //  This appears to point to a valid thread context. Fetch one page of stack memory from
            //  the current pointer, and load the context registers
            //

            threadInfo->Stack.Memory.DataSize = (ULONG32)4096;
            threadInfo->Stack.StartOfMemoryRange = thread.context.threadRecord.spill.sp;

            MemoryRanges->AddRange(threadInfo->Stack.StartOfMemoryRange, threadInfo->Stack.Memory.DataSize);
            threadInfo->ThreadContext.DataSize = GetTargetContextSize();

            LoadThreadContext(ctx, &thread.context.threadRecord.spill);

            if (IsCurrentStackRange(CurrentESPContext, thread.context.threadRecord.spill.sp)) {

                excptThread = threadInfo->ThreadId;
                dbgContextThreadInfo->Teb = excptThread;
            }

            FetchRegisterReferences(ctx);

            threadList->NumberOfThreads += 1;
        }
    }

    return threadList;

Exit:
    //  Error path
    if (threadList) free (threadList);
    ERRORBREAK("Invalid symbols information\n");
    return NULL;
}

void IncludeUsedMemory()
{
    HRESULT status;

    ULONG64 pageTable;
    ULONG64 pageCount;

    ExtVerb("Scanning flat pages for in-use memory");
    EXT_CHECK(FindBound("Microsoft_Singularity_Memory_FlatPages::pageTable", &pageTable));
    EXT_CHECK(FindBound("Microsoft_Singularity_Memory_FlatPages::pageCount", &pageCount));

    ExtOut("%p %p\n", pageTable, pageCount);
    ULONG * pageTableCopy = (ULONG *)malloc((SIZE_T)pageCount * sizeof(ULONG));

    if(pageTableCopy == NULL) {

        ExtOut("Not enough memory to cache the page table");
        return;
    }

    if (g_ExtData->ReadVirtual(pageTable, pageTableCopy, (ULONG)pageCount * sizeof(ULONG), NULL) != S_OK) {

       ExtOut("Error reading the page table");
       free(pageTableCopy);
       return;
    }

    for (ULONG64 i = 1; i < pageCount; i++) {

        if ((USHORT)(pageTableCopy[i]) != 0) {

            ExtVerb("Adding pages %p %lx\n", i * MEMORY_PAGE_SIZE, MEMORY_PAGE_SIZE);
            MemoryRanges->AddRange(i * MEMORY_PAGE_SIZE, MEMORY_PAGE_SIZE);
        }
    }

    free(pageTableCopy);
    return;

Exit:
    //  Error path

    ExtOut("Invalid symbols information\n");
    return;
}



void CrashDump(PCSTR fname)
{
    MINIDUMP_MODULE_LIST * moduleList = NULL;
    MINIDUMP_THREAD_LIST * threadList = NULL;

    if (MemoryRanges == NULL) {

        MemoryRanges = new MemoryRagesCollection();
    }

    FILE * file = fopen(fname, "wb");

    if (file == NULL) {
        ExtOut("Cannot open file");
        return;
    }

    int dumpsize =  sizeof(CRASH_DUMP_HEADER);

    void *buffer = malloc(dumpsize);
    CRASH_DUMP_HEADER *dump =  (CRASH_DUMP_HEADER *) buffer;

    dump->Header.Signature = MINIDUMP_SIGNATURE;
    dump->Header.Version = MINIDUMP_VERSION;
    dump->Header.NumberOfStreams = 4;
    dump->Header.StreamDirectoryRva = offsetof(CRASH_DUMP_HEADER, Directories);

    // Directory list - We use 4 directories currently:
    // SystemInfo
    // ThreadList
    // ModuleList
    // MemoryList

    dump->Directories[0].StreamType = SystemInfoStream;
    dump->Directories[0].Location.DataSize = sizeof(dump->SystemInfo);
    dump->Directories[0].Location.Rva = offsetof(CRASH_DUMP_HEADER, SystemInfo);

    //
    //  Fill in the system information part
    //

    switch (TargetMachine) {

        case IMAGE_FILE_MACHINE_AMD64:
            dump->SystemInfo.ProcessorArchitecture = PROCESSOR_ARCHITECTURE_AMD64;
            break;

        case IMAGE_FILE_MACHINE_I386:
            dump->SystemInfo.ProcessorArchitecture = PROCESSOR_ARCHITECTURE_INTEL;
            break;

        case IMAGE_FILE_MACHINE_ARM:
            dump->SystemInfo.ProcessorArchitecture = PROCESSOR_ARCHITECTURE_ARM;
            break;

        default:
            dump->SystemInfo.ProcessorArchitecture = PROCESSOR_ARCHITECTURE_UNKNOWN;
            break;
    }


    //
    //  TODO: the following fields need to be updated properly by querying the
    //  system
    //

    dump->SystemInfo.ProcessorLevel = 6;
    dump->SystemInfo.ProcessorRevision = 0;

    // FIXME from the target. It is not really relevant here since the minidump
    // is treated as a usermode process dump

    dump->SystemInfo.NumberOfProcessors = 1;

    dump->SystemInfo.ProductType = VER_NT_WORKSTATION;

    dump->SystemInfo.MajorVersion = 5; // WinXP
    dump->SystemInfo.MinorVersion = 1;
    dump->SystemInfo.BuildNumber = 0;
    dump->SystemInfo.PlatformId = VER_PLATFORM_WIN32_NT;

    dump->SystemInfo.CSDVersionRva = 0; // hopefully this is OK

    dump->SystemInfo.Cpu.X86CpuInfo.VendorId[0] = 'Genu';
    dump->SystemInfo.Cpu.X86CpuInfo.VendorId[1] = 'ineI';
    dump->SystemInfo.Cpu.X86CpuInfo.VendorId[2] = 'ntel';
    dump->SystemInfo.Cpu.X86CpuInfo.VersionInformation = 0; // get these right later as needed
    dump->SystemInfo.Cpu.X86CpuInfo.FeatureInformation = 0;
    dump->SystemInfo.Cpu.X86CpuInfo.AMDExtendedCpuFeatures = 0;

    LocalOffset = sizeof(CRASH_DUMP_HEADER);

    // Build the module information part of the crashdump

    moduleList = ReadModuleInformation();
    if (moduleList == NULL) goto Exit;

    dump->Directories[3].StreamType = ModuleListStream;
    dump->Directories[3].Location.DataSize = sizeof(MINIDUMP_MODULE_LIST) + (sizeof(MINIDUMP_MODULE)*moduleList->NumberOfModules);
    dump->Directories[3].Location.Rva = LocalOffset;

    LocalOffset += dump->Directories[3].Location.DataSize;

    int namebufferLength = 0;

    for (ULONG32 i = 0; i < moduleList->NumberOfModules; i++) {

        moduleList->Modules[i].ModuleNameRva += LocalOffset;
        LocalOffset += NameSizes[i];
        namebufferLength += NameSizes[i];
    }

    //
    //  Build the thread information part of the crashdump
    //

    threadList = ReadThreadInformation();
    if (threadList == NULL) goto Exit;

    dump->Directories[1].StreamType = ThreadListStream;
    dump->Directories[1].Location.DataSize = sizeof(MINIDUMP_THREAD_LIST) + (sizeof(MINIDUMP_THREAD)*threadList->NumberOfThreads );
    dump->Directories[1].Location.Rva = LocalOffset;

    LocalOffset += dump->Directories[1].Location.DataSize;

    //
    //  If we collected the current context, setup also an exception directory
    //  and make that active con text when the crashdump is opened in debugger
    //

    if (excptThread != 0) {

        dump->Header.NumberOfStreams = 5;
        dump->Directories[4].StreamType = ExceptionStream;
        dump->Directories[4].Location.DataSize = sizeof(MINIDUMP_EXCEPTION_STREAM);
        dump->Directories[4].Location.Rva = offsetof(CRASH_DUMP_HEADER, ExceptionInfo);
    }

    for (ULONG32 i = 0; i < threadList->NumberOfThreads ; i++) {

        threadList->Threads[i].ThreadContext.Rva = LocalOffset;

        if (threadList->Threads[i].ThreadId == excptThread) {

            //
            //  Update the exception information to the current thread
            //

            dump->ExceptionInfo.ThreadId = (ULONG32)excptThread;
            dump->ExceptionInfo.ThreadContext.DataSize = threadList->Threads[i].ThreadContext.DataSize;
            dump->ExceptionInfo.ThreadContext.Rva = threadList->Threads[i].ThreadContext.Rva;
        }

        LocalOffset += threadList->Threads[i].ThreadContext.DataSize;
    }

    if (FullMemoryDump) {

        IncludeUsedMemory();
    }

    //
    //  The memory ranges might be overlapped. This is not allowed in a crashdump
    //  we need to compact and coalesce the adjacent ranges to provide a full list
    //  of memory ranges that will be included in the dump
    //

    MemoryRanges->CompactItems();

    int numMemoryRanges = MemoryRanges->GetEffectiveRanges();
    ULONG32 memoryStreamLength = sizeof(_MEMORY_STREAM ) + sizeof(MINIDUMP_MEMORY_DESCRIPTOR)*(numMemoryRanges - 1);
    _MEMORY_STREAM * memoryStream = (_MEMORY_STREAM * )malloc(memoryStreamLength);

    memoryStream->MemoryCount = numMemoryRanges;
    dump->Directories[2].StreamType = MemoryListStream;
    dump->Directories[2].Location.DataSize = memoryStreamLength;
    dump->Directories[2].Location.Rva = LocalOffset;
    LocalOffset += memoryStreamLength;

    //
    //  Fixup the RVA memory references to the regions
    //

    int crtIndex = 0;
    for (int i = 0; i < MemoryRanges->GetRangesCount(); i++) {

        if (MemoryRanges->GetStartAddress(i)) {

            memoryStream->Memory[crtIndex].StartOfMemoryRange = MemoryRanges->GetStartAddress(i);
            memoryStream->Memory[crtIndex].Memory.DataSize = (ULONG32)MemoryRanges->GetRangeSize(i);
            memoryStream->Memory[crtIndex].Memory.Rva = LocalOffset  + (RVA)MemoryRanges->GetRVA(memoryStream->Memory[crtIndex].StartOfMemoryRange);
            crtIndex += 1;
            if (crtIndex >= numMemoryRanges) {
                break;
            }
        }
    }

    //
    //  Update the RVA references for objects that might have change after the
    //  memory ranges coalescing.
    //

    for (ULONG32 i = 0; i < threadList->NumberOfThreads ; i++) {

        threadList->Threads[i].Stack.Memory.Rva = LocalOffset +
            (RVA)MemoryRanges->GetRVA(threadList->Threads[i].Stack.StartOfMemoryRange);
        ExtVerb("Thread RVA %p\n",(UINT64)threadList->Threads[i].Stack.Memory.Rva);
    }

    //  All directories entries for streams must be setup at this point

    ExtOut("Writing crashdump ...");

    fwrite(buffer, dumpsize, 1, file);
    fwrite(moduleList, dump->Directories[3].Location.DataSize, 1, file);
    fwrite(ImageNameBuffer, namebufferLength, 1, file);
    fwrite(threadList, dump->Directories[1].Location.DataSize, 1, file);
    fwrite(ThreadContexts, threadList->NumberOfThreads * GetTargetContextSize(), 1, file);
    fwrite(memoryStream, dump->Directories[2].Location.DataSize, 1, file);

    void * tmpBuffer = malloc (MEMORY_PAGE_SIZE);
    if (tmpBuffer == NULL) goto Exit;

    for (ULONG32 i = 0; i < memoryStream->MemoryCount; i++) {

        ExtVerb("%p %p %p %p\n",(UINT64)memoryStream->Memory[i].StartOfMemoryRange, (UINT64)memoryStream->Memory[i].Memory.DataSize,
            (UINT64)(memoryStream->Memory[i].StartOfMemoryRange + memoryStream->Memory[i].Memory.DataSize),
            (UINT64)memoryStream->Memory[i].Memory.Rva );

        UINT64 RemainingSize = memoryStream->Memory[i].Memory.DataSize;
        UINT64 currentAddress = memoryStream->Memory[i].StartOfMemoryRange;

        while (RemainingSize > 0) {

            ULONG32 readSize = MEMORY_PAGE_SIZE;

            if (RemainingSize < readSize) {

                readSize = (ULONG32)RemainingSize;
            }

            g_ExtData->ReadVirtual(currentAddress, tmpBuffer, readSize, NULL);
            fwrite(tmpBuffer, readSize, 1, file);
            RemainingSize -= readSize;
            currentAddress += readSize;
        }
    }

    free(tmpBuffer);
    ExtOut("done\n");

    fclose(file);

Exit:
    if (moduleList) free(moduleList);
    if (threadList) free(threadList);

    //
    //  Cleanup the global states
    //

    if (ThreadContexts != NULL) free(ThreadContexts);
    ThreadContexts = NULL;

    free(buffer);

    delete MemoryRanges;
    MemoryRanges = NULL;

    //
    //  Reset the tracing store buffer
    //

    TracingStore = NULL;
}


EXT_DECL(crashdump) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    ResetGlobals();

    pointerSize = (g_ExtControl->IsPointer64Bit() == S_OK) ? 8 : 4;

    SKIP_WHITESPACES(args);

    if (*args == '\0')
    {
        Usage();
        goto Exit;
    }

    while (*args != '\0') {

        SKIP_WHITESPACES(args);

        // process argument
        if (*args == '-' || *args == '/') {
            args++;
            switch (*args++) {
              case 'x':
              case 'X': {

                IncludeExecutables = TRUE;
              }
                break;

              case 'f':
              case 'F': {

                FullMemoryDump = TRUE;
              }
                break;

              case 'r':
              case 'R': {

                IncludeRegisterReferences = TRUE;
              }
                break;

              case 's':
              case 'S': {

                SKIP_WHITESPACES(args);

                CrashDump(args);
                goto Exit;
              }
                break;
              case 't':
              case 'T': {

                SKIP_WHITESPACES(args);

                if (MemoryRanges != NULL) {
                    delete MemoryRanges;
                    MemoryRanges = NULL;
                    TracingStore = NULL;
                }
                MemoryRanges = new MemoryRagesCollection();
                TracingStore = MemoryRanges;
                goto Exit;
              }
                break;
              SKIP_WHITESPACES(args);
            }
        }
        else {
            Usage();
            break;
        }
    }

    EXT_LEAVE();    // Macro includes: return status;
}

