//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

// * searching exception table
// * make machine faults raise CIL exceptions
//
// C code should always invoke the filter BartokMachineFaultFilter
// before it attempts to handle any of the machine faults handled
// below.   BartokMachineFaultFilter causes an appropriate exception
// to be thrown if a machine fault occurred in CIL code.

# include "hal.h"

extern BOOL KdDebuggerNotPresent;
#ifndef NOEVENTING
#include "eventing.h"
#endif

// See bartok\tables\ExceptionTable.cs for a description of ExceptionTableEntry

//////////////////////////////////////////////////////////////////////////////
//
struct ExceptionTableEntry {
    uintptr scopeBaseAddr;
    union {
        struct {
            Class_System_Type *exceptionClass; // low bit is zero
            uintptr handlerAddr;
        };
        struct {
            uintptr frameSetupInfo; // low bit is one
            uintptr spillSize;
        };
    };
};

struct TableEntry {
    ExceptionTableEntry * tableBaseAddr;
    ExceptionTableEntry * tableEndAddr;
};

extern TableEntry TableBase[1];
extern TableEntry TableBound[1];

// TODO: BUGBUG_X64:
//   ExceptionTableLookupReturn breaks down with 64-bit pointers.
//   We will need to revisit the code
//   that uses the ExceptionTableLookupReturn result (__throwDispatcher*).

#ifdef ISA_IX64
struct PtrPair {
    uintptr a;
    uintptr b;
};
typedef PtrPair lookupReturnType;
#else
typedef uint64 lookupReturnType;
#endif
union ExceptionTableLookupReturn {
    lookupReturnType etlReturn;
    struct {
        Class_System_Type *exceptionClass;
        uintptr handlerAddr;
    };
    struct {
        uintptr frameSetupInfo;
        uintptr spillSize;
    };
};

static uintptr LookupTable(uintptr throwAddr,
                           ExceptionTableEntry **tableBaseEntry,
                           ExceptionTableEntry **tableEndEntry) {
#if 0
    printf("LookupTable(throwAddr=%p, tableBase=%p, tableEnd=%p)\n",
           throwAddr, tableBaseEntry, tableEndEntry);
    printf("  TableBase=%p, TableBound=%p, maxIndex = %d\n",
           TableBase, TableBound, TableBound - TableBase);
    printf("  callSiteTableCount=%d\n",
           Class_System_GCs_CallStack::c_callSiteTableCount);
    printf("  codeBaseStartTable=%p\n",
           Class_System_GCs_CallStack::c_codeBaseStartTable);
    printf("  returnAddressToCallSiteSetNumbers=%p\n",
           Class_System_GCs_CallStack::c_returnAddressToCallSiteSetNumbers);
    printf("  callSiteSetCount=%p\n",
           Class_System_GCs_CallStack::c_callSiteSetCount);
#endif

    //  search to find which table to use
    int maxIndex = (int) (TableBound - TableBase);
    uintptr codeBase = (uintptr) -1;
    uintptr relCodeAddr = 0;
    for (int i = 0; i < maxIndex; i++) {
        TableEntry *entry = &TableBase[i];
#if 0
        printf("   TableBase[%d]  base=%p end=%p  codeBaseStartTable[]=%p\n",
               i, entry->tableBaseAddr, entry->tableEndAddr,
               Class_System_GCs_CallStack::c_codeBaseStartTable[i]);
#endif
        codeBase =
            ((uintptr*)Class_System_GCs_CallStack::c_codeBaseStartTable)[i];

        if (throwAddr < codeBase) {
            continue;
        }
        relCodeAddr = throwAddr - codeBase;
        *tableBaseEntry = entry->tableBaseAddr;
        *tableEndEntry = entry->tableEndAddr;

#if 0
        printf("   relCodeAddr = %p\n", relCodeAddr);
        printf("    tableBase scopeBaseAddr=%p class=%p handler=%p\n",
               (*tableBaseEntry)->scopeBaseAddr,
               (*tableBaseEntry)->exceptionClass,
               (*tableBaseEntry)->handlerAddr);
        printf("    tableEnd  scopeBaseAddr=%p class=%p handler=%p\n",
               (*tableEndEntry)->scopeBaseAddr,
               (*tableEndEntry)->exceptionClass,
               (*tableEndEntry)->handlerAddr);
#endif

        if ((relCodeAddr >= (*tableBaseEntry)->scopeBaseAddr)
            && (relCodeAddr <= (*tableEndEntry)->scopeBaseAddr)) {
            return codeBase;
        }
    }

    return (uintptr) -1;
    //exit(-2);
    //__asm int 3;
}

Class_System_VTable * getRealVTable(Class_System_VTable * vt)
{
    return (Class_System_VTable *)((uintptr)vt & (~((uintptr)3)));
}

//////////////////////////////////////////////////////////////////////////////

// ExceptionAssert is called when an unexpected condition happens during
// exception processing

void ExceptionAssert()
{
#if SPIN
    // Useful for native cases when no debugger is avaiable
    while (1)
        ;
#endif

    __debugbreak();
}

// search an exception table

//////////////////////////////////////////////////////////////////////////////

// search an exception table
// - Returns the exception in eax.
// - Returns the handler address in edx.
// OR if the shared unwind handler should be used
// - Returns the frameSetupInfo in eax.
// - Returns the spill area size in edx.

lookupReturnType __fastcall ExceptionTableLookup(Class_System_Exception *exception,
                                                 uintptr throwAddr) {

#if 0
    printf("\n");
    printf("ExceptionTableLookup(exception=%p, vtable=%p, throwAddr=%p)\n",
           exception, ((uintptr *)exception)[0], throwAddr);
#endif

    if (exception->_throwAddress == NULL) {
        exception->_throwAddress = throwAddr;
    }

    //  search for table using throwAddr
    ExceptionTableEntry *baseEntry = NULL;
    ExceptionTableEntry *endEntry = NULL;
    uintptr codeBase = LookupTable(throwAddr, &baseEntry, &endEntry);

#if SINGULARITY_KERNEL
#if 0
    printf("  codeBase=%p baseEntry=%p endEntry=%p\n",
           codeBase, baseEntry, endEntry);
#endif
#endif

    if (codeBase == (uintptr) -1) {
#if SINGULARITY_KERNEL
#if 0
        printf("Exception outside of any known code regions!\n");
#endif
        if (!KdDebuggerNotPresent) {
            ExceptionAssert();
        }
#if 0
        printf("Terminating by exception!\n");
#endif
        Class_System_VTable::g_TerminateByException(exception);
        ExceptionAssert();
#elif SINGULARITY_PROCESS
        Assert("Exception outside of any known code regions!\n");
        Class_System_VTable::g_TerminateByException(exception);
#endif
    }

    // bsearch for throwAddr
    int minIndex = 0;
    int maxIndex = (int) (endEntry-baseEntry);
    throwAddr -= codeBase;

    if (throwAddr < baseEntry[minIndex].scopeBaseAddr ||
        throwAddr > baseEntry[maxIndex].scopeBaseAddr) {
        // BUGBUG: callback to C# code that may trigger GC
#if SINGULARITY_KERNEL
#if 0
        printf("Exception outside of known code region for %p\n", codeBase);
#endif
        if (!KdDebuggerNotPresent) {
            __debugbreak();
        }
        Class_System_VTable::g_TerminateByException(exception);
#if 0
        printf("top-level exception handling code failed\n");
#endif
        __debugbreak();
#elif SINGULARITY_PROCESS
        Assert("Exception outside of known code region for.\n");
        Class_System_VTable::g_TerminateByException(exception);
        Assert("top-level exception handling code failed\n");
#endif
    }
    while (minIndex+1 < maxIndex) {
        int midIndex = (minIndex+maxIndex)/2;
        uintptr midAddr = baseEntry[midIndex].scopeBaseAddr;
        if (throwAddr < midAddr) {
            maxIndex = midIndex;
        } else {
            minIndex = midIndex;
        }
    }
    ExceptionTableEntry *entry = &baseEntry[minIndex];

    //  back up to first entry containing throwAddr (there may be several)

    uintptr baseAddr;
    for (baseAddr = entry->scopeBaseAddr;
         entry->scopeBaseAddr == baseAddr && entry >= baseEntry;
         entry--) {
        continue;
    }

    //  check each of the handlers in turn

    for (entry++; entry->scopeBaseAddr <= throwAddr; entry++) {
#if 0
        printf("    entry=%p[%d]  "
               "scopeBaseAddr=%p exceptionClass=%p handler=%p\n",
               entry, entry - baseEntry,
               entry->scopeBaseAddr, entry->exceptionClass, entry->handlerAddr);
#endif

        // 0 now means "no frame pointer omission and no callee save registers
        // have been saved to the stack":
        // Assert(entry->exceptionClass);

        Assert(((entry->frameSetupInfo & 0x1) != 0)
               || (entry->handlerAddr != NULL));
        if (((entry->frameSetupInfo & 0x1) != 0)
            || Class_System_VTable::g_IsExceptionHandler(entry->exceptionClass,
                                                         exception)) {
#if 0
            printf("Found matching exception entry: %p\n", entry);
#endif
            break;
        }
    }
    Assert(entry->scopeBaseAddr == baseAddr);

    ExceptionTableLookupReturn retval;

    if((entry->frameSetupInfo & 0x1) != 0) {
        retval.frameSetupInfo = entry->frameSetupInfo;
        retval.spillSize = entry->spillSize;
#ifndef NOEVENTING
        LogExceptionInfo((UIntPtr)(codeBase + throwAddr),
                         0,
                         getRealVTable(exception->postHeader.vtableObject)->vtableType->name);
#endif
    } else {
        retval.exceptionClass = entry->exceptionClass;
        retval.handlerAddr = entry->handlerAddr + codeBase;
#ifndef NOEVENTING
        LogExceptionInfo((UIntPtr)(codeBase + throwAddr),
                         (UIntPtr)(retval.handlerAddr),
                         getRealVTable(exception->postHeader.vtableObject)->vtableType->name);
#endif
    }

#if SINGULARITY_KERNEL
    if (!exception->_notifiedDebugger && !KdDebuggerNotPresent) {
        exception->_notifiedDebugger = true;

        bool iflag =
            Class_Microsoft_Singularity_Processor::g_DisableInterrupts();
        Class_System_VTable * vtable = getRealVTable(exception->postHeader.vtableObject);
#if 0
        if ((entry->frameSetupInfo & 0x1) != 0) {
            printf("\n---- First chance %ls at %p.  Handler is shared ----\n",
                   &(vtable->vtableType->name->m_firstChar),
                   codeBase + throwAddr);
        }
        else {
            printf("\n---- First chance %ls at %p.  Handler is %p ----\n",
                   &(vtable->vtableType->name->m_firstChar),
                   codeBase + throwAddr,
                   retval.handlerAddr);
        }
        if (exception->_message != NULL) {
            printf("------ Message: %ls\n",
                   &(exception->_message->m_firstChar));
        }
#endif
        KdNotifyException(exception, (uint32) throwAddr);
        Class_Microsoft_Singularity_Processor::g_RestoreInterrupts(iflag);
    }
#endif

    return(retval.etlReturn);
}

