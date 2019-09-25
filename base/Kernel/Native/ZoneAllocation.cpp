////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ZoneAllocation.cpp
//
//  Note:   Non-blocking zone allocation for variable size
//          elements for eventing and tracing infrastructure.
//

#include "hal.h"
#include "eventing.h"

//
//  Utility routines for buffer validation
//

#ifdef BUFFER_VALIDATION

#define BOB_SIGNATURE 0xabababab  // begining of buffer signature
#define EOB_SIGNATURE 0xcdcdcdcd  // end of buffer signature

void SetEndOfBuffer(PMEMORY_ZONE Zone)
{
    uint32 * ptr = (uint32 *)((ULONG_PTR)Zone + Zone->ZoneSize);
    *ptr = EOB_SIGNATURE;

    ptr = (uint32 *)((ULONG_PTR)Zone) - 1;
    *ptr = BOB_SIGNATURE;
}

void CheckEndOfBuffer(PMEMORY_ZONE Zone)
{
    uint32 * ptr = (uint32 *)((ULONG_PTR)Zone + Zone->ZoneSize);
    EV_ASSERT(*ptr == EOB_SIGNATURE);

    ptr = (uint32 *)((ULONG_PTR)Zone) - 1;
    EV_ASSERT(*ptr == BOB_SIGNATURE);
}

#else // !BUFFER_VALIDATION

#define SetEndOfBuffer(x)
#define CheckEndOfBuffer(x)

#endif // BUFFER_VALIDATION


PMEMORY_ZONE
InitializeMemoryZone(void * Buffer, uint16 Size, UIntPtr storageHandle)
{
    PMEMORY_ZONE Zone;

#ifdef BUFFER_VALIDATION

    //  In buffer validation mode, add extra space for the end signature
    //  to detect potential buffer overruns

    Size = Size - 2 * sizeof(uint32);
    Buffer = (void *)((ULONG_PTR)Buffer + sizeof(uint32));

#endif // BUFFER_VALIDATION

    if (Size <= sizeof(MEMORY_ZONE)) {
        return NULL;
    }

    Zone = (PMEMORY_ZONE)Buffer;

    Zone->ZoneSize = Size;
    Zone->Link = NULL;
    Zone->StorageHandle = storageHandle;
    Zone->LastSyncPoint = 0;

    Zone->Allocation.AtomicValue32 = 0;
    Zone->ReadyList.AtomicValue32 = 0;

    Zone->Allocation.FreeOffset = sizeof(MEMORY_ZONE);

    //  Assert the assumptions regarding the bit values that have been initialized
    //  with the dword write above

    EV_ASSERT(Zone->Allocation.Filled == 0);
    EV_ASSERT(Zone->Allocation.Committed  == 0);
    Zone->Generation = 0;

    SetEndOfBuffer(Zone);
    return Zone;
}

bool
RecycleZone(PMEMORY_ZONE Zone)
{
    CheckEndOfBuffer(Zone);

    ZONE_ALLOCATION_POINTER CapturedValue;
    ZONE_ALLOCATION_POINTER NextValue;

    do {

        CapturedValue.AtomicValue32 = Zone->Allocation.AtomicValue32;

        if (CapturedValue.Recycling) {

            //  Someone is already recycling this zone. Nothing left to do, just return

            return false;
        }

        //  Also test whether the zone has been already recycled and in is in use

        if ((CapturedValue.Filled == 0) || (CapturedValue.Committed == 0)) {

            return false;
        }

        NextValue.AtomicValue32 = CapturedValue.AtomicValue32;
        NextValue.Recycling = 1;

        //  Atomically also set the recycling flag to prevent other concurrent recycling

    } while (InterlockedCompareExchange(&Zone->Allocation.AtomicValue32,
                NextValue.AtomicValue32,
                CapturedValue.AtomicValue32) != CapturedValue.AtomicValue32);

    //  We sucessfully too ownership on recycling phase. We can now reinitialize the fields
    //  The last operation should be atomically updating the flags and offset in
    //  the allocation field

    EV_ASSERT(IsZoneCompleted(Zone));
    EV_ASSERT(Zone->Allocation.Count == Zone->ReadyList.Count);

    ZONE_ALLOCATION_POINTER Allocation;
    Allocation.AtomicValue32 = 0;
    Allocation.FreeOffset = sizeof(MEMORY_ZONE);
    Zone->LastSyncPoint = Allocation.FreeOffset;

    Zone->Generation = MemoryStorageGetNextGeneration(HANDLE_TO_STORAGE(Zone->StorageHandle));

    InterlockedExchange(&Zone->ReadyList.AtomicValue32, 0);
    InterlockedExchange(&Zone->Allocation.AtomicValue32, Allocation.AtomicValue32);

    return true;
}


void
MarkZoneFull(PMEMORY_ZONE Zone)
{
    ZONE_ALLOCATION_POINTER CapturedOffset;
    ZONE_ALLOCATION_POINTER NextValueOffset;

    CheckEndOfBuffer(Zone);

    do {

        CapturedOffset.AtomicValue32 = Zone->Allocation.AtomicValue32;

        if (CapturedOffset.Filled) {

            //  Someone already did it. We are done here.

            return;
        }

        NextValueOffset.AtomicValue32 = CapturedOffset.AtomicValue32;
        NextValueOffset.Filled = 1;

        //
        //  Atomically also set the committed flag if all entries have been commited
        //

        if (Zone->ReadyList.Count == CapturedOffset.Count) {

            NextValueOffset.Committed = 1;
        }

    } while (InterlockedCompareExchange(&Zone->Allocation.AtomicValue32,
                NextValueOffset.AtomicValue32,
                CapturedOffset.AtomicValue32) != CapturedOffset.AtomicValue32);

}

void
MarkZoneCommited(PMEMORY_ZONE Zone)
{
    ZONE_ALLOCATION_POINTER CapturedValue;
    ZONE_ALLOCATION_POINTER NextValue;

    CheckEndOfBuffer(Zone);

    do {

        CapturedValue.AtomicValue32 = Zone->Allocation.AtomicValue32;

        if ((CapturedValue.Committed == 1)
                ||
            (CapturedValue.Recycling == 1)
                ||
            (CapturedValue.Filled == 0)
                ||
            (Zone->ReadyList.Count != CapturedValue.Count)) {

            return;
        }

        NextValue.AtomicValue32 = CapturedValue.AtomicValue32;
        NextValue.Committed = 1;

    } while (InterlockedCompareExchange(&Zone->Allocation.AtomicValue32,
                NextValue.AtomicValue32,
                CapturedValue.AtomicValue32) != CapturedValue.AtomicValue32);

}


PMEMORY_HEADER
AllocateEventEntry(PMEMORY_ZONE Zone, uint16 size)
{
    PMEMORY_HEADER ReturnBuffer;
    ZONE_ALLOCATION_POINTER CapturedOffset;
    ZONE_ALLOCATION_POINTER NextValueOffset;
    uint16 Reqsize = size;

    CheckEndOfBuffer(Zone);

    size += sizeof(MEMORY_HEADER);
    size = (uint16)ROUND_UP_TO_POWER2(size, sizeof(uint64));

    do {

        CapturedOffset.AtomicValue32 = Zone->Allocation.AtomicValue32;
        ReturnBuffer = GetMemoryHeader(Zone, CapturedOffset.FreeOffset);

        if (CapturedOffset.Filled) {

            return NULL;
        }

        NextValueOffset.AtomicValue32 = CapturedOffset.AtomicValue32;
        NextValueOffset.FreeOffset += size;
        NextValueOffset.Count += 1;

        if ((NextValueOffset.FreeOffset >= Zone->ZoneSize)
                ||
            (NextValueOffset.FreeOffset < CapturedOffset.FreeOffset )) {

            MarkZoneFull(Zone);

            // After that call this zone might have been recycled, no operations

            return NULL;
        }
    } while (InterlockedCompareExchange(&Zone->Allocation.AtomicValue32,
                NextValueOffset.AtomicValue32,
                CapturedOffset.AtomicValue32) != CapturedOffset.AtomicValue32);

    EV_ASSERT(((ULONG_PTR)ReturnBuffer + size) <= ((ULONG_PTR)Zone + Zone->ZoneSize));
    EV_ASSERT((ULONG_PTR)ReturnBuffer >= ((ULONG_PTR)(Zone + 1)));
#ifdef BUFFER_VALIDATION
    ReturnBuffer->Link = 0xffff;
#endif

    ReturnBuffer->Size = (uint16)size;
    ReturnBuffer->Offset = CapturedOffset.FreeOffset;
    ReturnBuffer->Flags = 0;


    Struct_Microsoft_Singularity_ThreadContext *threadContext =
        Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext();
    Struct_Microsoft_Singularity_ProcessorContext *processorContext =
        Class_Microsoft_Singularity_Processor::g_GetCurrentProcessorContext();

#if SINGULARITY_KERNEL
    ReturnBuffer->TID = threadContext->threadIndex;
#else
    ReturnBuffer->TID = threadContext->kernelThreadIndex;
#endif
    ReturnBuffer->Cpu = processorContext->cpuRecord.id;

#if ISA_XSCALE
    ReturnBuffer->Timestamp = Class_Microsoft_Singularity_Isal_Isa::g_GetCycleCount();
#else // ISA_XSCALE
    // Guarantee strict ordering across all CPUs (which RDTSC does not provide)
    static long s_timestamp;
    ReturnBuffer->Timestamp = ::InterlockedIncrement(&s_timestamp);
#endif // ISA_XSCALE

    CheckEndOfBuffer(Zone);

    return ReturnBuffer;
}

void
CommitEventEntry(PMEMORY_HEADER Entry)
{
    PMEMORY_ZONE Zone = (PMEMORY_ZONE)((ULONG_PTR)Entry - Entry->Offset);
    ZONE_ALLOCATION_POINTER CapturedAllocationInfo;
    ZONE_READY_LIST CapturedReadyList;
    ZONE_READY_LIST NextReadyList;

    EV_ASSERT(Entry->Link == 0xffff);
    CheckEndOfBuffer(Zone);

    do {

        CapturedReadyList.AtomicValue32 = Zone->ReadyList.AtomicValue32;
        CapturedAllocationInfo.AtomicValue32 = Zone->Allocation.AtomicValue32;

        EV_ASSERT(CapturedAllocationInfo.Committed == 0);
        EV_ASSERT(CapturedAllocationInfo.Count > CapturedReadyList.Count);

        Entry->Link = CapturedReadyList.ReadyList;

        NextReadyList.Count = CapturedReadyList.Count + 1;
        NextReadyList.ReadyList = Entry->Offset;

        if (NextReadyList.Count == CapturedAllocationInfo.Count) {

            //  Remember the new high watermark for forward zone walking

            Zone->LastSyncPoint = CapturedAllocationInfo.FreeOffset;
        }

    } while (InterlockedCompareExchange(&Zone->ReadyList.AtomicValue32,
             NextReadyList.AtomicValue32,
             CapturedReadyList.AtomicValue32) != CapturedReadyList.AtomicValue32);

    if (Zone->Allocation.Filled) {

        //  The thread that took the last entry from the zone, did not had
        //  a chance to see this last commit. We need to update also the
        //  commit flag

        MarkZoneCommited(Zone);
    }


}


bool
IsZoneCompleted(PMEMORY_ZONE Zone)
{
    ZONE_ALLOCATION_POINTER CapturedValue;

    CapturedValue.AtomicValue32 = Zone->Allocation.AtomicValue32;
    return ((CapturedValue.Filled != 0) && (CapturedValue.Committed != 0));
}

bool
IsEntryCommited(PMEMORY_ZONE Zone, PMEMORY_HEADER Entry)
{
    // This function assumes the zone is locked for read so it does not get
    // recycled during this test

    uint16 offsetKey = Entry->Offset;

    if (offsetKey < Zone->LastSyncPoint) {

        return true;
    }

    uint16 crtOffset = Zone->ReadyList.ReadyList;

    while (crtOffset) {

        if (crtOffset == offsetKey) {

            return true;
        }

        Entry = (PMEMORY_HEADER)((ULONG_PTR)Zone + crtOffset);
        crtOffset = Entry->Link;
    }

    return false;
}

PMEMORY_HEADER
GetFirstReadyEntry(PMEMORY_ZONE Zone, uint16 offset)
{
    PMEMORY_HEADER Entry;

    // This function assumes the zone is locked for read so it does not get
    // recycled during this test

    uint16 offsetFound = Zone->ZoneSize;
    uint16 crtOffset = Zone->ReadyList.ReadyList;

    while (crtOffset) {

        if ((crtOffset > offset) && (crtOffset < offsetFound)) {

            offsetFound = crtOffset;
        }

        Entry = (PMEMORY_HEADER)((ULONG_PTR)Zone + crtOffset);
        crtOffset = Entry->Link;
    }

    if (offsetFound != Zone->ZoneSize) {

        return (PMEMORY_HEADER)((ULONG_PTR)Zone + offsetFound);

    }
    return NULL;
}


PMEMORY_HEADER
GetFirstEntry(PMEMORY_ZONE Zone, bool forward)
{
    if (forward) {

        return GetFirstReadyEntry(Zone, 0);
    }

    uint16 crtOffset = Zone->ReadyList.ReadyList;

    if (crtOffset == 0) {

        return NULL;
    }

    return (PMEMORY_HEADER)((ULONG_PTR)Zone + crtOffset);
}



PMEMORY_HEADER
GetNextEntry(PQUERY_VIEW view)
{
    PMEMORY_ZONE Zone = view->CurrentZone;
    PMEMORY_HEADER Entry = view->CurrentEntry;

    if (!Zone->Allocation.Filled) {

        // The Zone is during allocations

        if (view->ZoneGeneration != Zone->Generation) {

            //  We lost the context as the zone has been recycled

            return NULL;
        }
    }

    if (view->Forward) {

        view->CurrentEntryIndex += 1;

        if (view->CurrentEntryIndex >= Zone->Allocation.Count) {

            return NULL;
        }

        view->CurrentEntry = (PMEMORY_HEADER)((ULONG_PTR)Entry + Entry->Size);

        if ((Zone->Allocation.Filled != 0) || IsEntryCommited(Zone, Entry)) {

            // Valid entry

            Entry = view->CurrentEntry;

        } else {

            view->CurrentEntry = GetFirstReadyEntry(Zone, Entry->Offset);
            Entry = view->CurrentEntry;
        }

    } else {

        if (Entry->Link == 0) {

            //  We finished to walk the chain backwards

            return NULL;
        }

        view->CurrentEntry = (PMEMORY_HEADER)((ULONG_PTR)Zone + Entry->Link);
        Entry = view->CurrentEntry;
    }

    return Entry;
}

//
///////////////////////////////////////////////////////////////// End of File.
