///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   halkd.cpp - runtime support for kernel debugging
//
//  For more information see:
//      \nt\base\ntos\kd64
//      \nt\base\boot\kdcom
//      \nt\base\boot\kd1394
//      \nt\base\boot\kdusb2
//      \nt\sdktools\debuggers\ntsd64
//
//  Note:   Kernel Only
//
#include "hal.h"
#include "halkd.h"

extern "C" void *  __cdecl memcpy(void *, const void *, size_t);
extern "C" void *  __cdecl memset(void *, int, size_t);

#define FALSE   0
#define TRUE    1

#define ASSERT(x)
#define NT_SUCCESS(Status) ((NTSTATUS)(Status) >= 0)

//
// Debugger Debugging
//
#define KDDBG if (0) kdprintf
#define KDDBG2 if (0) kdprintf
#define KDDBG3 if (0) kdprintf

#define KeProcessorLevel 15

//
// Globals
//
BOOL KdDebuggerNotPresent = FALSE;
BOOL KdAlwaysPrintOutput = FALSE;

#define KDP_MESSAGE_BUFFER_SIZE 4096
static CHAR KdpMessageBuffer[KDP_MESSAGE_BUFFER_SIZE];
static BOOL KdpContextSent;

static KPROCESSOR_STATE KdpProcessorState[MAX_CPU];
static KD_CONTEXT KdpContext;
static int KeNumberProcessors = 1;

KDP_BREAKPOINT_TYPE KdpBreakpointInstruction = KDP_BREAKPOINT_VALUE;
BREAKPOINT_ENTRY KdpBreakpointTable[BREAKPOINT_TABLE_SIZE] = {0};

//
// Some quick macros to avoid having to edit too much NT code
//
#define RtlZeroMemory(base, len)            memset((base), 0, (len))
#define KdpQuickMoveMemory(dst, src, len)     memcpy((dst), (src), (len))

// Read memory from an untrusted pointer into a trusted buffer.
#define KdpCopyFromPtr(Dst, Src, Size, Done) \
    KdpCopyMemoryChunks((ULONG_PTR)(Src), Dst, Size, 0,                       \
                        MMDBG_COPY_UNSAFE, Done)
// Write memory from a trusted buffer through an untrusted pointer.
#define KdpCopyToPtr(Dst, Src, Size, Done) \
    KdpCopyMemoryChunks((ULONG_PTR)(Dst), Src, Size, 0,                       \
                        MMDBG_COPY_WRITE | MMDBG_COPY_UNSAFE, Done)

#define RtlInitUnicodeString(string, source, length) \
 { (string)->Buffer = (source); (string)->Length = (string)->MaximumLength = (length); }

#define FORCEINLINE __inline

void
FORCEINLINE
InitializeListHead(
    IN PLIST_ENTRY ListHead
    )
{
    ListHead->Flink = ListHead->Blink = ListHead;
}

BOOLEAN
FORCEINLINE
RemoveEntryList(
    IN PLIST_ENTRY Entry
    )
{
    PLIST_ENTRY Blink;
    PLIST_ENTRY Flink;

    Flink = Entry->Flink;
    Blink = Entry->Blink;
    Blink->Flink = Flink;
    Flink->Blink = Blink;
    return (BOOLEAN)(Flink == Blink);
}

void
FORCEINLINE
InsertTailList(
    IN PLIST_ENTRY ListHead,
    IN PLIST_ENTRY Entry
    )
{
    PLIST_ENTRY Blink;

    Blink = ListHead->Blink;
    Entry->Flink = ListHead;
    Entry->Blink = Blink;
    Blink->Flink = Entry;
    ListHead->Blink = Entry;
}

//#define KdpCopyFromPtr(dst, src, size, done)  { memcpy((dst), (src), (size)); *(done)=(size); }
//#define KdpCopyToPtr(dst, src, size, done)  { memcpy((dst), (src), (size)); *(done)=(size); }

//
// KdpRetryCount controls the number of retries before we give
// up and assume kernel debugger is not present.
// KdpNumberRetries is the number of retries left.  Initially,
// it is set to 5 such that booting NT without debugger won't be
// delayed to long.
//
UINT32 KdCompNumberRetries = 5;
UINT32 KdCompRetryCount    = 5;
UINT32 KdPacketId = 0;

static void KdpNulSendPacket(UINT32 PacketType,
                             IN PSTRING MessageHeader,
                             IN PSTRING MessageData OPTIONAL,
                             IN OUT PKD_CONTEXT KdContext)
{
}

static KDP_STATUS KdpNulReceivePacket(IN UINT32 PacketType,
                                      OUT PSTRING MessageHeader,
                                      OUT PSTRING MessageData,
                                      OUT UINT32 * DataLength,
                                      IN OUT PKD_CONTEXT KdContext)
{
    return KDP_PACKET_TIMEOUT;
}

static bool KdpNulPollBreakIn()
{
    return false;
}

void (*KdSendPacket)(UINT32 PacketType,
                     IN PSTRING MessageHeader,
                     IN PSTRING MessageData OPTIONAL,
                     IN OUT PKD_CONTEXT KdContext) = KdpNulSendPacket;
KDP_STATUS (*KdReceivePacket)(IN UINT32 PacketType,
                         OUT PSTRING MessageHeader,
                         OUT PSTRING MessageData,
                         OUT UINT32 * DataLength,
                         IN OUT PKD_CONTEXT KdContext) = KdpNulReceivePacket;
bool (*KdPollBreakIn)() = KdpNulPollBreakIn;

//
// Static data - these are walked by the kernel debugger
//

//PsLoadedModuleList ===========================================================

struct KLDR_DATA_TABLE_ENTRY_WITH_NAME : KLDR_DATA_TABLE_ENTRY
{
    WCHAR   wzName[32];
};

static KLDR_DATA_TABLE_ENTRY_WITH_NAME KdModuleKernelEntry[128];
static UINT32 KdModuleKernelUsed = 0;
static LIST_ENTRY PsLoadedModuleList;

// KdVersionBlock =============================================================

static DBGKD_GET_VERSION64 KdVersionBlock = {
    DBGKD_MAJOR_SINGULARITY << 8, // MajorVersion
    0, // Minor
    DBGKD_64BIT_PROTOCOL_VERSION2, // Protocol
    DBGKD_VERS_FLAG_NOMM, //DBGKD_VERS_FLAG_DATA, // Flags
#if ISA_IX86
    IMAGE_FILE_MACHINE_X86, // Machine Type
#elif ISA_IX64
    IMAGE_FILE_MACHINE_X64, // Machine Type
#elif ISA_ARM
    IMAGE_FILE_MACHINE_ARM, // Machine Type
#endif
    PACKET_TYPE_MAX, // Max packet
    DbgKdMaximumStateChange - DbgKdMinimumStateChange, // MaxStateChange
    DbgKdSetContextApi /*DbgKdMaximumManipulate*/ - DbgKdMinimumManipulate, // MaxManipulate we support
    0, // Simulation
    0, // Unused
    0, // KernBase
    0, // PsLoadedModuleList
    0 // DebuggerDataList
};

// ========================================================================

// Forward declarations

static void KdpMpLock(void);
static void KdpMpUnlock(void);

static void KdpMpEnter(void);
static void KdpMpLeave(void);

static void KdpUpLock(void);
static void KdpUpUnlock(void);

static void KdpUpEnter(void);
static void KdpUpLeave(void);

static void KdpFakeOutPsLoadedModuleList(Class_Microsoft_Singularity_Hal_Platform *);

static KCONTINUE_STATUS
KdpSendWaitContinue(
    IN UINT32 OutPacketType,
    IN PSTRING OutMessageHeader,
    IN PSTRING OutMessageData OPTIONAL,
    IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *Context
    );

static void LoadedBinary(KdDebugTrapData *trapData,
                         Struct_Microsoft_Singularity_Isal_SpillContext *context);
static void UnloadedBinary(KdDebugTrapData *trapData,
                           Struct_Microsoft_Singularity_Isal_SpillContext *context);

extern int printf(const char *pszFmt, ...);

#if ISA_ARM
void (*KdpLock)() = KdpUpLock;
void (*KdpUnlock)() = KdpUpUnlock;
void (*KdpEnter)() = KdpUpEnter;
void (*KdpLeave)() = KdpUpLeave;
#else
void (*KdpLock)() = KdpMpLock;
void (*KdpUnlock)() = KdpMpUnlock;
void (*KdpEnter)() = KdpMpEnter;
void (*KdpLeave)() = KdpMpLeave;
#endif

// Ack! We cannot replicate the entire pathway through HAL just so single-stepping
// doesn't become nested and confused.
static bool KdpDisableInterrupts(void)
{
    return KdpDisableInterruptsInline();
}

static void KdpRestoreInterrupts(bool enabled)
{
    return KdpRestoreInterruptsInline(enabled);
}

//////////////////////////////////////////////////////////////////////////////
//
static volatile INT32 KdpInDebugger = 0;
static volatile bool KdpInDebuggerIntEnabled = FALSE;

//
// Sending IPI's to other processors may be broken at times, and
// this allows recursive entry to the debugger from breakpoints
// or exceptions in the SendIPI code.
//
static volatile INT32 KdpCpuInDebugger = -1;
static volatile INT32 KdpMpEnterCount = 0;
static volatile INT32 KdpLockEnterCount = 0;

static CHAR KdpDbgMessageBuffer[KDP_MESSAGE_BUFFER_SIZE];

#define MAXIMUM_RETRIES 20

void KdInitialize(Class_Microsoft_Singularity_Hal_Platform *platform)
{
    kdprintf("KdInitialize! [CpuMaxCount=%d]\n", platform->CpuMaxCount);

    if (platform->CpuMaxCount == 1) {
        KdpLock = KdpUpLock;
        KdpUnlock = KdpUpUnlock;
        KdpEnter = KdpUpEnter;
        KdpLeave = KdpUpLeave;
    }
    else  {
        KdpLock = KdpMpLock;
        KdpUnlock = KdpMpUnlock;
        KdpEnter = KdpMpEnter;
        KdpLeave = KdpMpLeave;
    }

    KdpLock();

    //
    // Note that this is not quite right - the Hal debugger routines are only called
    // if DEBUGGER_SERIAL is configured.  The right thing to do is always go through the HAL,
    // and then do the switching between serial/1394 inside the hal.
    //  @todo: Fix this when reconciling native HAL.
    //

    switch (platform->DebuggerType) {

    default:
    case Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_NONE:
        kdprintf("No debugger.\n");

        KdSendPacket = KdpNulSendPacket;
        KdReceivePacket = KdpNulReceivePacket;
        KdPollBreakIn = KdpNulPollBreakIn;

        KdDebuggerNotPresent = TRUE;
        KdAlwaysPrintOutput = TRUE;  // do we really want to do this?
        break;

    case Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_SERIAL:
        kdprintf("Serial Debugger:\n");
        KdSendPacket = KdpSerialSendPacket;
        KdReceivePacket = KdpSerialReceivePacket;
        KdPollBreakIn = KdpSerialPollBreakIn;

        KdDebuggerNotPresent = FALSE;
        break;

    case Class_Microsoft_Singularity_Hal_Platform_DEBUGGER_1394:
        kdprintf("1394 Debugger:\n");

        KdSendPacket = Kdp1394SendPacket;
        KdReceivePacket = Kdp1394ReceivePacket;
        KdPollBreakIn = Kdp1394PollBreakIn;

        KdDebuggerNotPresent = FALSE;
        break;
    }

    // Retries are set to this after boot
    KdpContext.KdpDefaultRetries = MAXIMUM_RETRIES;

    KdpUnlock();

    KdpFakeOutPsLoadedModuleList(platform);
}

//
// Return current CPU ID
//
int KdCurrentCpuId()
{
    return Class_Microsoft_Singularity_Isal_Isa::g_GetCurrentCpu()->id;
}

//
//  MP-safe versions of lock/unlock enter/leave kd functions
//

static void KdpMpLock()
{
    for (;;) {
        bool enabled = KdpDisableInterrupts();
        if (InterlockedCompareExchange(&KdpInDebugger, 1, 0) == 0) {
            KdpInDebuggerIntEnabled = enabled;

            KdpCpuInDebugger = KdCurrentCpuId();
            KdpLockEnterCount++;
            return;
        }

        // Check to see if its already us recursively
        if (KdpCpuInDebugger == KdCurrentCpuId()) {
            KdpLockEnterCount++;
            kdprintf("CPU %d: KdpMpLock: Entered Recursively due to breakpoint or exception, EnterCount %d\n",
                      KdpCpuInDebugger, KdpLockEnterCount);
            return;
        }
        KdpRestoreInterrupts(enabled);
        KdpPause();
    }
}

static void KdpMpUnlock()
{
    KdpLockEnterCount--;

    // Recursive lock leave
    if (KdpLockEnterCount != 0) {
        return;
    }

    // Must grab the state of interrupts before we release our lock.  Fortunately,
    // KdpInDebuggerIntEnabled is volatile, so the compiler will not reorder our
    // read:
    bool intEnabled = KdpInDebuggerIntEnabled;

    KdpCpuInDebugger = -1;

    KdpInDebugger = 0;
    KdpRestoreInterrupts(intEnabled);
}

static void KdpMpEnter()
{
    KdpMpEnterCount++;

    // Only attempt to stop processors on the first entry
    if (KdpMpEnterCount == 1) {
        if (KeNumberProcessors > 1) {
             KDDBG("CPU %d: KdpMpEnter, calling FreezeAllProcessors...\n", KdCurrentCpuId());
             Class_Microsoft_Singularity_MpExecution::g_FreezeAllProcessors();
             KDDBG("CPU %d: KdpMpEnter, return from FreezeAllProcessors...\n", KdCurrentCpuId());
        }
    }
}

static void KdpMpLeave()
{
    KdpMpEnterCount--;
    Class_Microsoft_Singularity_MpExecution::g_ThawAllProcessors();
}

//
//  Single processor versions of lock/unlock enter/leave kd functions
//

static void KdpUpLock()
{
    bool enabled = KdpDisableInterrupts();
    KdpInDebugger++;

    if (KdpInDebugger == 1) {
        KdpInDebuggerIntEnabled = enabled;
    }
}

static void KdpUpUnlock()
{
    KdpInDebugger--;
    if (KdpInDebugger == 0) {
        KdpRestoreInterrupts(KdpInDebuggerIntEnabled);
    }
}

static void KdpUpEnter(void)
{
}

static void KdpUpLeave(void)
{
}

//////////////////////////////////////////////////////////////////////////////
//
extern int strformat(void (*pfOutput)(void *pContext, char c), void *pContext,
                     const char * pszFmt, va_list args);


static void koutput(void *pContext, char c)
{
#if ISA_IX86 || ISA_IX64
#define KD_LEFT     0
#define KD_HEIGHT   46

    static UINT16 kdcurs = KD_LEFT;
    static UINT16 kdattr = 0x2f00;

    //
    // Update cursor position
    //
    if ((kdcurs % 80) < KD_LEFT) {
        kdcurs += KD_LEFT - (kdcurs % 80);
    }

    if (kdcurs >= KD_HEIGHT * 80) {
        for (UINT16 i = 0; i < KD_HEIGHT - 1; i++) {
            for (UINT16 j = KD_LEFT; j < 80; j++) {
                ((UINT16 *)0xb8000)[i*80+j] = ((UINT16 *)0xb8000)[i*80+80+j];
            }
        }
        for (UINT16 j = KD_LEFT; j < 80; j++) {
            ((UINT16 *)0xb8000)[(KD_HEIGHT-1)*80+j] = kdattr | ' ';
        }
        kdcurs = kdcurs - 80;
    }

    //
    // Output character
    //
    if (c >= ' ' && c <= '~') {
        ((UINT16 *)0xb8000)[kdcurs++] = kdattr | c;
    }
    else if (c == '\t') {
        kdcurs += 8 - (kdcurs % 8);
    }
    else if (c == '\n') {
        while ((kdcurs % 80) != 0) {
            ((UINT16 *)0xb8000)[kdcurs++] = kdattr | ' ';
        }
    }
    else if (c == '\r') {
        kdcurs -= (kdcurs % 80);
    }
    else if (c == '\f') {
        kdcurs = 0;
    }
#elif ISA_ARM
    // Do nothing.
#endif
}

void kdprints(const char * pszFmt)
{
    while (*pszFmt) {
        koutput(NULL, *pszFmt++);
    }
}

void kdprintf(const char * pszFmt, ...)
{
    va_list args;

    va_start(args, pszFmt);
    strformat(koutput, NULL, pszFmt, args);
    va_end(args);
}

BOOL
ProbeMemoryRange(UINT64 address, UINT32 length)
{
    Struct_Microsoft_Singularity_SMAPINFO *sm =
        (Struct_Microsoft_Singularity_SMAPINFO *)Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->Smap32;
    int smapCount = Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->SmapCount;

    for (int32 i = 0; i < smapCount; i++) {
        if (// (sm[i].type == Struct_Microsoft_Singularity_SMAPINFO_AddressTypeFree) &&
            (sm[i].addr <= address) &&
            (sm[i].addr + sm[i].size) >= (address + length)) {

            return true;
        }
    }

    if ((address >= Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->Smap32) &&
        ((address + length) <= (Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->Smap32 + 4096))) {

        return true;
    }

    if ((address >= Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogRecordBuffer) &&
        ((address + length) <= (Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogRecordBuffer + Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogRecordSize))) {

        return true;
    }

    if ((address >= Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogTextBuffer) &&
        ((address + length) <= (Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogTextBuffer + Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogTextSize))) {

        return true;
    }

    if ((address >= Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->Smap32) &&
        ((address + length) <= (Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->Smap32 + 4096))) {

        return true;
    }

    if ((address >= Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogRecordBuffer) &&
        ((address + length) <= (Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogRecordBuffer + Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogRecordSize))) {

        return true;
    }

    if ((address >= Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogTextBuffer) &&
        ((address + length) <= (Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogTextBuffer + Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->LogTextSize))) {

        return true;
    }

#if ISA_IX
    // TODO: HACK!HACK!HACK! These I/O ranges
    // should not be hardcoded, but probed and put into the SMAP
    // as reserved, .
    const UINT64 ApicBase     = 0xfee00000;
    const UINT32 ApicLength   = 0x1000;
    const UINT64 IoApic0Base  = 0xfec00000;
    const UINT32 IoApicLength = 0x100;
    const UINT64 IoApic1Base  = 0xfec80000;

    if (address >= ApicBase &&
        address <= ApicBase + ApicLength) {
        return true;
    }
    if (address >= IoApic0Base &&
        address <= IoApic0Base + IoApicLength) {
        return true;
    }
    if (address >= IoApic1Base &&
        address <= IoApic1Base + IoApicLength) {
        return true;
    }
#endif

    //
    // TODO: revisit this with paging and new MM design
    //
#if ISA_ARM
    KDDBG("ProbeFailed %p..%p\n", (UIntPtr)address, (UIntPtr)(address + length));
#endif

    return false;
}

//////////////////////////////////////////////////////////////////////////////
//
UINT32 KdpComputeChecksum(IN PCHAR Buffer, IN UINT32 Length)
{
    // Compute the checksum for the string passed in.
    UINT32 Checksum = 0;

    while (Length > 0) {
        Checksum = Checksum + (UINT32)*(PUCHAR)Buffer++;
        Length--;
    }

    return(Checksum);
} // KdpComputeChecksum

//////////////////////////////////////////////////////////////////////////////
//
UINT16 KdpGetCurrentProcessorNumber()
{
    return (UINT16) Class_Microsoft_Singularity_Isal_Isa::g_GetCurrentCpu()->id;
} // KdpGetCurrentProcessorNumber

//////////////////////////////////////////////////////////////////////////////

//
// Misc KD functions
//

NTSTATUS
KdpCopyMemoryChunks(
    UINT64 Address,
    PVOID Buffer,
    UINT32 TotalSize,
    UINT32 ChunkSize,
    UINT32 Flags,
    UINT32 * ActualSize OPTIONAL
    )
    //  Routine Description:
    //      Copies memory to/from a buffer to/from a system address.
    //      The address can be physical or virtual.
    //      The buffer is assumed to be valid for the duration of this call.
    //
    //  Arguments:
    //      Address - System address.
    //      Buffer - Buffer to read from or write to.
    //      TotalSize - Number of bytes to read/write.
    //      ChunkSize - Maximum single item transfer size, must
    //                  be 1, 2, 4 or 8.
    //                  0 means choose a default.
    //      Flags - MMDBG_COPY flags for MmDbgCopyMemory.
    //      ActualSize - Number of bytes actually read/written.
{
    UINT32 Length;
    UINT32 CopyChunk;

    if (ChunkSize > MMDBG_COPY_MAX_SIZE) {
        ChunkSize = MMDBG_COPY_MAX_SIZE;
    }
    else if (ChunkSize == 0) {
        // Default to 4 byte chunks as that's
        // what the previous code did.
        ChunkSize = 4;
    }

    //
    // MmDbgCopyMemory only copies a single aligned chunk at a
    // time.  It is Kd's responsibility to chunk up a larger
    // request for individual copy requests.  This gives Kd
    // the flexibility to pick a chunk size and also frees
    // Mm from having to worry about more than a page at a time.
    // Additionally, it is important that we access memory with the
    // largest size possible because we could be accessing
    // memory-mapped I/O space.
    //

    Length = TotalSize;
    CopyChunk = 1;

    while (Length > 0) {

        // Expand the chunk size as long as:
        //   We haven't hit the chunk limit.
        //   We have enough data left.
        //   The address is properly aligned.
        while (CopyChunk < ChunkSize &&
               (CopyChunk << 1) <= Length &&
               (Address & ((CopyChunk << 1) - 1)) == 0) {
            CopyChunk <<= 1;
        }

        // Shrink the chunk size to fit the available data.
        while (CopyChunk > Length) {
            CopyChunk >>= 1;
        }

        if (Address < Class_Microsoft_Singularity_Hal_Platform::c_thePlatform->PhysicalBase) {
            break;
        }
        if (Address == 0) {
            break;
        }
#if PAGING
        UINT64 RawAddress = Address;
        if (Flags & MMDBG_COPY_PHYSICAL) {
            // Temporarily map the physical memory range.
            // TODO: KernelMapPhysicalMemory tries to acquire a lock -- if
            // this lock is not free, we may deadlock here.
            // Also, remapping for every chunk is inefficient.
            KDDBG("Physical address = 0x%x size = 0x%x\n", int(Address), int(CopyChunk));
            Struct_Microsoft_Singularity_Memory_PhysicalAddress physical;
            Struct_Microsoft_Singularity_Memory_PhysicalAddress::m__ctor(
                &physical,
                UIntPtr(Address));
            Address = UINT64(Class_Microsoft_Singularity_Memory_MemoryManager
                ::g_KernelMapPhysicalMemory(
                    physical,
                    UIntPtr(CopyChunk)));
            KDDBG("Physical address 0x%x mapped to virtual address 0x%x\n", int(RawAddress), int(Address));
        }
        else {
            if (Class_Microsoft_Singularity_Memory_MemoryManager::c_isInitialized
                && !Class_Microsoft_Singularity_Memory_VMManager::g_IsPageMapped(
                        Class_Microsoft_Singularity_Memory_MemoryManager::g_PageAlign(
                            UIntPtr(Address)))) {
                break;
            }
        }

#endif
        //
        //  It is illegal to just touch the memory that the debugger just asked for
        //  w/o making sure it is valid. Otherwise this will trap inside the debugger
        //  code, hanging both the system and debugger. We need to ansure the memory
        //  is valid. For now just check against the smap.
        //

        if (!ProbeMemoryRange(Address, CopyChunk)) {
            break;
        }

        if (Flags & MMDBG_COPY_WRITE) {
            memcpy((void*)Address, Buffer, CopyChunk);
        }
        else {
            memcpy(Buffer, (void*)Address, CopyChunk);
        }

#if PAGING
        if (Flags & MMDBG_COPY_PHYSICAL) {
            KDDBG("Unmapping physical address 0x%x (virtual address 0x%x)\n", int(RawAddress), int(Address));
            Class_Microsoft_Singularity_Memory_MemoryManager
                ::g_KernelUnmapPhysicalMemory(
                    UIntPtr(Address), UIntPtr(Address + CopyChunk));
            KDDBG("Unmapped physical address 0x%x (virtual address 0x%x)\n", int(RawAddress), int(Address));
            Address = RawAddress;
        }
#endif

        Address += CopyChunk;
        Buffer = (PVOID)((PUCHAR)Buffer + CopyChunk);
        Length -= CopyChunk;
    }

    if (ActualSize) {
        *ActualSize = TotalSize - Length;
    }

    //
    // Flush the instruction cache in case the write was into the instruction
    // stream.  Only do this when writing into the kernel address space,
    // and if any bytes were actually written
    //

    if ((Flags & MMDBG_COPY_WRITE) && Length < TotalSize) {
        KdpFlushInstCache();
    }

    return Length != 0 ? STATUS_UNSUCCESSFUL : STATUS_SUCCESS;
}

static
void
KdpSetCommonState(
    IN UINT32 NewState,
    IN Struct_Microsoft_Singularity_Isal_SpillContext *Context,
    OUT PDBGKD_ANY_WAIT_STATE_CHANGE WaitStateChange
    )
{
    UINT32 InstrCount;
    PUCHAR InstrStream;

    WaitStateChange->NewState = NewState;
    WaitStateChange->ProcessorLevel = KeProcessorLevel;
    WaitStateChange->Processor = KdpGetCurrentProcessorNumber();
    WaitStateChange->NumberProcessors = KeNumberProcessors;
    WaitStateChange->Thread
        = SIGN_EXTEND(Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext()->_thread);

#if ISA_IX86
    WaitStateChange->ProgramCounter = SIGN_EXTEND(Context->ip);
#elif ISA_IX64
    WaitStateChange->ProgramCounter = Context->ip;
#elif ISA_ARM
    WaitStateChange->ProgramCounter = SIGN_EXTEND(Context->pc);
#endif
    RtlZeroMemory(&WaitStateChange->AnyControlReport,
                  sizeof(WaitStateChange->AnyControlReport));

    //
    // Copy instruction stream immediately following location of event.
    //
    PCHAR PcMemory = (PCHAR)WaitStateChange->ProgramCounter;

    InstrStream = (PUCHAR)&WaitStateChange->ControlReport.InstructionStream;
    KdpCopyFromPtr(InstrStream, PcMemory,
                   sizeof(WaitStateChange->ControlReport.InstructionStream), &InstrCount);
    WaitStateChange->ControlReport.InstructionCount = (UINT16)InstrCount;

    //
    // Clear breakpoints in copied area.
    // If there were any breakpoints cleared, recopy the instruction area
    // without them.
    //

    // if (KdpDeleteBreakpointRange(PcMemory, PcMemory + InstrCount - 1)) {
    //    KdpCopyFromPtr(InstrStream, PcMemory, InstrCount, &InstrCount);
    // }
}

UINT32 WcsToStr(WCHAR *pwcsSrc, UINT32 Length, PCHAR pszDst)
{
    for (UINT32 n = 0; n < Length; n++) {
        *pszDst++ = (char)*pwcsSrc++;
    }
    *pszDst++ = '\0';

    return Length + 1;
}

bool
KdpReportLoadSymbolsStateChange(
    IN WCHAR *PathName,
    IN UINT32 PathNameLength,
    IN UINT64 BaseOfDll,
    IN UINT32  ProcessId,
    IN UINT32  CheckSum,
    IN UINT32  SizeOfImage,
    IN BOOLEAN UnloadSymbols,
    IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *Context
    )
    //  Routine Description:
    //      This routine sends a load symbols state change packet to the kernel
    //      debugger and waits for a manipulate state message.
    //
    //  Arguments:
    //      PathName - Supplies a pointer to the pathname of the image whose
    //          symbols are to be loaded.
    //      BaseOfDll - Supplies the base address where the image was loaded.
    //      ProcessId - Unique identifier for process that is using
    //          the symbols.  -1 for system process.
    //      CheckSum - Checksum from image header.
    //      UnloadSymbol - TRUE if the symbols that were previously loaded for
    //          the named image are to be unloaded from the debugger.
{
    // NB: \nt\sdktools\debuggers\ntsd64\event.cpp
    // PathNameLength = 0, ProcessId = 0, BaseOfDll = -1 for reboot.
    // PathNameLength = 0, ProcessId = 0, BaseOfDll = -2 for hibernate.

    STRING MessageData;
    STRING MessageHeader;
    DBGKD_ANY_WAIT_STATE_CHANGE WaitStateChange;
    KCONTINUE_STATUS Status;

    KDDBG("KdpReportLoadSymbolsStateChange %p\n", Context);

    do {
        //
        // Construct the wait state change message and message descriptor.
        //

        KdpSetCommonState(DbgKdLoadSymbolsStateChange, Context,
                          &WaitStateChange);

        WaitStateChange.LoadSymbols.UnloadSymbols = UnloadSymbols;
        WaitStateChange.LoadSymbols.BaseOfDll = SIGN_EXTEND(BaseOfDll);
        WaitStateChange.LoadSymbols.ProcessId = ProcessId;
        WaitStateChange.LoadSymbols.CheckSum = CheckSum;
        WaitStateChange.LoadSymbols.SizeOfImage = SizeOfImage;
        if (PathName != NULL) {
            WaitStateChange.LoadSymbols.PathNameLength =
                WcsToStr(PathName, PathNameLength, KdpMessageBuffer);
        }
        else {
            WaitStateChange.LoadSymbols.PathNameLength = 0;
        }
        MessageData.Buffer = KdpMessageBuffer;
        MessageData.Length = (UINT16)WaitStateChange.LoadSymbols.PathNameLength;

        KdpSetControlReport(&WaitStateChange.ControlReport, Context);

        MessageHeader.Length = sizeof(WaitStateChange);
        MessageHeader.Buffer = (PCHAR)&WaitStateChange;

        Status = KdpSendWaitContinue(
                    PACKET_TYPE_KD_STATE_CHANGE64,
                    &MessageHeader,
                    &MessageData,
                    Context
                    );

    } while (Status == ContinueProcessorReselected) ;

    return (Status == ContinueSuccess) ? true : false;
}

static
KCONTINUE_STATUS
KdpReportExceptionStateChange(
    IN EXCEPTION_RECORD64 *ExceptionRecord,
    IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *Context,
    IN BOOLEAN FirstChance
    )
    //  Routine Description:
    //      This routine sends an exception state change packet to the kernel
    //      debugger and waits for a manipulate state message.
    //
    //  Arguments:
    //      ExceptionRecord - Supplies a pointer to an exception record.
    //      Context - Supplies a pointer to a context record.
    //      FirstChance - Supplies a boolean value that determines whether this is
    //          the first or second chance for the exception.
    //
    //  Return Value:
    //      A value of TRUE is returned if the exception is handled. Otherwise, a
    //      value of FALSE is returned.
{
    STRING MessageData;
    STRING MessageHeader;
    DBGKD_ANY_WAIT_STATE_CHANGE WaitStateChange;
    KCONTINUE_STATUS Status;

    KDDBG("KdpReportExceptionStateChange %p\n", Context);

    do {

        //
        // Construct the wait state change message and message descriptor.
        //

        KdpSetCommonState(DbgKdExceptionStateChange, Context,
                          &WaitStateChange);

        WaitStateChange.Exception.ExceptionRecord = *ExceptionRecord;
        WaitStateChange.Exception.FirstChance = FirstChance;

        KdpSetControlReport(&WaitStateChange.ControlReport, Context);

        MessageHeader.Length = sizeof(WaitStateChange);
        MessageHeader.Buffer = (PCHAR)&WaitStateChange;
        MessageData.Length = 0;

        //
        // Send packet to the kernel debugger on the host machine,
        // wait for answer.
        //
        Status = KdpSendWaitContinue(
                    PACKET_TYPE_KD_STATE_CHANGE64,
                    &MessageHeader,
                    &MessageData,
                    Context
                    );
    } while (Status == ContinueProcessorReselected) ;

    return Status;
}


static
void
KdpReadVirtualMemory(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData
    )
    //  Routine Description:
    //      This function is called in response to a read virtual memory 32-bit
    //      state manipulation message. Its function is to read virtual memory
    //      and return.
    //
    //  Arguments:
    //      m - Supplies a pointer to the state manipulation message.
    //      AdditionalData - Supplies a pointer to a descriptor for the data to read.
{
    UINT32 Length;
    STRING MessageHeader;

    //
    // Trim the transfer count to fit in a single message.
    //

    Length = m->ReadMemory.TransferCount;
    if (Length > (PACKET_MAX_SIZE - sizeof(DBGKD_MANIPULATE_STATE64))) {
        Length = PACKET_MAX_SIZE - sizeof(DBGKD_MANIPULATE_STATE64);
    }

    //
    // Move the data to the destination buffer.
    //

    m->ReturnStatus =
        KdpCopyMemoryChunks((UINT64)(ULONG_PTR)m->ReadMemory.TargetBaseAddress,
                            AdditionalData->Buffer,
                            Length,
                            0,
                            MMDBG_COPY_UNSAFE,
                            &Length);

    //
    // Set the actual number of bytes read, initialize the message header,
    // and send the reply packet to the host debugger.
    //

    AdditionalData->Length = (UINT16)Length;
    m->ReadMemory.ActualBytesRead = Length;

    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 AdditionalData,
                 &KdpContext);

    return;
}

static
void
KdpWriteVirtualMemory(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData
    )
    //  Routine Description:
    //      This function is called in response of a write virtual memory 32-bit
    //      state manipulation message. Its function is to write virtual memory
    //      and return.
    //
    //  Arguments:
    //      m - Supplies a pointer to the state manipulation message.
    //      AdditionalData - Supplies a pointer to a descriptor for the data to write.
    //      Context - Supplies a pointer to the current context.
{

    STRING MessageHeader;

    //
    // Move the data to the destination buffer.
    //

    m->ReturnStatus =
        KdpCopyMemoryChunks((UINT64)(ULONG_PTR)m->WriteMemory.TargetBaseAddress,
                            AdditionalData->Buffer,
                            AdditionalData->Length,
                            0,
                            MMDBG_COPY_WRITE | MMDBG_COPY_UNSAFE,
                            &m->WriteMemory.ActualBytesWritten);

    //
    // Set the actual number of bytes written, initialize the message header,
    // and send the reply packet to the host debugger.
    //

    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 NULL,
                 &KdpContext);

    return;
}

static
void
KdpReadPhysicalMemory(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData
    )
    //  Routine Description:
    //      This function is called in response to a read physical memory 32-bit
    //      state manipulation message. Its function is to read physical memory
    //      and return.
    //
    //  Arguments:
    //      m - Supplies a pointer to the state manipulation message.
    //      AdditionalData - Supplies a pointer to a descriptor for the data to read.
    //      Context - Supplies a pointer to the current context.
{
    UINT32 Length;
    STRING MessageHeader;

    //
    // Trim the transfer count to fit in a single message.
    //

    Length = m->ReadMemory.TransferCount;
    if (Length > (PACKET_MAX_SIZE - sizeof(DBGKD_MANIPULATE_STATE64))) {
        Length = PACKET_MAX_SIZE - sizeof(DBGKD_MANIPULATE_STATE64);
    }

    m->ReturnStatus =
        KdpCopyMemoryChunks((UINT64)(ULONG_PTR)m->ReadMemory.TargetBaseAddress,
                            AdditionalData->Buffer,
                            Length,
                            0,
                            MMDBG_COPY_UNSAFE | MMDBG_COPY_PHYSICAL,
                            &Length);

    //
    // Set the actual number of bytes read, initialize the message header,
    // and send the reply packet to the host debugger.
    //

    AdditionalData->Length = (UINT16)Length;
    m->ReadMemory.ActualBytesRead = Length;

    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 AdditionalData,
                 &KdpContext);

    return;
}

static
void
KdpWritePhysicalMemory(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData
    )
    //  Routine Description:
    //      This function is called in response of a write physical memory 32-bit
    //      state manipulation message. Its function is to write physical memory
    //      and return.
    //
    //  Arguments:
    //      m - Supplies a pointer to the state manipulation message.
    //      AdditionalData - Supplies a pointer to a descriptor for the data to write.
    //      Context - Supplies a pointer to the current context.
{
    STRING MessageHeader;

    //
    // Move the data to the destination buffer.
    //

    m->ReturnStatus =
        KdpCopyMemoryChunks((UINT64)(ULONG_PTR)m->WriteMemory.TargetBaseAddress,
                            AdditionalData->Buffer,
                            AdditionalData->Length,
                            0,
                            MMDBG_COPY_WRITE | MMDBG_COPY_UNSAFE | MMDBG_COPY_PHYSICAL,
                            &m->WriteMemory.ActualBytesWritten);

    //
    // Set the actual number of bytes written, initialize the message header,
    // and send the reply packet to the host debugger.
    //

    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 NULL,
                 &KdpContext);

    return;
}

static
void
KdpReadMachineSpecificRegister(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext *Context
    )
    //  Routine Description:
    //      This function is called in response of a write physical memory 32-bit
    //      state manipulation message. Its function is to write physical memory
    //      and return.
    //
    //  Arguments:
    //      m - Supplies a pointer to the state manipulation message.
    //      AdditionalData - Supplies a pointer to a descriptor for the data to write.
    //      Context - Supplies a pointer to the current context.
{
    STRING MessageHeader;

    //
    // Read the MSR
    //
    m->ReturnStatus = KdpReadMsr(m->ReadWriteMsr.Msr,
                                 &m->ReadWriteMsr.DataValueLow,
                                 &m->ReadWriteMsr.DataValueHigh)
        ? STATUS_SUCCESS : STATUS_UNSUCCESSFUL;

    //
    // Set the actual number of bytes written, initialize the message header,
    // and send the reply packet to the host debugger.
    //

    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 NULL,
                 &KdpContext);
}

static
void
KdpWriteMachineSpecificRegister(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext *Context
    )
    //  Routine Description:
    //      This function is called in response of a write physical memory 32-bit
    //      state manipulation message. Its function is to write physical memory
    //      and return.
    //
    //  Arguments:
    //      m - Supplies a pointer to the state manipulation message.
    //      AdditionalData - Supplies a pointer to a descriptor for the data to write.
    //      Context - Supplies a pointer to the current context.
{
    STRING MessageHeader;

    //
    // Write the MSR
    //
    m->ReturnStatus = KdpWriteMsr(m->ReadWriteMsr.Msr,
                                  m->ReadWriteMsr.DataValueLow,
                                  m->ReadWriteMsr.DataValueHigh)
        ? STATUS_SUCCESS : STATUS_UNSUCCESSFUL;

    //
    // Set the actual number of bytes written, initialize the message header,
    // and send the reply packet to the host debugger.
    //

    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 NULL,
                 &KdpContext);

    return;
}

static int wcslen(WCHAR *pwz)
{
    int len = 0;

    while (*pwz++) {
        len++;
    }
    return len;
}

static WCHAR * trim(WCHAR *pwz)
{
    WCHAR *pwzBeg = pwz;
    for (; *pwz; pwz++) {
        if (*pwz == '\\') {
            pwzBeg = pwz + 1;
        }
    }
    return pwzBeg;
}

KLDR_DATA_TABLE_ENTRY_WITH_NAME KernelEntry;
KLDR_DATA_TABLE_ENTRY_WITH_NAME HalEntry;

static void KdpFakeOutPsLoadedModuleList(Class_Microsoft_Singularity_Hal_Platform *platform)
{
    //
    //  If the debug information has not been filled in by the loader
    //  we need to reconstruct the loader list from the bootinfo data,
    //  including the hal and the kernel modules
    //
    KdVersionBlock.PsLoadedModuleList = SIGN_EXTEND(&PsLoadedModuleList);
    KdVersionBlock.KernBase = SIGN_EXTEND(platform->KernelDllBase);

    KernelEntry.DllBase = (void *) platform->KernelDllBase;
    KernelEntry.CheckSum = 0;
    KernelEntry.TimeDateStamp = 0;
    KernelEntry.LoadCount = 1;
    KernelEntry.SizeOfImage = (uint32)platform->KernelDllSize;

#if ISA_IX86
    memcpy(KernelEntry.wzName, L"kernel.x86", sizeof(KernelEntry.wzName));
#elif ISA_IX64
    memcpy(KernelEntry.wzName, L"kernel.x64", sizeof(KernelEntry.wzName));
#elif ISA_ARM
    memcpy(KernelEntry.wzName, L"kernel.arm", sizeof(KernelEntry.wzName));
#endif

    RtlInitUnicodeString(&KernelEntry.BaseDllName, KernelEntry.wzName, 20);
    RtlInitUnicodeString(&KernelEntry.FullDllName, KernelEntry.wzName, 20);

    InitializeListHead(&PsLoadedModuleList);
    InsertTailList(&PsLoadedModuleList, &KernelEntry.InLoadOrderLinks);
}

void
KdpSysGetVersion(
    PDBGKD_GET_VERSION64 Version
    )
    //  Routine Description:
    //      This function returns to the caller a general information packet
    //      that contains useful information to a debugger.  This packet is also
    //      used for a debugger to determine if the writebreakpointex and
    //      readbreakpointex APIs are available.
    //
    //  Arguments:
    //      Version - Supplies the structure to fill in
{
    *Version = KdVersionBlock;
}


static
void
KdpGetVersion(
    IN PDBGKD_MANIPULATE_STATE64 m
    )
    //  Routine Description:
    //      This function returns to the caller a general information packet
    //      that contains useful information to a debugger.  This packet is also
    //      used for a debugger to determine if the writebreakpointex and
    //      readbreakpointex APIs are available.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
{
    STRING messageHeader;

    messageHeader.Length = sizeof(*m);
    messageHeader.Buffer = (PCHAR)m;

    KdpSysGetVersion(&m->GetVersion64);

    //
    // the usual stuff
    //
    m->ReturnStatus = STATUS_SUCCESS;
    m->ApiNumber = DbgKdGetVersionApi;

    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &messageHeader,
                 NULL,
                 &KdpContext
                 );

    return;
} // KdGetVersion

static inline UINT32 min(UINT32 a, UINT32 b)
{
    return a < b ? a : b;
}

static
void
KdpReadControlSpace(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext * Context
    )
    //  Routine Description:
    //      This function is called in response of a read control space state
    //      manipulation message.  Its function is to read implementation
    //      specific system data.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    PDBGKD_READ_MEMORY64 a = &m->ReadMemory;
    STRING MessageHeader;
    PVOID Source = NULL;
    UINT32 Length = 0;
    UINT32 Actual = 0;
    UINT32 Isa = (UINT32)a->TargetBaseAddress;

    MessageHeader.Length = sizeof(*m);
    MessageHeader.Buffer = (PCHAR)m;

    ASSERT(AdditionalData->Length == 0);

    KDDBG2(" rctl base=%x, len=%x\n", Isa, a->TransferCount);

    if (m->Processor < (UINT32)KeNumberProcessors) {
        PKPROCESSOR_STATE ProcessorState = &KdpProcessorState[m->Processor];

        switch (Isa) {
            case X86_DEBUG_CONTROL_SPACE_KSPECIAL:
            case DEBUG_CONTROL_SPACE_KSPECIAL:
                KdpReadSpecialRegisters(&ProcessorState->SpecialRegisters, Context);
                Source = &ProcessorState->SpecialRegisters;
                Length = sizeof(ProcessorState->SpecialRegisters);
                break;
        }

        if (Source != NULL) {
            if (Length > a->TransferCount) {
                Length = a->TransferCount;
            }
            m->ReturnStatus = KdpCopyToPtr(AdditionalData->Buffer, Source, Length, &Actual);

            KDDBG2(" rctl: copy src=%p, len=%x, Actual=%x, return status=%x\n",
                  Source, Length, Actual, m->ReturnStatus);
        }
    }
    else {
        KDDBG("ReadControl: proc %d unknown control type (%d)\n", m->Processor, Isa);
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
    }

    AdditionalData->Length = (UINT16)Actual;
    a->ActualBytesRead = Actual;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE, &MessageHeader, AdditionalData, &KdpContext);
}

static
void
KdpWriteControlSpace(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext * Context
    )
    //  Routine Description:
    //      This function is called in response of a write control space state
    //      manipulation message.  Its function is to write implementation
    //      specific system data.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    PDBGKD_WRITE_MEMORY64 a = &m->WriteMemory;
    STRING MessageHeader;
    PVOID Dest = NULL;      // Pointer to bytes available to target.
    UINT32 Length = 0;      // # of bytes available to target.
    UINT32 Isa = (UINT32)a->TargetBaseAddress;
    PKPROCESSOR_STATE ProcessorState = NULL;

    MessageHeader.Length = sizeof(*m);
    MessageHeader.Buffer = (PCHAR)m;

    KDDBG2(" wctl base=%x, len=%x\n", Isa, a->TransferCount);

    if (m->Processor < (UINT32)KeNumberProcessors) {
        ProcessorState = &KdpProcessorState[m->Processor];

        switch (Isa) {
            case X86_DEBUG_CONTROL_SPACE_KSPECIAL:
            case DEBUG_CONTROL_SPACE_KSPECIAL:
                Dest = &ProcessorState->SpecialRegisters;
                Length = sizeof(ProcessorState->SpecialRegisters);
                break;
        }
    }

    UINT32 Actual = 0;
    if (Dest != NULL) {
        if (Length > a->TransferCount) {
            Length = a->TransferCount;
        }

        m->ReturnStatus = KdpCopyToPtr(Dest, AdditionalData->Buffer, Length, &Actual);

        switch (Isa) {
            case X86_DEBUG_CONTROL_SPACE_KSPECIAL:
            case DEBUG_CONTROL_SPACE_KSPECIAL:
                KdpWriteSpecialRegisters(&ProcessorState->SpecialRegisters);
                break;
        }

        KDDBG2(" wctl: copy dst=%p, len=%x, Actual=%x, return status=%x\n",
              Dest, Length, Actual, m->ReturnStatus);
    }
    else {
        KDDBG("WriteControl: proc %d unknown control type (%d)\n",
              m->Processor, Isa);
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
    }

    a->ActualBytesWritten = Actual;
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE, &MessageHeader, AdditionalData, &KdpContext);
}

static
void
KdpReadIoSpace(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext * x86Context
    )
    //  Routine Description:
    //      This function is called in response of a read I/O space
    //      manipulation message.  Its function is to read the x86 processors
    //      I/O space and return the result.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    PDBGKD_READ_WRITE_IO64 a = &m->ReadWriteIo;
    STRING MessageHeader;
    UINT16 Target = (UINT16)a->IoAddress;

    ASSERT(AdditionalData->Length == 0);

    KDDBG(" read io base=%x, len=%x\n", Target, a->DataSize, AdditionalData->Buffer);

    //
    // Zero-fill the entire value so that shorter reads
    // do not leave unset bytes.
    //
    a->DataValue = 0;

    m->ReturnStatus = STATUS_SUCCESS;

    switch (a->DataSize) {
    case 1:
        a->DataValue = KdpReadWriteIoSpace(a->DataSize, 0, Target, 0);
        break;

    case 2:
        a->DataValue = KdpReadWriteIoSpace(a->DataSize, 0, Target, 0);
        break;

    case 4:
        a->DataValue = KdpReadWriteIoSpace(a->DataSize, 0, Target, 0);
        break;

    default:
        KDDBG("ReadIoSpace: Unrecognized size (%d)\n", a->DataSize);
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
        break;
    }

    //
    // Send the response
    //
    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;

    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE, &MessageHeader, NULL, &KdpContext);
}

static
void
KdpWriteIoSpace(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext * x86Context
    )
    //  Routine Description:
    //      This function is called in response of a write I/O space
    //      manipulation message.  Its function is to write the x86 processors
    //      I/O space.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    PDBGKD_READ_WRITE_IO64 a = &m->ReadWriteIo;
    STRING MessageHeader;
    UINT16 Target = (UINT16)a->IoAddress;

    ASSERT(AdditionalData->Length == 0);

    KDDBG(" write io base=%x, len=%x, value=%x\n", Target, a->DataSize, a->DataValue);

    m->ReturnStatus = STATUS_SUCCESS;

    switch (a->DataSize) {
    case 1:
        KdpReadWriteIoSpace(a->DataSize, 1, Target, a->DataValue & 0x000000FF);
        break;

    case 2:
        KdpReadWriteIoSpace(a->DataSize, 1, Target, a->DataValue & 0x0000FFFF);
        break;

    case 4:
        KdpReadWriteIoSpace(a->DataSize, 1, Target, a->DataValue);
        break;

    default:
        KDDBG("WriteIoSpace: Unrecognized size (%d)\n", a->DataSize);
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
        break;
    }

    // Send the reply
    MessageHeader.Length = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)m;

    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE, &MessageHeader, NULL, &KdpContext);
}

static
void
KdpSetContext(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext * Context
    )
    //  Routine Description:
    //      This function is called in response of a set context state
    //      manipulation message.  Its function is set the current
    //      context.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    STRING MessageHeader;

    MessageHeader.Length = sizeof(*m);
    MessageHeader.Buffer = (PCHAR)m;

    ASSERT(AdditionalData->Length == sizeof(CONTEXT));

    if ((m->Processor >= (UINT16)KeNumberProcessors) || (KdpContextSent == FALSE)) {
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
    }
    else {
        m->ReturnStatus = STATUS_SUCCESS;
        KdpFromKdContext((CONTEXT*)AdditionalData->Buffer, Context);
    }

    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 NULL,
                 &KdpContext);
}

static
void
KdpGetContext(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData,
    IN Struct_Microsoft_Singularity_Isal_SpillContext *Context
    )
    //  Routine Description:
    //      This function is called in response of a get context state
    //      manipulation message.  Its function is to return the current
    //      context.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    STRING MessageHeader;

    MessageHeader.Length = sizeof(*m);
    MessageHeader.Buffer = (PCHAR)m;

    ASSERT(AdditionalData->Length == 0);

    if (m->Processor >= (UINT16)KeNumberProcessors) {
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
    }
    else {
        m->ReturnStatus = STATUS_SUCCESS;
        AdditionalData->Length = sizeof(CONTEXT);

        RtlZeroMemory(AdditionalData->Buffer, AdditionalData->Length);
        KdpToKdContext(Context, (CONTEXT*)AdditionalData->Buffer);
        KdpContextSent = TRUE;
    }

    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 AdditionalData,
                 &KdpContext);
}


UINT32
KdpAddBreakpoint(
    IN PVOID Address
    )
    //  Routine Description:
    //      This routine adds an entry to the breakpoint table and returns a handle
    //      to the breakpoint table entry.
    //
    //  Arguments:
    //      Address - Supplies the address where to set the breakpoint.
    //
    //  Return Value:
    //
    //      A value of zero is returned if the specified address is already in the
    //      breakpoint table, there are no free entries in the breakpoint table, the
    //      specified address is not correctly aligned, or the specified address is
    //      not valid. Otherwise, the index of the assigned breakpoint table entry
    //      plus one is returned as the function value.
{
    UINT32 Index;
    KDP_BREAKPOINT_TYPE Content;
    BOOL Accessible;

    KDDBG2("KdpAddBreakpoint(%p)\n", Address);

    for (Index = 0; Index < BREAKPOINT_TABLE_SIZE; Index++) {
        if (KdpBreakpointTable[Index].Flags == 0) {
            break;
        }
    }
    if (Index == BREAKPOINT_TABLE_SIZE) {
        KDDBG("KD: ran out of breakpoints!\n");
        return 0;
    }

    Accessible = NT_SUCCESS(KdpCopyFromPtr(&Content,
                                           Address,
                                           sizeof(KDP_BREAKPOINT_TYPE),
                                           NULL));
    KDDBG("KD: memory %saccessible\n", Accessible ? "" : "in");

    if (Accessible) {
        KdpBreakpointTable[Index].Address = Address;
        KdpBreakpointTable[Index].Content = Content;
        KdpBreakpointTable[Index].Flags = KD_BREAKPOINT_IN_USE;

        if (!NT_SUCCESS(KdpCopyToPtr(Address,
                                     &KdpBreakpointInstruction,
                                     sizeof(KDP_BREAKPOINT_TYPE),
                                     NULL))) {
            KDDBG("KD: Unable to write BP!\n");
        }
    }
    else {
        return 0;
    }

    return Index+1;
}

BOOLEAN
KdpDeleteBreakpoint(
    IN UINT32 Handle
    )
{
    UINT32 Index = Handle - 1;
    KDDBG2("KD: Delete Breakpoint %d\n", Handle);

    if ((Handle == 0) || (Handle > BREAKPOINT_TABLE_SIZE)) {
        KDDBG("KD: Breakpoint %d invalid.\n", Index);
        return FALSE;
    }

    //
    // Replace the instruction contents.
    //
    if (!NT_SUCCESS(KdpCopyToPtr(KdpBreakpointTable[Index].Address,
                                 &KdpBreakpointTable[Index].Content,
                                 sizeof(KDP_BREAKPOINT_TYPE),
                                 NULL))) {
        KDDBG("KD: Breakpoint at 0x%p; unable to clear, flag set.\n",
                  KdpBreakpointTable[Index].Address);
        return FALSE;
    }
    else {
        KDDBG2("KD: Breakpoint at 0x%p cleared.\n",
               KdpBreakpointTable[Index].Address);
        KdpBreakpointTable[Index].Flags = 0;
    }
    return TRUE;
}

void
KdpWriteBreakpoint(
    IN PDBGKD_MANIPULATE_STATE64 m
    )
    //  Routine Description:
    //      This function is called in response of a write breakpoint state
    //      manipulation message.  Its function is to write a breakpoint
    //      and return a handle to the breakpoint.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    PDBGKD_WRITE_BREAKPOINT64 a = &m->WriteBreakPoint;
    STRING MessageHeader;

    MessageHeader.Length = sizeof(*m);
    MessageHeader.Buffer = (PCHAR)m;

    ASSERT(AdditionalData->Length == 0);

    a->BreakPointHandle = KdpAddBreakpoint((PVOID)(ULONG_PTR)a->BreakPointAddress);
    if (a->BreakPointHandle != 0) {
        m->ReturnStatus = STATUS_SUCCESS;
    }
    else {
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
    }
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 NULL,
                 &KdpContext);
}

void
KdpRestoreBreakpoint(
    IN PDBGKD_MANIPULATE_STATE64 m,
    IN PSTRING AdditionalData
    )
    //  Routine Description:
    //      This function is called in response of a restore breakpoint state
    //      manipulation message.  Its function is to restore a breakpoint
    //      using the specified handle.
    //
    //  Arguments:
    //      m - Supplies the state manipulation message.
    //      AdditionalData - Supplies any additional data for the message.
    //      Context - Supplies the current context.
{
    PDBGKD_RESTORE_BREAKPOINT a = &m->RestoreBreakPoint;
    STRING MessageHeader;

    MessageHeader.Length = sizeof(*m);
    MessageHeader.Buffer = (PCHAR)m;

    ASSERT(AdditionalData->Length == 0);
    if (KdpDeleteBreakpoint(a->BreakPointHandle)) {
        m->ReturnStatus = STATUS_SUCCESS;
    }
    else {
        m->ReturnStatus = STATUS_UNSUCCESSFUL;
    }
    KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE,
                 &MessageHeader,
                 NULL,
                 &KdpContext);
}

static
void
KdpGetStateChange(
    IN PDBGKD_MANIPULATE_STATE64 ManipulateState,
    IN Struct_Microsoft_Singularity_Isal_SpillContext *Context
    )
    //  Routine Description:
    //      Extract continuation control data from Manipulate_State message
    //
    //  Arguments:
    //      ManipulateState - supplies pointer to Manipulate_State packet
    //      Context - Supplies a pointer to a context record.
{
    if (NT_SUCCESS(ManipulateState->Continue2.ContinueStatus)) {
        //
        // If NT_SUCCESS returns TRUE, then the debugger is doing a
        // continue, and it makes sense to apply control changes.
        // Otherwise the debugger is saying that it doesn't know what
        // to do with this exception, so control values are ignored.
        //

        KdpSetControlSet(&ManipulateState->Continue2.ControlSet, Context);

#if 0
        for (Processor = 0; Processor < (UINT32)KeNumberProcessors; Processor++) {
            Prcb = KiProcessorBlock[Processor];

            Prcb->ProcessorState.SpecialRegisters.KernelDr7 =
                ManipulateState->Continue2.ControlSet.Dr7;

            Prcb->ProcessorState.SpecialRegisters.KernelDr6 = 0L;
        }
        if (ManipulateState->Continue2.ControlSet.CurrentSymbolStart != 1) {
            KdpCurrentSymbolStart = ManipulateState->Continue2.ControlSet.CurrentSymbolStart;
            KdpCurrentSymbolEnd = ManipulateState->Continue2.ControlSet.CurrentSymbolEnd;
        }
#endif
    }
}

KCONTINUE_STATUS
KdpSendWaitContinue(
    IN UINT32 OutPacketType,
    IN PSTRING OutMessageHeader,
    IN PSTRING OutMessageData OPTIONAL,
    IN OUT Struct_Microsoft_Singularity_Isal_SpillContext *Context
    )
    //  Routine Description:
    //      This function sends a packet, and then waits for a continue message.
    //      BreakIns received while waiting will always cause a resend of the
    //      packet originally sent out.  While waiting, manipulate messages
    //      will be serviced.
    //      A resend always resends the original event sent to the debugger,
    //      not the last response to some debugger command.
    //
    //  Arguments:
    //      OutPacketType - Supplies the type of packet to send.
    //      OutMessageHeader - Supplies a pointer to a string descriptor that describes
    //          the message information.
    //      OutMessageData - Supplies a pointer to a string descriptor that describes
    //          the optional message data.
    //      x86Record - Exception context
    //
    //  Return Value:
    //      A value of TRUE is returned if the continue message indicates
    //      success, Otherwise, a value of FALSE is returned.
{

    UINT32 Length;
    STRING MessageData;
    STRING MessageHeader;
    DBGKD_MANIPULATE_STATE64 ManipulateState;
    UINT32 ReturnCode;
    //    NTSTATUS Status;
    //    KCONTINUE_STATUS ContinueStatus;

    //
    // Loop servicing state manipulation message until a continue message
    // is received.
    //

    MessageHeader.MaximumLength = sizeof(DBGKD_MANIPULATE_STATE64);
    MessageHeader.Buffer = (PCHAR)&ManipulateState;
    MessageData.MaximumLength = arrayof(KdpMessageBuffer);
    MessageData.Buffer = KdpMessageBuffer;
    KdpContextSent = FALSE;

  ResendPacket:

    //
    // Send event notification packet to debugger on host.  Come back
    // here any time we see a breakin sequence.
    //

    KdSendPacket(OutPacketType,
                 OutMessageHeader,
                 OutMessageData,
                 &KdpContext);

    //
    // After sending packet, if there is no response from debugger
    // AND the packet is for reporting symbol (un)load, the debugger
    // will be declared to be not present.  Note If the packet is for
    // reporting exception, the KdSendPacket will never stop.
    //

    if (KdDebuggerNotPresent) {
        return ContinueSuccess;
    }

    for (;;) {
        //
        // Wait for State Manipulate Packet without timeout.
        //

        do {
            ReturnCode = KdReceivePacket(
                                         PACKET_TYPE_KD_STATE_MANIPULATE,
                                         &MessageHeader,
                                         &MessageData,
                                         &Length,
                                         &KdpContext
                                        );
            KDDBG3("KdReceivePacket returned %d\n", ReturnCode);
            if (ReturnCode == KDP_PACKET_RESEND) {
                goto ResendPacket;
            }
        } while (ReturnCode == KDP_PACKET_TIMEOUT);

        KDDBG2("KdpSendWaitContinue: ManipulateState.ApiNumber=0x%x\n", ManipulateState.ApiNumber);

        //
        // Switch on the return message API number.
        //

        switch (ManipulateState.ApiNumber) {

          case DbgKdReadVirtualMemoryApi:
            KDDBG("KdReadVirt(%p-%p)\n",
                  (ULONG_PTR)ManipulateState.ReadMemory.TargetBaseAddress,
                  (ULONG_PTR)ManipulateState.ReadMemory.TargetBaseAddress +
                  ManipulateState.ReadMemory.TransferCount);
            KdpReadVirtualMemory(&ManipulateState, &MessageData);
            break;

#if 0
          case DbgKdReadVirtualMemory64Api:
            KdpReadVirtualMemory64(&ManipulateState, &MessageData);
            break;
#endif
          case DbgKdWriteVirtualMemoryApi:
            KDDBG("KdWritVirt(%p-%p)\n",
                  (ULONG_PTR)ManipulateState.WriteMemory.TargetBaseAddress,
                  (ULONG_PTR)ManipulateState.WriteMemory.TargetBaseAddress +
                  ManipulateState.WriteMemory.TransferCount);
            KdpWriteVirtualMemory(&ManipulateState, &MessageData);
            break;
#if 0
          case DbgKdWriteVirtualMemory64Api:
            KdpWriteVirtualMemory64(&ManipulateState, &MessageData);
            break;
#endif
          case DbgKdGetVersionApi:
            KDDBG("KdGetVersion()\n");
            KdpGetVersion(&ManipulateState);
            break;

          case DbgKdGetContextApi:
            KDDBG("KdGetContext(p=%x)\n", ManipulateState.Processor);
            KdpGetContext(&ManipulateState, &MessageData, Context);
            break;

          case DbgKdReadControlSpaceApi:
            KDDBG("KdReadCtrl(%p-%p p=%x)\n",
                  (ULONG_PTR)ManipulateState.ReadMemory.TargetBaseAddress,
                  (ULONG_PTR)ManipulateState.ReadMemory.TargetBaseAddress +
                  ManipulateState.ReadMemory.TransferCount,
                  (ULONG_PTR)ManipulateState.Processor);
            KdpReadControlSpace(&ManipulateState, &MessageData, Context);
            break;

          case DbgKdWriteControlSpaceApi:
            KDDBG("KdWriteCtrl(%p-%p p=%x)\n",
                  (ULONG_PTR)ManipulateState.WriteMemory.TargetBaseAddress,
                  (ULONG_PTR)ManipulateState.WriteMemory.TargetBaseAddress +
                  ManipulateState.WriteMemory.TransferCount,
                  (ULONG_PTR)ManipulateState.Processor);
            KdpWriteControlSpace(&ManipulateState, &MessageData, Context);
            break;

        case DbgKdReadIoSpaceApi:
            KDDBG("KdReadIoSpace(%p size=%x p=%x)\n",
                  (ULONG_PTR)ManipulateState.ReadWriteIo.IoAddress,
                  (ULONG_PTR)ManipulateState.ReadWriteIo.DataSize,
                  (ULONG_PTR)ManipulateState.Processor);
            KdpReadIoSpace(&ManipulateState, &MessageData, Context);
            break;

        case DbgKdWriteIoSpaceApi:
            KDDBG("KdWriteIoSpace(%p size=%x value=%x, p=%x)\n",
                  (ULONG_PTR)ManipulateState.ReadWriteIo.IoAddress,
                  (ULONG_PTR)ManipulateState.ReadWriteIo.DataSize,
                  (ULONG_PTR)ManipulateState.ReadWriteIo.DataValue,
                  (ULONG_PTR)ManipulateState.Processor);
            KdpWriteIoSpace(&ManipulateState, &MessageData, Context);
            break;

          case DbgKdSetContextApi:
            KDDBG("KdSetContext(p=%x)\n", ManipulateState.Processor);
            KdpSetContext(&ManipulateState, &MessageData, Context);
            break;

          case DbgKdWriteBreakPointApi:
            KDDBG("KdWriteBreak(%p)\n",
                  ManipulateState.WriteBreakPoint.BreakPointAddress);
            KdpWriteBreakpoint(&ManipulateState);
            break;

          case DbgKdRestoreBreakPointApi:
            if (ManipulateState.RestoreBreakPoint.BreakPointHandle < 0x8 ||
                ManipulateState.RestoreBreakPoint.BreakPointHandle > 0x1e) {
                KDDBG("KdRestoreBreak(%x)\n",
                      ManipulateState.RestoreBreakPoint.BreakPointHandle);
            }
            KdpRestoreBreakpoint(&ManipulateState, &MessageData);
            break;

          case DbgKdContinueApi:
            KDDBG("KdContinue(%08x)\n",
                  ManipulateState.Continue.ContinueStatus);
            if (NT_SUCCESS(ManipulateState.Continue.ContinueStatus)) {
                return ContinueSuccess;
            }
            else {
                return ContinueError;
            }
            break;

          case DbgKdContinueApi2:
            KDDBG("KdContinue2(%08x)\n",
                  ManipulateState.Continue2.ContinueStatus);
            if (NT_SUCCESS(ManipulateState.Continue2.ContinueStatus)) {
                KDDBG("KdpGetStateChange()\n");
                KdpGetStateChange(&ManipulateState, Context);
                return ContinueSuccess;
            }
            else {
                KDDBG("KdpContinue2 Error!\n");
                return ContinueError;
            }
            break;

          case DbgKdReadPhysicalMemoryApi:
            KDDBG("KdReadPhys(%8p-%8p)\n",
                  (ULONG_PTR)ManipulateState.ReadMemory.TargetBaseAddress,
                  (ULONG_PTR)ManipulateState.ReadMemory.TargetBaseAddress +
                  ManipulateState.ReadMemory.TransferCount);
            // KdpReadPhysicalMemory(&ManipulateState, &MessageData, Context);
            KdpReadPhysicalMemory(&ManipulateState, &MessageData);
            break;

          case DbgKdWritePhysicalMemoryApi:
            KdpWritePhysicalMemory(&ManipulateState, &MessageData);
            KDDBG("KdWritePhys(%8p-%8p)\n",
                  (ULONG_PTR)ManipulateState.WriteMemory.TargetBaseAddress,
                  (ULONG_PTR)ManipulateState.WriteMemory.TargetBaseAddress +
                  ManipulateState.ReadMemory.TransferCount);
            break;

          case DbgKdSwitchProcessor:
              {
                  // KdRestore(FALSE);
                  bool switched = Class_Microsoft_Singularity_MpExecution::g_SwitchFrozenProcessor((int32) ManipulateState.Processor);
                  return (switched == true) ? ContinueNextProcessor : ContinueSuccess;
                  // KdSave(FALSE);
              }
            break;

          case DbgKdReadMachineSpecificRegister:
            KdpReadMachineSpecificRegister(&ManipulateState, &MessageData, Context);
            break;

          case DbgKdWriteMachineSpecificRegister:
            KdpWriteMachineSpecificRegister(&ManipulateState, &MessageData, Context);
            break;

          default:
            KDDBG2("Kd Bad API (0x%x)\n", ManipulateState.ApiNumber);
            MessageData.Length = 0;
            ManipulateState.ReturnStatus = STATUS_UNSUCCESSFUL;
            KdSendPacket(PACKET_TYPE_KD_STATE_MANIPULATE, &MessageHeader, &MessageData, &KdpContext);
            break;
        }
    }
}
//
//////////////////////////////////////////////////////////////////////////////

BOOLEAN
KdPrintString(
    IN PSTRING Output,
    IN BOOLEAN Unicode
    )
    //  Routine Description:
    //      This routine prints a string.
    //
    //  Arguments:
    //      Output - Supplies a pointer to a string descriptor for the output string.
    //
    //  Return Value:
    //      TRUE if Control-C present in input buffer after print is done.
    //      FALSE otherwise.
{

    UINT32 Length;
    STRING MessageData;
    STRING MessageHeader;
    DBGKD_DEBUG_IO DebugIo;

    if (KdDebuggerNotPresent) {
        return FALSE;
    }
    KdpLock();

    // Move the output string to the message buffer.
    //
    if (Unicode) {
        WCHAR *pBuffer = (WCHAR *)Output->Buffer;
        for (int i = 0; i < Output->Length; i++) {
            KdpMessageBuffer[i] = (char)pBuffer[i];
        }
        Length = Output->Length;
    }
    else {
        KdpCopyFromPtr(KdpMessageBuffer,
                       Output->Buffer,
                       Output->Length,
                       &Length);
    }

    // If the total message length is greater than the maximum packet size,
    // then truncate the output string.
    //
    if ((sizeof(DBGKD_DEBUG_IO) + Length) > PACKET_MAX_SIZE) {
        Length = PACKET_MAX_SIZE - sizeof(DBGKD_DEBUG_IO);
    }

    // Construct the print string message and message descriptor.
    //
    DebugIo.ApiNumber = DbgKdPrintStringApi;
    DebugIo.ProcessorLevel = KeProcessorLevel;
    DebugIo.Processor = (UINT16)KdpGetCurrentProcessorNumber();
    DebugIo.PrintString.LengthOfString = Length;
    MessageHeader.Length = sizeof(DBGKD_DEBUG_IO);
    MessageHeader.Buffer = (PCHAR)&DebugIo;

    // Construct the print string data and data descriptor.
    //
    MessageData.Length = (UINT16)Length;
    MessageData.Buffer = (PCHAR) KdpMessageBuffer;

    // Send packet to the kernel debugger on the host machine.
    //
    KdSendPacket(PACKET_TYPE_KD_DEBUG_IO,
                 &MessageHeader,
                 &MessageData,
                 &KdpContext);

    KdpUnlock();

    return FALSE;
}

/////////////////////////////////////////////////////// Methods Exposed to C#.
//
bool Class_Microsoft_Singularity_DebugStub::
g_Trap(Struct_Microsoft_Singularity_Isal_SpillContext *context, int id)
{
    EXCEPTION_RECORD64 er;
    bool handled;
    RtlZeroMemory(&er, sizeof(er));

    if (KdDebuggerNotPresent) {
        return true;
    }

    KdpLock();

    KDDBG("CPU %d: In g_Trap num=%d ...", KdCurrentCpuId(), id);

    KdDebugTrapData * trapData = KdpIsDebugTrap(context, id);

    if (trapData != NULL) {
        if (trapData->tag == KdDebugTrapData::LOADED_BINARY) {
            KDDBG("KD: Loaded binary %ls\n", trapData->loadedBinary.name);
            KdpUnlock();
            LoadedBinary(trapData, context);
            return true;
        }
        else if (trapData->tag == KdDebugTrapData::UNLOADED_BINARY) {
            KDDBG("KD: Unloaded binary\n");
            KdpUnlock();
            UnloadedBinary(trapData, context);
            return true;
        }
    }

    KdpConvertTrapToException(&er, context, id);

    KdpEnter();

    handled = (KdpReportExceptionStateChange(&er, context, trapData != NULL) == ContinueSuccess);

    KdpLeave();

    KdpUnlock();

    return handled;
}

bool Class_Microsoft_Singularity_DebugStub::
g_TrapForProcessorSwitch(Struct_Microsoft_Singularity_Isal_SpillContext *context)
{
    EXCEPTION_RECORD64 er;

    KDDBG("CPU %d: TrapForProcessorSwitch:\n", KdCurrentCpuId());

    RtlZeroMemory(&er, sizeof(er));
    er.ExceptionCode    = STATUS_WAKE_SYSTEM_DEBUGGER;
    er.ExceptionRecord  = (UINT64)&er;

#if ISA_IX86 || ISA_IX64
    er.ExceptionAddress = context->ip;
#elif ISA_ARM
    er.ExceptionAddress = context->pc;
#endif

    // KdSave(FALSE);
    KCONTINUE_STATUS status = KdpReportExceptionStateChange(&er, context, true);
    // KdRestore(FALSE);
    return status == ContinueSuccess;
}

void Class_Microsoft_Singularity_DebugStub::g_AddProcessor(int cpuId)
{
    KdpLock();
    if (KeNumberProcessors <= cpuId) {
        KeNumberProcessors = cpuId + 1;
    }
    KdpUnlock();
}

bool Class_Microsoft_Singularity_DebugStub::g_PollForBreak()
{
    // Don't re-enter debugger if already debugging.
    if (KdpInDebugger) {
        return FALSE;
    }

    // If the debugger is enabled, see if a breakin by the kernel
    // debugger is pending.
    // We might want to enable retry here.  The transports support it.
    if (KdDebuggerNotPresent) {
        return false;
    }

    // Did we already record a break from the host?
    if (KdpContext.KdpControlCPending) {
        KdpContext.KdpControlCPending = FALSE;
        return true;
    }

    KdpLock();
    bool success = KdPollBreakIn();
    KdpUnlock();

    return success;
}

bool Class_Microsoft_Singularity_DebugStub::g_LoadedBinary(UIntPtr baseAddress,
                                                           UIntPtr bytes,
                                                           Class_System_String *name,
                                                           uint32 checksum,
                                                           uint32 timestamp,
                                                           bool silent)
{
    return g_LoadedBinary(baseAddress,
                          bytes,
                          (UIntPtr)&name->m_firstChar,
                          checksum,
                          timestamp,
                          silent);
}

bool Class_Microsoft_Singularity_DebugStub::g_LoadedBinary(UIntPtr baseAddress,
                                                           UIntPtr bytes,
                                                           UIntPtr name,
                                                           uint32 checksum,
                                                           uint32 timestamp,
                                                           bool silent)
{
    if (KdDebuggerNotPresent) {
        return true;
    }

    KdDebugTrapData trapData;
    trapData.tag = KdDebugTrapData::LOADED_BINARY;
    trapData.loadedBinary.baseAddress = baseAddress;
    trapData.loadedBinary.bytes = bytes;
    trapData.loadedBinary.name = name;
    trapData.loadedBinary.checksum = checksum;
    trapData.loadedBinary.timestamp = timestamp;
    trapData.loadedBinary.silent = silent;
    KdNotifyTrap(&trapData);

    return trapData.loadedBinary.ret;
}

static void LoadedBinary(KdDebugTrapData *trapData,
                         Struct_Microsoft_Singularity_Isal_SpillContext *context)
{
    UIntPtr baseAddress = trapData->loadedBinary.baseAddress;
    UIntPtr bytes = trapData->loadedBinary.bytes;
    UIntPtr nameof = trapData->loadedBinary.name;
    uint32 checksum = trapData->loadedBinary.checksum;
    uint32 timestamp = trapData->loadedBinary.timestamp;
    bool silent = trapData->loadedBinary.silent;

    KLDR_DATA_TABLE_ENTRY_WITH_NAME *pEntry;
    bool good = false;
    WCHAR * name = trim((WCHAR *)nameof);
    UINT16 nlen = (UINT16)2 * wcslen(name);
    if (nlen > sizeof(pEntry->wzName)) {
        nlen = sizeof(pEntry->wzName);
    }

    KdpLock();

    for (int i = 0; i < ARRAYOF(KdModuleKernelEntry); i++) {
        pEntry = &KdModuleKernelEntry[i];

        if (pEntry->DllBase == 0) {
            pEntry->DllBase = (PVOID *)baseAddress;
            pEntry->CheckSum = checksum;
            pEntry->TimeDateStamp = timestamp;
            pEntry->LoadCount = 1;
            pEntry->SizeOfImage = (UINT32)bytes;
            memcpy(pEntry->wzName, name, nlen);
            RtlInitUnicodeString(&pEntry->FullDllName, name, nlen);
            RtlInitUnicodeString(&pEntry->BaseDllName, name, nlen);

            // We should insert in the right order in the list...
            InsertTailList(&PsLoadedModuleList, &pEntry->InLoadOrderLinks);
            good = true;
            break;
        }
    }

    if (!silent) {
        if (good) {
            KdpReportLoadSymbolsStateChange(pEntry->BaseDllName.Buffer,
                                            pEntry->BaseDllName.Length,
                                            (UINT64)baseAddress,
                                            (UINT32)0,
                                            checksum,
                                            (INT32)bytes,
                                            FALSE,
                                            context);
        }
        else {
            KdpReportLoadSymbolsStateChange(NULL,
                                            0,
                                            (UINT64)baseAddress,
                                            (UINT32)0,
                                            checksum,
                                            (INT32)bytes,
                                            FALSE,
                                            context);
        }
    }
    KdpUnlock();

    trapData->loadedBinary.ret = good;
}

bool Class_Microsoft_Singularity_DebugStub::g_UnloadedBinary(UIntPtr baseAddress,
                                                             bool silent)
{
    if (KdDebuggerNotPresent) {
        return true;
    }

    KdDebugTrapData trapData;
    trapData.tag = KdDebugTrapData::UNLOADED_BINARY;
    trapData.unloadedBinary.baseAddress = baseAddress;
    trapData.unloadedBinary.silent = silent;
    KdNotifyTrap(&trapData);

    return trapData.unloadedBinary.ret;
}

static void UnloadedBinary(KdDebugTrapData *trapData,
                           Struct_Microsoft_Singularity_Isal_SpillContext *context)
{
    UIntPtr baseAddress = trapData->unloadedBinary.baseAddress;
    bool silent = trapData->unloadedBinary.silent;
    bool good = false;

    KdpLock();
    KLDR_DATA_TABLE_ENTRY_WITH_NAME *pEntry = NULL;
    for (int i = 0; i < ARRAYOF(KdModuleKernelEntry); i++) {
        pEntry = &KdModuleKernelEntry[i];

        if (pEntry->DllBase == (PVOID*)baseAddress) {
            RemoveEntryList(&pEntry->InLoadOrderLinks);
            good = true;
            break;
        }
    }

    if (good) {
        if (!silent) {
            // Only tell debugger if we found an image name.
            // The debugger ignores unload requests that lack a processId (not us)
            // or a path name.

            KdpReportLoadSymbolsStateChange(pEntry->BaseDllName.Buffer,
                                            pEntry->BaseDllName.Length,
                                            (UINT64)baseAddress,
                                            (UINT32)0,
                                            0,
                                            0,
                                            TRUE,
                                            context);
        }
        RtlZeroMemory(pEntry, sizeof(*pEntry));
    }
    KdpUnlock();

    trapData->unloadedBinary.ret = good;
}

bool Class_Microsoft_Singularity_DebugStub::g_IsDebuggerPresent()
{
    return !KdDebuggerNotPresent;
}

//////////////////////////////////////////////////////////////////////////////
// Note: Leaves the lock held by the client code, so it had better be trustworthy.
void Class_Microsoft_Singularity_DebugStub::g_PrintBegin(WCHAR **buffer, int *length)
{
    if (KdDebuggerNotPresent && !KdAlwaysPrintOutput) {

        *buffer = NULL;
        *length = 0;
        return;
    }
    else {
        KdpLock();

        *buffer = (WCHAR *)KdpMessageBuffer;
        *length = sizeof(KdpMessageBuffer) / sizeof(WCHAR);
    }
}

// Note: Assumes the lock is held, so the client code had better be trustworthy.
void Class_Microsoft_Singularity_DebugStub::g_PrintComplete(WCHAR *buffer, int length)
{
    if (KdDebuggerNotPresent && !KdAlwaysPrintOutput) {
        return;
    }

    CHAR *out = KdpMessageBuffer;
    if (length > arrayof(KdpMessageBuffer)) {
        length = arrayof(KdpMessageBuffer);
    }

    for (int i = 0; i < length; i++) {
        *out++ = (CHAR)*buffer++;
    }

    // If the total message length is greater than the maximum packet size,
    // then truncate the output string.
    //
    if ((sizeof(DBGKD_DEBUG_IO) + length) > PACKET_MAX_SIZE) {
        length = PACKET_MAX_SIZE - sizeof(DBGKD_DEBUG_IO);
    }

    //
    // Construct the print string message and message descriptor.
    //
    DBGKD_DEBUG_IO DebugIo;
    DebugIo.ApiNumber = DbgKdPrintStringApi;
    DebugIo.ProcessorLevel = KeProcessorLevel;
    DebugIo.Processor = (UINT16)KdpGetCurrentProcessorNumber();
    DebugIo.PrintString.LengthOfString = length;

    STRING MessageHeader;
    MessageHeader.Length = sizeof(DBGKD_DEBUG_IO);
    MessageHeader.Buffer = (PCHAR)&DebugIo;

    //
    // Construct the print string data and data descriptor.
    //
    STRING MessageData;
    MessageData.Length = (UINT16)length;
    MessageData.Buffer = KdpMessageBuffer;

    //
    // Send packet to the kernel debugger on the host machine.
    //
    KdSendPacket(PACKET_TYPE_KD_DEBUG_IO,
                 &MessageHeader,
                 &MessageData,
                 &KdpContext);

    KdpUnlock();
}

void Class_Microsoft_Singularity_DebugStub::g_Print(WCHAR *buf, int len)
{
    WCHAR *buffer;
    int length;

    if (KdDebuggerNotPresent && !KdAlwaysPrintOutput) {
        return;
    }

    g_PrintBegin(&buffer, &length);
    g_PrintComplete(buf, len);
}

void Class_Microsoft_Singularity_DebugStub::g_Print(WCHAR *buf)
{
    int len = 0;

    while (buf[len] != '\0') {
        len++;
    }
    g_Print(buf, len);
}

void Class_Microsoft_Singularity_DebugStub::g_RevertToUniprocessor()
{
    KdpLock();
    KeNumberProcessors = 1;
    KdpUnlock();
}

void Class_Microsoft_Singularity_KernelDebugger_Kd::g_SendPacket(
    /*Struct_Microsoft_Singularity_KernelDebugger_KdPacketType*/ uint32 PacketType,
    uint8* MessageHeaderBuffer,
    int32 MessageHeaderLength,
    uint8* MessageDataBuffer,
    int32 MessageDataLength)
{
    ASSERT(MessageHeaderLength >= 0);
    ASSERT(MessageHeaderLength < 0x10000);
    ASSERT(MessageDataLength >= 0);
    ASSERT(MessageDataLength < 0x10000);

    STRING MessageHeaderDesc;
    MessageHeaderDesc.Buffer = (PCHAR)MessageHeaderBuffer;
    MessageHeaderDesc.Length = (uint16)MessageHeaderLength;
    MessageHeaderDesc.MaximumLength = (uint16)MessageHeaderLength;

    STRING MessageDataDesc;
    MessageDataDesc.Buffer = (PCHAR)MessageDataBuffer;
    MessageDataDesc.Length = (uint16)MessageDataLength;
    MessageDataDesc.MaximumLength = (uint16)MessageDataLength;

    KdSendPacket(
        PacketType,
        &MessageHeaderDesc,
        &MessageDataDesc,
        &KdpContext);
}

/*Struct_Microsoft_Singularity_KernelDebugger_KdStatus*/ uint32
Class_Microsoft_Singularity_KernelDebugger_Kd::g_ReceivePacket(
    /*Struct_Microsoft_Singularity_KernelDebugger_KdPacketType*/ uint32 PacketType,
    uint8* MessageHeaderBuffer,
    int32 MessageHeaderLength,
    uint8* MessageDataBuffer,
    int32 MessageDataBufferLength,
    OUT int32* MessageDataLength)
{
    UINT32 DataLength;

    ASSERT(MessageDataLength != NULL);
    *MessageDataLength = 0;

    STRING MessageHeaderDesc;
    MessageHeaderDesc.Buffer = (PCHAR)MessageHeaderBuffer;
    MessageHeaderDesc.Length = 0;
    MessageHeaderDesc.MaximumLength = (uint16)MessageHeaderLength;

    STRING MessageDataDesc;
    MessageDataDesc.Buffer = (PCHAR)MessageDataBuffer;
    MessageDataDesc.Length = 0;
    MessageDataDesc.MaximumLength = (uint16)MessageDataBufferLength;

    DataLength = (uint32)MessageDataBufferLength;

    uint32 Status = KdReceivePacket(
        PacketType,
        &MessageHeaderDesc,
        &MessageDataDesc,
        &DataLength,
        &KdpContext
        );

    *MessageDataLength = (int)DataLength;

    return Status;
}

void Class_Microsoft_Singularity_KernelDebugger_Kd::g_Lock()
{
    KdpLock();
}

void Class_Microsoft_Singularity_KernelDebugger_Kd::g_Unlock()
{
    KdpUnlock();
}

//
///////////////////////////////////////////////////////////////// End of File.
