///////////////////////////////////////////////////////////////////////////////
//
//  profile.cpp - Extension to dump profiling information.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
//

///////////////////////////////////////////////////////////////////////////////
//
// Preprocessor material

// #define TEST 1
#ifdef TEST

#include <windows.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ExtOut printf

#else

#include "singx86.h"
#define assert //

#endif

#include "diagnose.h"

#define UNUSED(x) (x) = (x);

///////////////////////////////////////////////////////////////////////////////
//
// Forward declarations

extern "C" {
    int OriginCompare(const void* a, const void* b);
    int TargetCompare(const void* a, const void* b);
}

///////////////////////////////////////////////////////////////////////////////
//
// Global variables


///////////////////////////////////////////////////////////////////////////////
//
// Utility methods
#ifdef TEST

static const char* fake_methods[] = { "foo", "bar", "puck", "po", "dizzy", "bazz", "escher", "ringo", "borix" };
static const size_t n_fake_methods = sizeof(fake_methods) / sizeof(fake_methods[0]);

ULONG64 MethodIp(ULONG64 ip)
{
    return ip;
}

void GetMethodName(ULONG64 ip, PSTR buffer, ULONG bufferLength)
{
    strncpy(buffer, fake_methods[ip], bufferLength);
}

#else // TEST

ULONG64 RoundIp(ULONG64 ip)
{
    ULONG64 displacement;
    if (g_ExtSymbols->GetNameByOffset(ip, NULL, 0, NULL, &displacement) == S_OK) {
        return (ip - displacement);
    }
    return ip;
}

void GetMethodName(ULONG64 ip, PSTR buffer, ULONG bufferLength)
{
    ULONG64 displacement;
    ULONG   bufferUsed = 0;

    int status = g_ExtSymbols->GetNameByOffset(ip, buffer, bufferLength,
                                               &bufferUsed, &displacement);
    if (status != S_OK) {
        _snprintf(buffer, bufferLength, "%I64x", ip);
        return;
    }
    else if (displacement != 0) {
        _snprintf(buffer + bufferUsed - 1, bufferLength - bufferUsed, "+0x%I64x", displacement);
    }
}
#endif // TEST

///////////////////////////////////////////////////////////////////////////////
//
// Target Node

struct TargetNode
{
    ULONG64 jumpTarget;
    int     jumpCount;

    struct TargetNode* next;
    struct TargetNode* prev;

    TargetNode(ULONG64 theJumpTarget = 0)
        : jumpTarget(theJumpTarget), jumpCount(1)
    {
        next = this;
        prev = this;
    }

    inline ULONG64 JumpTarget() const   { return jumpTarget; }
    inline int JumpCount() const        { return jumpCount; }

    static int CompareJumps(const TargetNode* a, const TargetNode* b)
    {
        if (a->jumpCount > b->jumpCount) {
            return -1;
        } else if (a->jumpCount < b->jumpCount) {
            return +1;
        }
        return 0;
    }
};

///////////////////////////////////////////////////////////////////////////////
//
// Originating Node

struct OriginNode
{
    struct OriginNode* next;
    struct OriginNode* prev;

  private:
    TargetNode sentinel;
    ULONG64  jumpOrigin;
    int      jumpCount;
    int      nodeCount;

    inline void Append(TargetNode* node)
    {
        node->next = sentinel.next;
        node->next->prev = node;
        node->prev = &sentinel;
        sentinel.next = node;
        nodeCount++;
    }

  public:
    OriginNode(ULONG64 theJumpOrigin = 0) : sentinel(0)
    {
        jumpOrigin = theJumpOrigin;
        jumpCount  = 0;
        nodeCount  = 0;

        this->next = this;
        this->prev = this;
    }

    ~OriginNode()
    {
        TargetNode* node = sentinel.next;
        while (node != &sentinel) {
            TargetNode* next = node->next;
            delete node;
            node = next;
        }
    }

    void AddJump(ULONG64 theJumpTarget)
    {
        jumpCount++;

        TargetNode* node = sentinel.next;
        TargetNode* stop = &sentinel;

        while (node != stop) {
            if (node->jumpTarget == theJumpTarget) {
                node->jumpCount++;
                return;
            }
            node = node->next;
        }
        Append(new TargetNode(theJumpTarget));
    }

    inline int JumpCount() const
    {
        return jumpCount;
    }

    inline ULONG64 JumpOrigin() const { return jumpOrigin; }

    TargetNode** CreateSortTable()
    {
        TargetNode** sortTable = new TargetNode* [nodeCount];
        int insert = 0;

        TargetNode* stop = &sentinel;
        TargetNode* node = stop->next;
        while (node != stop) {
            sortTable[insert++] = node;
            node = node->next;
        }
        assert(insert == nodeCount);
        qsort(sortTable, nodeCount, sizeof(TargetNode*), TargetCompare);
        return sortTable;
    }

    void ReleaseSortTable(TargetNode** sortTable)
    {
        delete [] sortTable;
    }

    void DisplayTargets(const char* preamble)
    {
        char name[512];

        TargetNode** sortTable = CreateSortTable();

        for (int i = 0; i < nodeCount; i++) {
            TargetNode* node = sortTable[i];
            GetMethodName(node->JumpTarget(), name, sizeof(name) - 1);
            ExtOut("%s [%d] %s\n", preamble, node->JumpCount(), name);
        }
        ReleaseSortTable(sortTable);
    }

    static int CompareJumps(const OriginNode* a, const OriginNode* b)
    {
        if (a->jumpCount> b->jumpCount) {
            return -1;
        }
        else if (a->jumpCount < b->jumpCount) {
            return +1;
        }
        return 0;
    }
};

///////////////////////////////////////////////////////////////////////////////
//
// Jump Table to store all IP jumps

class JumpTable
{
    static const int hashBins = 32;

    OriginNode hashTable[hashBins];
    int totalJumps;
    int nodeCount;

    inline int Hash(ULONG64 theJumpOrigin)
    {
        return (int) ((theJumpOrigin ^
                       (theJumpOrigin >> 12) ^
                       (theJumpOrigin >> 24)
                      ) % hashBins);
    }

  public:

    JumpTable()
        : nodeCount(0), totalJumps(0)
    {
    }

    ~JumpTable()
    {
        for (int i = 0; i < hashBins; i++) {
            OriginNode* sentinel = &hashTable[i];
            OriginNode* node = sentinel->next;
            while (node != sentinel) {
                OriginNode* next = node->next;
                delete node;
                node = next;
            }
        }
    }

    void AddJump(ULONG64 theJumpOrigin, ULONG64 theJumpTarget)
    {
        int bin = Hash(theJumpOrigin);

        OriginNode* sentinel = &hashTable[bin];
        OriginNode* node = sentinel->next;
        while (node != sentinel) {
            if (node->JumpOrigin() == theJumpOrigin) {
                node->AddJump(theJumpTarget);
                totalJumps++;
                return;
            }
            node = node->next;
        }

        node = new OriginNode(theJumpOrigin);
        nodeCount++;

        node->AddJump(theJumpTarget);
        totalJumps++;

        node->next = sentinel->next;
        node->prev = sentinel;
        node->next->prev = node;
        sentinel->next = node;
    }

    OriginNode** CreateSortTable()
    {
        // Build table to sort
        OriginNode** sortTable = new OriginNode* [nodeCount];
        int insert = 0;

        for (int i = 0; i < hashBins; i++)
        {
            OriginNode* sentinel = &hashTable[i];
            OriginNode* node = sentinel->next;
            while (node != sentinel) {
                assert(node->JumpOrigin() < 0xffffffffULL);
                sortTable[insert++] = node;
                node = node->next;
            }
        }
        qsort(sortTable, nodeCount, sizeof(OriginNode*), OriginCompare);

        for (int i = 1; i < nodeCount; i++) {
            assert(sortTable[i-1]->JumpCount() >= sortTable[i]->JumpCount());
        }

        return sortTable;
    }

    void ReleaseSortTable(OriginNode** sortTable)
    {
        delete [] sortTable;
    }

    void Display(const char* parentPreamble, const char* childPreamble)
    {
        OriginNode** sortTable = CreateSortTable();
        char name[512];

        int lastJumps = 0x7fffffff;
        for (int i = 0; i < nodeCount; i++) {
            OriginNode* node = sortTable[i];
            int nodeJumps = node->JumpCount();
            assert(nodeJumps <= lastJumps);
            lastJumps = nodeJumps;

            GetMethodName(node->JumpOrigin(), name, sizeof(name) - 1);

            ExtOut("%d. %s %s [%d calls (%.2f%%)]\n",
                   i, parentPreamble, name, nodeJumps,
                   100.0 * (float)nodeJumps / (float) totalJumps);
            node->DisplayTargets(childPreamble);
        }

        ReleaseSortTable(sortTable);
    }
};

int OriginCompare(const void* pa, const void* pb)
{
    return OriginNode::CompareJumps(*((const OriginNode**)pa),
                                    *((const OriginNode**)pb));
}

int TargetCompare(const void* pa, const void* pb)
{
    return TargetNode::CompareJumps(*(const TargetNode**)pa,
                                    *(const TargetNode**)pb);
}

#ifdef TEST

int main()
{
    JumpTable jt;
    for (int calls = 0; calls < 150; calls++) {
        int n = sizeof(fake_methods) / sizeof(fake_methods[0]);
        int s = rand() % n_fake_methods;
        int t = rand() % n_fake_methods;
        jt.AddJump((ULONG64)s, (ULONG64)t);
    }
    jt.Display("  ", "   >>");

    return 0;
}

#else

static HRESULT Usage()
{
    ExtOut("Usage:\n"
           "    !sample {options}\n"
           "Options:\n"
           "    -e size  : Enables sample profiling for the system. Size represents\n"
           "             : the memory buffer in kbytes used for profiling\n"
           "             : This command takes effect only on initial breakpoint in debugger\n"
           "    -c       : Print caller-callee information\n"
           "    -f       : Print frequency distribution of methods\n"
           "    -k       : Print callee-caller information\n"
           "    -l       : Analyze call graph leafs only\n"
           "    -n count : Print count most recent sample stack traces\n"
           "    -t       : Print sample stack traces\n"
           "    -x       : Use exact IP values rather than rounding to method start\n"
          );

    return S_FALSE;
}

void
EnableSampleProfiler(ULONG64 MemorySize)
{
    HRESULT status;
    BOOL OKSymbols = FALSE;

    EXT_CHECK(SetBound("Kernel::ProfilerBufferSize", MemorySize));

    ExtOut("Sampling profiler is enabled for a buffer of %ld KBytes\n",
        (ULONG)MemorySize / 1024);

    OKSymbols = TRUE;

Exit:

    if (!OKSymbols)
    {
        ExtOut("Error accessing variables. Please check symbols for kernel\n");
    }

    return;
}



static void
ClearLog()
{
    ULONG64 address;
    int newPcLength = 0;
    if (g_ExtSymbols->GetOffsetByName("!Processor::pcLength", &address) == S_OK) {
        g_ExtData->WriteVirtual(address, &newPcLength, 4, NULL);
        ExtOut("Log cleared.\n");
        return;
    }
    ExtOut("Failed: Could not locate log length variable.\n");
}

class  SampleStats: public VariableArray {

public:

    SampleStats() : VariableArray(){};
    void Sort();
};

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

static int ItemCompareFreq(const void * e1, const void * e2)
{
    UINT64 *ptr1 = (UINT64 *) e1;
    UINT64 *ptr2 = (UINT64 *) e2;

    if (ptr1[1] < ptr2[1]) {
        return 1;
    } else if (ptr1[1] == ptr2[1]) {
        return 0;
    }

    return -1;
}


void SampleStats::Sort()
{
    //
    //  Sort all ranges by address to make easier searching for overlapped ranges
    //

    qsort(Array, InUse / 2, 2*sizeof(UINT64), ItemCompare);
}

class SampleTracing : public EventingEnumerator
{

public:
    bool doExactIps;
    bool doCallerCallee;
    bool doCalleeCaller;
    bool doLeavesOnly;
    bool doTraces;
    bool doFrequencies;
    int  mostRecent;
    SampleStats * Stats;

    SampleTracing();
    ~SampleTracing();

    //  Override callouts

    bool virtual TypeCallout(EventTypeEntry * entryDescriptor);
    bool virtual EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor);

    void AnalyzeTraces();

private:
    JumpTable foreTable;
    JumpTable backTable;
    UINT64 profileType;
    UINT64 LastTimestamp;
    int CrtItem;
};

SampleTracing::SampleTracing()
{
    doExactIps     = false;
    doCallerCallee = false;
    doCalleeCaller = false;
    doLeavesOnly   = false;
    doTraces       = false;
    doFrequencies  = false;
    mostRecent = 0;
    profileType = 0;

    LastTimestamp = 0;
    CrtItem = 0;

    Stats = new SampleStats();
}
SampleTracing::~SampleTracing()
{
    if (Stats) delete Stats;
}

bool SampleTracing::TypeCallout(EventTypeEntry * entryDescriptor)
{
    if (!EventingEnumerator::TypeCallout(entryDescriptor)) {

        if (!EventingEnumerator::TypeCallout(SystemHeaderType)) {
            return FALSE;
        }
    }

    if (_stricmp(entryDescriptor->Name, "ProfileEvent") == 0) {

        profileType = (UINT64)entryDescriptor->Key;

    }
    return TRUE;
}

bool SampleTracing::EntryCallout(EntryHeader *header, EventTypeEntry * entryDescriptor)
{
    if (entryDescriptor == NULL) {

        return FALSE;
    }

    //
    //  Filter only for the events of interest
    //

    if (entryDescriptor->Key == profileType) {

        if (doTraces) {

            ULONG cpuId;
            UINT64 timestamp;

            //
            //  Switch to the metadata context of an entry to access the metadata fields
            //

            ULONG_PTR ctx = SWITCH_TO_METADATA_CURSOR();

                FieldEntry * field = SystemHeaderType->GetField("Cpu");
                cpuId = (ULONG)field->GetFieldNumericValue();

                field = SystemHeaderType->GetField("Timestamp");
                timestamp = field->GetFieldNumericValue();

            RESTORE_CURSOR(ctx);

            ExtOut("%5ld %2ld %18I64x  %12I64d:",
                   (int)CrtItem,
                   (int)cpuId,
                   timestamp,
                   (LastTimestamp != 0 ? (timestamp - LastTimestamp) : 0));

            LastTimestamp = timestamp;
            CrtItem += 1;
        }

        //
        //  Prepare to access the array of IP entries
        //

        FieldEntry * array = entryDescriptor->GetField("StackTrace");
        void * buffer = entryDescriptor->GetFieldArray((int)array->GetFieldNumericValue());

        int count = array->GetArraySize(buffer);

        int doneFirst = 0;
        ULONG64 lastIp = 0;
        bool leafJumpDone = false;
        bool leafIpDone  = false;
        CHAR name[512];

        for (int i = 0; i < count; i++) {

            UINT64 eip = (UINT64)array->GetFieldNumericValue(buffer, i);

            if (!doExactIps) {
                eip = RoundIp(eip);
            }

            if ((leafIpDone == false || doLeavesOnly == false) && eip != 0) {
                Stats->Add(eip);
                Stats->Add(0);
                leafIpDone = true;
            }

            if (lastIp != 0 && eip != 0 &&
                (leafJumpDone == false || doLeavesOnly == false)) {
                foreTable.AddJump(lastIp, eip);
                backTable.AddJump(eip, lastIp);
                leafJumpDone = true;
            }

            lastIp = eip;

            if (eip == 0) {
                break;
            }

            doneFirst |= 1;

            if (doTraces == false)
                continue;


            if (g_ExtSymbols->GetNameByOffset(eip, (PSTR)&name, sizeof(name), NULL, NULL) == S_OK) {
                if (doneFirst)
                    ExtOut(" <- %s (%p)", name, eip);
                else
                    ExtOut(" %s (%p)", name, eip);
            }
            else {
                if (doneFirst)
                    ExtOut(" <- %p", eip);
                else
                    ExtOut(" %p", eip);
            }
        }

        if (doTraces)
            ExtOut("\n");
    }

    return TRUE;

}

void SampleTracing::AnalyzeTraces()
{
    CHAR name[512];
    if (doFrequencies) {
        ExtOut("==================================================================\n");
        ExtOut("Raw instruction hits\n");

        if (Stats->InUse > 0) {

            Stats->Sort();

            int outIndex = 0;
            ULONG64 lastIp = Stats->Array[0];
            for (int i = 0; i < Stats->InUse;  i+= 2) {
                if (Stats->Array[i] == lastIp) {
                    Stats->Array[outIndex + 1] += 1;
                }
                else {
                    outIndex += 2;
                    Stats->Array[outIndex] = Stats->Array[i];
                    Stats->Array[outIndex + 1] = 1;
                    lastIp = Stats->Array[i];
                }
            }

            // Sort on frequency and display
            qsort(Stats->Array, outIndex / 2, 2*sizeof(UINT64), ItemCompareFreq);
            ExtOut("Top of the pops has %d entries:\n", outIndex);

            for (int i = 0; i < outIndex; i += 2) {
                if (g_ExtSymbols->GetNameByOffset(Stats->Array[i],
                                                  (PSTR)&name,
                                                  sizeof(name),
                                                  NULL, NULL) == S_OK) {
                    ExtOut("% 7d %p %s\n", (int)Stats->Array[i + 1], Stats->Array[i], name);
                }
                else {
                    ExtOut("% 7d %p (unknown symbol)\n", (int)Stats->Array[i + 1], Stats->Array[i]);
                }
            }
        }
    }

    if (doCallerCallee) {
        ExtOut("==================================================================\n");
        ExtOut("Calls by target method to other methods:\n");
        backTable.Display("Calls made by", "       ");
    }

    if (doCalleeCaller) {
        ExtOut("==================================================================\n");
        ExtOut("Calls to target method by other methods.\n");
        foreTable.Display("Calls made to",   "       ");
    }
}


EXT_DECL(sample) // Defines: PDEBUG_CLIENT Client, PCSTR args
{

    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    pointerSize = (g_ExtControl->IsPointer64Bit() == S_OK) ? 8 : 4;

    SourceCollector * collector = new SourceCollector("SampleProfiler:0", "Timestamp");
    SampleTracing * dump = NULL;

    if (collector) {

        dump = new SampleTracing();

        if (dump == NULL) {
            ExtOut("Not enough memory\n");
            EXT_CHECK(~S_OK);
        }
    }

    collector->TypeHandle = 0;
    collector->GroupByController = TRUE;
    collector->cascadeEnumerator = dump;

    while (*args != '\0') {
        while (*args == ' ' || * args == '\t') {
            args++;
        }

        if (*args != '-' && *args != '/') {
            Usage();
            EXT_CHECK(~S_OK);
        }
        args++;
        switch (tolower(*args++)) {
          case 'e' : {

                SKIP_WHITESPACES(args);
                int bufferSize = (int)GetValue(args, true);
                EnableSampleProfiler(bufferSize*1024);
                goto Exit;
              }
            break;
          case 'c':
            dump->doCallerCallee = true;
            break;
          case 'f':
            dump->doFrequencies = true;
            break;
          case 'k':
            dump->doCalleeCaller = true;
            break;
          case 'l':
            dump->doLeavesOnly = true;
            break;
          case 'n':
            while ((*args == ' ' || *args == '\t') && *args != '\0') {
                args++;
            }
            dump->mostRecent = atoi(args);
            while (*args != ' ' && *args != '\t' && *args != '\0') {
                args++;
            }
            break;
          case 't':
            dump->doTraces = true;
            break;
          case 'x':
            dump->doExactIps = true;
            break;
          default:
            Usage();
            EXT_CHECK(~S_OK);
        }
    }

    if (dump->doCallerCallee == false &&
        dump->doCalleeCaller == false &&
        dump->doTraces       == false &&
        dump->doFrequencies  == false) {
        Usage();
        EXT_CHECK(~S_OK);
    }

    if (dump->doTraces) {
        ExtOut("<Sample Round> <DeltaTicks> <interrupt> <eip ...>\n");
    }

    // Allocate statistics array

    ExtOut("Starting analysis of sample log\n");
    if (dump->doLeavesOnly)
        ExtOut("Analyzing leaf nodes only.\n");

    if (dump->doTraces) {
        ExtOut("==================================================================\n");
        ExtOut("Raw call stacks\n");
    }

    if (dump->doExactIps) {
        ExtOut("Exact IPs\n");
    }

    WalkTracingDatabase(collector, FALSE);
    dump->AnalyzeTraces();


  Exit:
    if (collector) delete collector;
    if (dump) delete dump;
    ExtRelease();
    return S_OK;
}


#endif // TEST
