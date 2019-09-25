/////////////////////////////////////////////////////////////////////////////
//
//  threads.cpp - Extension to find Singularity threads.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//
#include "singx86.h"

ULONG64 stoppedThreads;
ULONG64 blockedThreads;
ULONG64 runnableThreads;
ULONG64 unblockedThreads;
ULONG64 idleThreads;

CHAR * GetQueueName(ULONG64 queue)
{
    if (stoppedThreads == 0) {
        stoppedThreads = GetStaticPointer(kernel_stoppedThreads);
        blockedThreads = GetStaticPointer(kernel_blockedThreads);
        runnableThreads = GetStaticPointer(kernel_runnableThreads);
        unblockedThreads = GetStaticPointer(kernel_unblockedThreads);
        idleThreads = GetStaticPointer(kernel_idleThreads);
        ExtVerb("Queues: stopped=%p blocked=%p runnable=%p unblocked=%p idle=%p\n",
                stoppedThreads, blockedThreads, runnableThreads,
                unblockedThreads, idleThreads);
    }

    if (queue == stoppedThreads) {
        return "stopped";
    }
    if (queue == blockedThreads) {
        return "blocked";
    }
    if (queue == runnableThreads) {
        return "runnable";
    }
    if (queue == unblockedThreads) {
        return "unblocked";
    }
    if (queue == idleThreads) {
        return "idle";
    }
    return "running";
}

HRESULT DumpThread(ULONG64 threadaddr, bool stack, bool fullstack, bool detail, bool blocked)
{
    HRESULT status = S_OK;

    if (threadaddr == 0) {
        return S_FALSE;
    }

    Thread thread;
    ThreadEntry entry;

    EXT_CHECK(ThreadStruct->Read(threadaddr, &thread));
    EXT_CHECK(ThreadEntryStruct.Read(thread.schedulerEntry, &entry));

    char *which = GetQueueName(entry.queue);
    char offQueueMarker = (entry.queue != NULL) ? ' ' : '*';

    if ((stack) || (fullstack)) {
        ExtOut("%c thread=%p { tid=%03x pid=%03x eip=%p, ebp=%p, esp=%p %02x }\n",
               offQueueMarker,
               threadaddr,
               (ULONG)(thread.context.threadIndex == 0xffff ? 0xfff : thread.context.threadIndex),
               (ULONG)(thread.context.processId == 0xffff ? 0xfff : thread.context.processId),
               thread.context.threadRecord.spill.ip,
               thread.context.threadRecord.spill.bp,
               thread.context.threadRecord.spill.sp,
               (ULONG)thread.context.gcStates);

        if (fullstack) {
            DEBUG_STACK_FRAME frames[30];
            ULONG filled = 0;

            status = g_ExtControl->GetStackTrace(thread.context.threadRecord.spill.bp,
                                                 thread.context.threadRecord.spill.sp,
                                                 thread.context.threadRecord.spill.ip,
                                                 frames,
                                                 arrayof(frames),
                                                 &filled);

            if (status == S_OK) {
                g_ExtClient->SetOutputLinePrefix("      ");
                g_ExtControl->OutputStackTrace(DEBUG_OUTPUT_NORMAL,
                                               frames,
                                               filled,
                                               detail ? (DEBUG_STACK_FRAME_ADDRESSES |
                                                         DEBUG_STACK_COLUMN_NAMES |
                                                         DEBUG_STACK_SOURCE_LINE) : 0);
            }
        }
        else {
            DEBUG_STACK_FRAME frames[10];
            ULONG filled = 0;

            status = g_ExtControl->GetStackTrace(thread.context.threadRecord.spill.bp,
                                                 thread.context.threadRecord.spill.sp,
                                                 thread.context.threadRecord.spill.ip,
                                                 frames,
                                                 arrayof(frames),
                                                 &filled);

            if (status == S_OK) {
                g_ExtClient->SetOutputLinePrefix("      ");
                g_ExtControl->OutputStackTrace(DEBUG_OUTPUT_NORMAL,
                                               frames,
                                               filled,
                                               detail ? (DEBUG_STACK_FRAME_ADDRESSES |
                                                         DEBUG_STACK_COLUMN_NAMES |
                                                         DEBUG_STACK_SOURCE_LINE) : 0);
            }
        }
    }
    else {
        CHAR name[512];
        ULONG64 displacement = 0;

        status = g_ExtSymbols->GetNameByOffset(thread.context.threadRecord.spill.ip,
                                               name,
                                               arrayof(name),
                                               NULL,
                                               &displacement);
        if (status == S_OK) {
            ExtOut("%c thread=%p { tid=%03x pid=%03x eip=%p, ebp=%p, esp=%p %02x } %s+%I64d\n",
                   offQueueMarker,
                   threadaddr,
                   (ULONG)(thread.context.threadIndex == 0xffff ? 0xfff : thread.context.threadIndex),
                   (ULONG)(thread.context.processId == 0xffff ? 0xfff : thread.context.processId),
                   thread.context.threadRecord.spill.ip,
                   thread.context.threadRecord.spill.bp,
                   thread.context.threadRecord.spill.sp,
                   (ULONG)thread.context.gcStates,
                   name,
                   (LONG64)displacement);
        }
        else {
            ExtOut("%c thread=%p { tid=%03x pid=%03x eip=%p, ebp=%p, esp=%p %02x }\n",
                   offQueueMarker,
                   threadaddr,
                   (ULONG)(thread.context.threadIndex == 0xffff ? 0xfff : thread.context.threadIndex),
                   (ULONG)(thread.context.processId == 0xffff ? 0xfff : thread.context.processId),
                   thread.context.threadRecord.spill.ip,
                   thread.context.threadRecord.spill.bp,
                   thread.context.threadRecord.spill.sp,
                   (ULONG)thread.context.gcStates);
        }
    }
    if (blocked) {
        if (entry.queue != NULL) {
        }
    }

    if (blocked) {
        ExtOut("                  { %-8.8s blocked=%d count=%d until=%16I64x queue=%p entry=%p}\n",
               which,
               (ULONG)thread.blocked,
               (ULONG)thread.blockedOnCount,
               thread.blockedUntil,
               entry.queue,
               thread.schedulerEntry);
    }
  Exit:
    return status;
}

EXT_DECL(threads) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    bool stack = false;
    bool fullstack = false;
    bool detail = false;
    bool blocked = false;

    while (*args != '\0') {
        // skip whitespace
        while (*args == ' ' || *args == '\t') {
            args++;
        }

        // process argument
        if (*args == '-' || *args == '/') {
            args++;
            switch (*args++) {
              case 'd': // detail
              case 'D':
                detail = !detail;
                break;
              case 'f': // fullstack
              case 'F':
                fullstack = !fullstack;
                break;
              case 's': // stack
              case 'S':
                stack = !stack;
                break;
              case 'b': // Blocked information
              case 'B':
                blocked = !blocked;
                break;
              case '?': // Help
              case 'h':
              case 'H':
                status = S_FALSE;
                goto Exit;
            }
            while (*args != ' ') {
                args++;
            }
        }
        else {
            break;
        }
    }

    ULONG pointerSize = (g_ExtControl->IsPointer64Bit() == S_OK) ? 8 : 4;
    ULONG64 address = 0;
    ULONG64 threads = 0;
    ULONG type = 0;
    ULONG subtype = 0;
    ULONG64 module = 0;

    EXT_CHECK(g_ExtSymbols->GetOffsetByName(kernel_threadTable, &address));
    EXT_CHECK(g_ExtSymbols->GetOffsetTypeId(address, &type, &module));
    EXT_CHECK(TraceReadPointer(1, address, &threads));
    ExtVerb("threadTable: %p\n", threads);

    CHAR name[512];

    EXT_CHECK(g_ExtSymbols->GetTypeName(module, type, name, arrayof(name), NULL));
    ExtVerb("  threadTable type: %s\n", name);
    int len = (int)strlen(name);
    if (len > 3 &&
        name[len-3] == '[' &&
        name[len-2] == ']' &&
        name[len-1] == '*') {
        name[len-3] = '\0';

        EXT_CHECK(g_ExtSymbols->GetTypeId(module, name, &subtype));
        EXT_CHECK(g_ExtSymbols->GetTypeName(module, subtype, name, arrayof(name), NULL));
        ExtVerb("  threadTable[] type: %s\n", name);
    }

    ULONG lengthOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "overall_length", &lengthOffset));

    ULONG valuesOffset = 0;
    EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, "values", &valuesOffset));

    ULONG length = 0;
    EXT_CHECK(TraceRead(threads + lengthOffset, &length, sizeof(length)));
    ExtOut("threadTable: %p [maximum %d entries]\n", threads, length);

    CHAR prefix[256];
    EXT_CHECK(client->GetOutputLinePrefix(prefix, arrayof(prefix), NULL));
    for (ULONG id = 0; id < length; id++) {
        ULONG64 thread = 0;

        EXT_CHECK(TraceReadPointer(1, threads + valuesOffset + id * pointerSize, &thread));
        if (thread != 0) {
            DumpThread(thread, stack, fullstack, detail, blocked);
            g_ExtClient->SetOutputLinePrefix(prefix);
        }
    }

    EXT_LEAVE();    // Macro includes: return status;
}
