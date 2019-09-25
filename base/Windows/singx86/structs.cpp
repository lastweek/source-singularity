///////////////////////////////////////////////////////////////////////////////////////////////////
//
//  structs.cpp - extensions to dump well-known structs.
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

#include "singx86.h"
#include <strsafe.h>

///////////////////////////////////////////////////////////////////////////////////////////////////
//
FieldType *ThreadContextFields = NULL;
StructType *ThreadContextStruct = NULL;

FieldType X86ThreadContextFields[] = {
    FIELD(ThreadContext, threadRecord.spill.mmx),       // "mmx" must be ThreadContextFields[0]
    FIELD(ThreadContext, threadRecord.spill.mmx.st0),   // "st0" must be ThreadContextFields[1]
    FIELD(ThreadContext, threadRecord.spill.mmx.st1),
    FIELD(ThreadContext, threadRecord.spill.mmx.st2),
    FIELD(ThreadContext, threadRecord.spill.mmx.st3),
    FIELD(ThreadContext, threadRecord.spill.mmx.st4),
    FIELD(ThreadContext, threadRecord.spill.mmx.st5),
    FIELD(ThreadContext, threadRecord.spill.mmx.st6),
    FIELD(ThreadContext, threadRecord.spill.mmx.st7),
    FIELD(ThreadContext, threadRecord.spill.mmx.fcw),
    FIELD(ThreadContext, threadRecord.spill.mmx.fsw),
    FIELD(ThreadContext, threadRecord.spill.mmx.ftw),
    FIELD(ThreadContext, threadRecord.spill.mmx.fop),
    FIELD(ThreadContext, threadRecord.spill.mmx.ip),
    FIELD(ThreadContext, threadRecord.spill.mmx.cs),
    FIELD(ThreadContext, threadRecord.spill.mmx.dp),
    FIELD(ThreadContext, threadRecord.spill.mmx.ds),
    FIELD(ThreadContext, threadRecord.spill.mmx.mxcsr),
    FIELD(ThreadContext, threadRecord.spill.mmx.mxcsrmask),
    FIELD(ThreadContext, threadRecord.spill.ax),
    FIELD(ThreadContext, threadRecord.spill.bx),
    FIELD(ThreadContext, threadRecord.spill.cx),
    FIELD(ThreadContext, threadRecord.spill.dx),
    FIELD(ThreadContext, threadRecord.spill.di),
    FIELD(ThreadContext, threadRecord.spill.si),
    FIELD(ThreadContext, threadRecord.spill.sp),
    FIELD(ThreadContext, threadRecord.spill.ip),
    FIELD(ThreadContext, threadRecord.spill.bp),
    FIELD(ThreadContext, threadRecord.spill.fl),
    // Common Fields
    FIELD(ThreadContext, threadRecord.activeStackLimit),
    FIELD(ThreadContext, regs),
    FIELD(ThreadContext, prev),
    FIELD(ThreadContext, next),
    FIELD(ThreadContext, stackBegin),
    FIELD(ThreadContext, stackLimit),
    FIELD(ThreadContext, processId),
    FIELD(ThreadContext, uncaughtFlag),
    FIELD(ThreadContext, suspendAlert),
    FIELD(ThreadContext, _thread),
    FIELD(ThreadContext, processThread),
    FIELD(ThreadContext, stackMarkers),
    FIELD(ThreadContext, processMarkers),
    FIELD(ThreadContext, threadIndex),
    FIELD(ThreadContext, processThreadIndex),
    FIELD(ThreadContext, gcStates),
    FIELDEND(),
};

FieldType X64ThreadContextFields[] = {
    FIELD(ThreadContext, threadRecord.spill.mmx),       // "mmx" must be ThreadContextFields[0]
    FIELD(ThreadContext, threadRecord.spill.mmx.st0),   // "st0" must be ThreadContextFields[1]
    FIELD(ThreadContext, threadRecord.spill.mmx.st1),
    FIELD(ThreadContext, threadRecord.spill.mmx.st2),
    FIELD(ThreadContext, threadRecord.spill.mmx.st3),
    FIELD(ThreadContext, threadRecord.spill.mmx.st4),
    FIELD(ThreadContext, threadRecord.spill.mmx.st5),
    FIELD(ThreadContext, threadRecord.spill.mmx.st6),
    FIELD(ThreadContext, threadRecord.spill.mmx.st7),
    FIELD(ThreadContext, threadRecord.spill.mmx.fcw),
    FIELD(ThreadContext, threadRecord.spill.mmx.fsw),
    FIELD(ThreadContext, threadRecord.spill.mmx.ftw),
    FIELD(ThreadContext, threadRecord.spill.mmx.fop),
    FIELD(ThreadContext, threadRecord.spill.mmx.ip),
    FIELD(ThreadContext, threadRecord.spill.mmx.cs),
    FIELD(ThreadContext, threadRecord.spill.mmx.dp),
    FIELD(ThreadContext, threadRecord.spill.mmx.ds),
    FIELD(ThreadContext, threadRecord.spill.mmx.mxcsr),
    FIELD(ThreadContext, threadRecord.spill.mmx.mxcsrmask),
    FIELD(ThreadContext, threadRecord.spill.ax),
    FIELD(ThreadContext, threadRecord.spill.bx),
    FIELD(ThreadContext, threadRecord.spill.cx),
    FIELD(ThreadContext, threadRecord.spill.dx),
    FIELD(ThreadContext, threadRecord.spill.di),
    FIELD(ThreadContext, threadRecord.spill.si),
    FIELD(ThreadContext, threadRecord.spill.sp),
    FIELD(ThreadContext, threadRecord.spill.ip),
    FIELD(ThreadContext, threadRecord.spill.bp),
    FIELD(ThreadContext, threadRecord.spill.r8),
    FIELD(ThreadContext, threadRecord.spill.r9),
    FIELD(ThreadContext, threadRecord.spill.r10),
    FIELD(ThreadContext, threadRecord.spill.r11),
    FIELD(ThreadContext, threadRecord.spill.r12),
    FIELD(ThreadContext, threadRecord.spill.r13),
    FIELD(ThreadContext, threadRecord.spill.r14),
    FIELD(ThreadContext, threadRecord.spill.r15),
    FIELD(ThreadContext, threadRecord.spill.fl),
    // Common Fields
    FIELD(ThreadContext, threadRecord.activeStackLimit),
    FIELD(ThreadContext, regs),
    FIELD(ThreadContext, prev),
    FIELD(ThreadContext, next),
    FIELD(ThreadContext, stackBegin),
    FIELD(ThreadContext, stackLimit),
    FIELD(ThreadContext, processId),
    FIELD(ThreadContext, uncaughtFlag),
    FIELD(ThreadContext, suspendAlert),
    FIELD(ThreadContext, _thread),
    FIELD(ThreadContext, processThread),
    FIELD(ThreadContext, stackMarkers),
    FIELD(ThreadContext, processMarkers),
    FIELD(ThreadContext, threadIndex),
    FIELD(ThreadContext, processThreadIndex),
    FIELD(ThreadContext, gcStates),
    FIELDEND(),
};

FieldType ArmThreadContextFields[] = {
    FIELD(ThreadContext, threadRecord.spill.r0),
    FIELD(ThreadContext, threadRecord.spill.r1),
    FIELD(ThreadContext, threadRecord.spill.r2),
    FIELD(ThreadContext, threadRecord.spill.r3),
    FIELD(ThreadContext, threadRecord.spill.r4),
    FIELD(ThreadContext, threadRecord.spill.r5),
    FIELD(ThreadContext, threadRecord.spill.r6),
    FIELD(ThreadContext, threadRecord.spill.r7),
    FIELD(ThreadContext, threadRecord.spill.r8),
    FIELD(ThreadContext, threadRecord.spill.r9),
    FIELD(ThreadContext, threadRecord.spill.r10),
    FIELD(ThreadContext, threadRecord.spill.r11),
    FIELD(ThreadContext, threadRecord.spill.r12),
    FIELD(ThreadContext, threadRecord.spill.sp),
    FIELD(ThreadContext, threadRecord.spill.lr),
    FIELD(ThreadContext, threadRecord.spill.pc),
    FIELD(ThreadContext, threadRecord.spill.cpsr),
    // Common Fields
    FIELD(ThreadContext, threadRecord.activeStackLimit),
    FIELD(ThreadContext, regs),
    FIELD(ThreadContext, prev),
    FIELD(ThreadContext, next),
    FIELD(ThreadContext, stackBegin),
    FIELD(ThreadContext, stackLimit),
    FIELD(ThreadContext, processId),
    FIELD(ThreadContext, uncaughtFlag),
    FIELD(ThreadContext, suspendAlert),
    FIELD(ThreadContext, _thread),
    FIELD(ThreadContext, processThread),
    FIELD(ThreadContext, stackMarkers),
    FIELD(ThreadContext, processMarkers),
    FIELD(ThreadContext, threadIndex),
    FIELD(ThreadContext, processThreadIndex),
    FIELD(ThreadContext, gcStates),
    FIELDEND(),
};

///////////////////////////////////////////////////////////////////////////////////////////////////
//
FieldType *ThreadFields = NULL;
StructType *ThreadStruct = NULL;

FieldType X86ThreadFields[] = {
    FIELD(Thread, context),                             // "context" must be ThreadFields[0]
    FIELD(Thread, context.threadRecord.spill.ax),
    FIELD(Thread, context.threadRecord.spill.bx),
    FIELD(Thread, context.threadRecord.spill.cx),
    FIELD(Thread, context.threadRecord.spill.dx),
    FIELD(Thread, context.threadRecord.spill.di),
    FIELD(Thread, context.threadRecord.spill.si),
    FIELD(Thread, context.threadRecord.spill.sp),
    FIELD(Thread, context.threadRecord.spill.ip),
    FIELD(Thread, context.threadRecord.spill.bp),
    FIELD(Thread, context.threadRecord.spill.fl),
    FIELD(Thread, context.threadRecord.spill.mmx.st0),
    FIELD(Thread, context.threadRecord.spill.mmx.st1),
    FIELD(Thread, context.threadRecord.spill.mmx.st2),
    FIELD(Thread, context.threadRecord.spill.mmx.st3),
    FIELD(Thread, context.threadRecord.spill.mmx.st4),
    FIELD(Thread, context.threadRecord.spill.mmx.st5),
    FIELD(Thread, context.threadRecord.spill.mmx.st6),
    FIELD(Thread, context.threadRecord.spill.mmx.st7),
    FIELD(Thread, context.threadRecord.spill.mmx.fcw),
    FIELD(Thread, context.threadRecord.spill.mmx.fsw),
    FIELD(Thread, context.threadRecord.spill.mmx.ftw),
    FIELD(Thread, context.threadRecord.spill.mmx.fop),
    FIELD(Thread, context.threadRecord.spill.mmx.ip),
    FIELD(Thread, context.threadRecord.spill.mmx.cs),
    FIELD(Thread, context.threadRecord.spill.mmx.dp),
    FIELD(Thread, context.threadRecord.spill.mmx.ds),
    FIELD(Thread, context.threadRecord.spill.mmx.mxcsr),
    FIELD(Thread, context.threadRecord.spill.mmx.mxcsrmask),
    // Common Fields
    FIELD(Thread, context.threadRecord.activeStackLimit),
    FIELD(Thread, context.regs),
    FIELD(Thread, context.prev),
    FIELD(Thread, context.next),
    FIELD(Thread, context.stackBegin),
    FIELD(Thread, context.stackLimit),
    FIELD(Thread, context.processId),
    FIELD(Thread, context.uncaughtFlag),
    FIELD(Thread, context.suspendAlert),
    FIELD(Thread, context._thread),
    FIELD(Thread, context.processThread),
    FIELD(Thread, context.stackMarkers),
    FIELD(Thread, context.processMarkers),
    FIELD(Thread, context.threadIndex),
    FIELD(Thread, context.processThreadIndex),
    FIELD(Thread, context.gcStates),
    FIELD(Thread, blocked),
    FIELD(Thread, blockedOn),
    FIELD(Thread, blockedOnCount),
    FIELD(Thread, blockedUntil),
    FIELD(Thread, process),
    FIELD(Thread, schedulerEntry),
    FIELDEND(),
};

FieldType X64ThreadFields[] = {
    FIELD(Thread, context),                             // "context" must be ThreadFields[0]
    FIELD(Thread, context.threadRecord.spill.ax),
    FIELD(Thread, context.threadRecord.spill.bx),
    FIELD(Thread, context.threadRecord.spill.cx),
    FIELD(Thread, context.threadRecord.spill.dx),
    FIELD(Thread, context.threadRecord.spill.di),
    FIELD(Thread, context.threadRecord.spill.si),
    FIELD(Thread, context.threadRecord.spill.sp),
    FIELD(Thread, context.threadRecord.spill.ip),
    FIELD(Thread, context.threadRecord.spill.bp),
    FIELD(Thread, context.threadRecord.spill.r8),
    FIELD(Thread, context.threadRecord.spill.r9),
    FIELD(Thread, context.threadRecord.spill.r10),
    FIELD(Thread, context.threadRecord.spill.r11),
    FIELD(Thread, context.threadRecord.spill.r12),
    FIELD(Thread, context.threadRecord.spill.r13),
    FIELD(Thread, context.threadRecord.spill.r14),
    FIELD(Thread, context.threadRecord.spill.r15),
    FIELD(Thread, context.threadRecord.spill.fl),
    FIELD(Thread, context.threadRecord.spill.mmx.st0),
    FIELD(Thread, context.threadRecord.spill.mmx.st1),
    FIELD(Thread, context.threadRecord.spill.mmx.st2),
    FIELD(Thread, context.threadRecord.spill.mmx.st3),
    FIELD(Thread, context.threadRecord.spill.mmx.st4),
    FIELD(Thread, context.threadRecord.spill.mmx.st5),
    FIELD(Thread, context.threadRecord.spill.mmx.st6),
    FIELD(Thread, context.threadRecord.spill.mmx.st7),
    FIELD(Thread, context.threadRecord.spill.mmx.fcw),
    FIELD(Thread, context.threadRecord.spill.mmx.fsw),
    FIELD(Thread, context.threadRecord.spill.mmx.ftw),
    FIELD(Thread, context.threadRecord.spill.mmx.fop),
    FIELD(Thread, context.threadRecord.spill.mmx.ip),
    FIELD(Thread, context.threadRecord.spill.mmx.cs),
    FIELD(Thread, context.threadRecord.spill.mmx.dp),
    FIELD(Thread, context.threadRecord.spill.mmx.ds),
    FIELD(Thread, context.threadRecord.spill.mmx.mxcsr),
    FIELD(Thread, context.threadRecord.spill.mmx.mxcsrmask),
    // Common Fields
    FIELD(Thread, context.threadRecord.activeStackLimit),
    FIELD(Thread, context.regs),
    FIELD(Thread, context.prev),
    FIELD(Thread, context.next),
    FIELD(Thread, context.stackBegin),
    FIELD(Thread, context.stackLimit),
    FIELD(Thread, context.processId),
    FIELD(Thread, context.uncaughtFlag),
    FIELD(Thread, context.suspendAlert),
    FIELD(Thread, context._thread),
    FIELD(Thread, context.processThread),
    FIELD(Thread, context.stackMarkers),
    FIELD(Thread, context.processMarkers),
    FIELD(Thread, context.threadIndex),
    FIELD(Thread, context.processThreadIndex),
    FIELD(Thread, context.gcStates),
    FIELD(Thread, blocked),
    FIELD(Thread, blockedOn),
    FIELD(Thread, blockedOnCount),
    FIELD(Thread, blockedUntil),
    FIELD(Thread, process),
    FIELD(Thread, schedulerEntry),
    FIELDEND(),
};

FieldType ArmThreadFields[] = {
    FIELD(Thread, context),                             // "context" must be ThreadFields[0]
    FIELD(Thread, context.threadRecord.spill.r0),
    FIELD(Thread, context.threadRecord.spill.r1),
    FIELD(Thread, context.threadRecord.spill.r2),
    FIELD(Thread, context.threadRecord.spill.r3),
    FIELD(Thread, context.threadRecord.spill.r4),
    FIELD(Thread, context.threadRecord.spill.r5),
    FIELD(Thread, context.threadRecord.spill.r6),
    FIELD(Thread, context.threadRecord.spill.r7),
    FIELD(Thread, context.threadRecord.spill.r8),
    FIELD(Thread, context.threadRecord.spill.r9),
    FIELD(Thread, context.threadRecord.spill.r10),
    FIELD(Thread, context.threadRecord.spill.r11),
    FIELD(Thread, context.threadRecord.spill.r12),
    FIELD(Thread, context.threadRecord.spill.sp),
    FIELD(Thread, context.threadRecord.spill.lr),
    FIELD(Thread, context.threadRecord.spill.pc),
    FIELD(Thread, context.threadRecord.spill.cpsr),
    // Common Fields.
    FIELD(Thread, context.threadRecord.activeStackLimit),
    FIELD(Thread, context.regs),
    FIELD(Thread, context.prev),
    FIELD(Thread, context.next),
    FIELD(Thread, context.stackBegin),
    FIELD(Thread, context.stackLimit),
    FIELD(Thread, context.processId),
    FIELD(Thread, context.uncaughtFlag),
    FIELD(Thread, context.suspendAlert),
    FIELD(Thread, context._thread),
    FIELD(Thread, context.processThread),
    FIELD(Thread, context.stackMarkers),
    FIELD(Thread, context.processMarkers),
    FIELD(Thread, context.threadIndex),
    FIELD(Thread, context.processThreadIndex),
    FIELD(Thread, context.gcStates),
    FIELD(Thread, blocked),
    FIELD(Thread, blockedOn),
    FIELD(Thread, blockedOnCount),
    FIELD(Thread, blockedUntil),
    FIELD(Thread, process),
    FIELD(Thread, schedulerEntry),
    FIELDEND(),
};

///////////////////////////////////////////////////////////////////////////////////////////////////
//
FieldType ThreadEntryFields[] = {
    FIELD(ThreadEntry, queue),
    FIELDEND(),
};

// kernel name is potentially fixed up in StructType::Initialize
StructType ThreadEntryStruct
= StructType(kernel_ThreadEntry,
             sizeof(ThreadEntry), ThreadEntryFields);

FieldType StringFields[] = {
    FIELD(String, m_firstChar),                         // Accessed directly as Field[0]
    FIELD(String, m_stringLength),
    FIELDEND(),
};

// kernel name is potentially fixed up in StructType::Initialize
StructType StringStruct = StructType(kernel_String,
                                     sizeof(String), StringFields);

FieldType LogEntryFields[] = {
    FIELD(LogEntry, _cycleCount),
    FIELD(LogEntry, _eip),
    FIELD(LogEntry, _cpuId),
    FIELD(LogEntry, _threadId),
    FIELD(LogEntry, _processId),
    FIELD(LogEntry, _tag),
    FIELD(LogEntry, _severity),
    FIELD(LogEntry, _strings),
    FIELD(LogEntry, _text),
    FIELD(LogEntry, _arg0),
    FIELD(LogEntry, _arg1),
    FIELD(LogEntry, _arg2),
    FIELD(LogEntry, _arg3),
    FIELD(LogEntry, _arg4),
    FIELD(LogEntry, _arg5),
    FIELDEND(),
};

// kernel name is potentially fixed up in StructType::Initialize
StructType LogEntryStruct = StructType(kernel_Struct_Microsoft_Singularity_Tracing_LogEntry,
                                       sizeof(LogEntry), LogEntryFields);

FieldType ProcessorContextFields[] = {
    FIELD(ProcessorContext, cpuRecord.id),
    FIELD(ProcessorContext, cpuRecord.interruptStackBegin),
    FIELD(ProcessorContext, cpuRecord.interruptStackLimit),
    FIELD(ProcessorContext, _processor),
    FIELD(ProcessorContext, exception),
    FIELD(ProcessorContext, nextProcessorContext),
    FIELDEND(),
};

// kernel name is potentially fixed up in StructType::Initialize
StructType ProcessorContextStruct
= StructType(kernel_ProcessorContext,
             sizeof(ProcessorContext), ProcessorContextFields);

FieldType ProcessorFields[] = {
    FIELD(Processor, context),
    FIELD(Processor, pic),
    FIELD(Processor, timer),
    FIELD(Processor, clock),
    FIELD(Processor, timerInterrupt),
    FIELD(Processor, clockInterrupt),
    FIELD(Processor, inInterruptContext),
    FIELD(Processor, halted),
    FIELD(Processor, NumExceptions),
    FIELD(Processor, NumInterrupts),
    FIELD(Processor, NumContextSwitches),
    FIELD(Processor, interruptCounts),
    FIELDEND(),
};

// kernel name is potentially fixed up in StructType::Initialize
StructType ProcessorStruct
= StructType(kernel_Processor,
             sizeof(Processor), ProcessorFields);

///////////////////////////////////// Remote to Local conversions for structs.
//
StructType * StructType::registered = NULL;

StructType::StructType(PSTR name, ULONG localSize, struct FieldType *fields)
{
    this->next = registered;
    registered = this;

    this->name = name;
    this->localSize = localSize;
    this->fields = fields;

    this->fieldCount = 0;
    this->module = 0;
    this->type = 0;
    this->size = 0;
    this->temp = NULL;
}

HRESULT StructType::InitializeRegistered()
{
    if (TargetMachine == IMAGE_FILE_MACHINE_I386) {
        ThreadContextFields = X86ThreadContextFields;
        ThreadFields = X86ThreadFields;
        ExtVerb("Selected X86 fields.\n");
    }
    else if (TargetMachine == IMAGE_FILE_MACHINE_AMD64) {
        ThreadContextFields = X64ThreadContextFields;
        ThreadFields = X64ThreadFields;
        ExtVerb("Selected X64 fields.\n");
    }
    else if (TargetMachine == IMAGE_FILE_MACHINE_ARM) {
        ThreadContextFields = ArmThreadContextFields;
        ThreadFields = ArmThreadFields;
        ExtVerb("Selected Arm fields.\n");
    }
    else {
        ExtErr("Selected *NO* fields. [target:%08x]\n", TargetMachine);
    }

    // kernel name is potentially fixed up in StructType::Initialize
    ThreadContextStruct = new StructType(kernel_ThreadContext,
                                         sizeof(ThreadContext),
                                         ThreadContextFields);

    // kernel name is potentially fixed up in StructType::Initialize
    ThreadStruct = new StructType(kernel_Thread,
                                  sizeof(Thread),
                                  ThreadFields);

    for (StructType *next = registered; next != NULL; next = next->next) {
        next->Initialize();
    }
    return S_OK;
}

HRESULT StructType::Initialize()
{
    HRESULT status = S_OK;

    ExtVerb("Initializing: %s [%p]\n", name, fields);
    EXT_CHECK(g_ExtSymbols->GetSymbolTypeId(name, &type, &module));
    EXT_CHECK(g_ExtSymbols->GetTypeSize(module, type, &size));
    ExtVerb("Initializing: %s [size=%d]\n", name, size);
    if (temp != NULL) {
        delete[] temp;
    }
    temp = new BYTE [size];
    ZeroMemory(temp, size);

    fieldCount = 0;
    for (FieldType *field = fields; field->name != NULL; field++) {
        CHAR fieldName[512];

        EXT_CHECK(StringCbPrintf(fieldName, sizeof(fieldName), "%s.%s", name, field->name));
        status = g_ExtSymbols->GetSymbolTypeId(fieldName, &field->type, &field->module);
        if (status == S_OK) {
            EXT_CHECK(g_ExtSymbols->GetTypeSize(field->module, field->type, &field->size));
            EXT_CHECK(g_ExtSymbols->GetFieldOffset(module, type, field->name, &field->offset));
            ExtVerb("Initializing: %s [offset=%d,size=%d]\n", fieldName, field->offset, field->size);
        }
        else {
            ExtErr("Can't find: %s\n", fieldName);
            field->size = 0;
            field->offset = 0;
        }

        field->parent = this;
        fieldCount++;
    }

  Exit:
    ExtVerb("** Exited with %08x\n", status);
    return status;
}

HRESULT StructType::RemoteOffsetFromLocal(ULONG localOffset, ULONG *remoteOffset)
{
    for (ULONG f = 0; f < fieldCount; f++) {
        FieldType *field = &fields[f];

        if (field->localOffset == localOffset) {
            if (remoteOffset != NULL) {
                *remoteOffset = field->offset;
                return S_OK;
            }
            return S_FALSE;
        }
    }
    return E_FAIL;
}

HRESULT StructType::RawAccess(ULONG remoteOffset, PVOID *raw)
{
    *raw = temp + remoteOffset;
    return S_OK;
}

HRESULT StructType::Read(ULONG64 address, PVOID local)
{
    HRESULT status = S_OK;

    ZeroMemory(temp, size);
    ZeroMemory(local, localSize);

    EXT_CHECK(TraceRead(address, temp, size));

    for (ULONG f = 0; f < fieldCount; f++) {
        FieldType *field = &fields[f];

        PBYTE pbLocal = ((PBYTE)local) + field->localOffset;
        PBYTE pbTemp = &temp[field->offset];

        switch (field->size) {
          case 1:
            *(ULONG64 *)pbLocal = *(BYTE *)pbTemp;
            break;
          case 2:
            *(ULONG64 *)pbLocal = *(USHORT *)pbTemp;
            break;
          case 4:
            *(ULONG64 *)pbLocal = *(ULONG *)pbTemp;
            break;
          case 8:
            *(ULONG64 *)pbLocal = *(ULONG64 *)pbTemp;
            break;
          default:
#if 0
              // We allow bigger sizes, for raw access only.
            ExtOut("Unknown size: %d, in field %s\n", field->size, field->name);
#endif
            break;
        }
    }

  Exit:
    return status;
}

HRESULT StructType::Clear()
{
    HRESULT status = S_OK;

    ZeroMemory(temp, size);

    return status;
}

HRESULT StructType::Update(PVOID local)
{
    HRESULT status = S_OK;

    for (ULONG f = 0; f < fieldCount; f++) {
        FieldType *field = &fields[f];

        PBYTE pbLocal = ((PBYTE)local) + field->localOffset;
        PBYTE pbTemp = &temp[field->offset];

        switch (field->size) {
          case 1:
            *(BYTE *)pbTemp = (BYTE)*(ULONG64 *)pbLocal;
            break;
          case 2:
            *(USHORT *)pbTemp = (USHORT)*(ULONG64 *)pbLocal;
            break;
          case 4:
            *(ULONG *)pbTemp = (ULONG)*(ULONG64 *)pbLocal;
            break;
          case 8:
            *(ULONG64 *)pbTemp = *(ULONG64 *)pbLocal;
            break;
        }
    }

    return status;
}

HRESULT StructType::Flush(ULONG64 address)
{
    HRESULT status = S_OK;

    EXT_CHECK(g_ExtData->WriteVirtual(address, temp, size, NULL));

  Exit:
    return status;
}

/////////////////////////////////////////////////////////// KnownStructOutput.
//
const char* KnownStructs[] = {"String",
                              "Thread",
                              "System_String",
                              "System_Threading_Thread",
#if 0
                              "ProcessorContext",
                              "Microsoft_Singularity_X86_ProcessorContext"
#endif
};

HRESULT OnGetKnownStructNames(PDEBUG_CLIENT client,
                              PSTR buffer,
                              PULONG bufferSize)
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    //
    // Return names of known structs in multi string
    //
    ULONG sizeRemaining = *bufferSize, SizeNeeded = 0, Length;
    PCHAR copyAt = buffer;

    for (ULONG i = 0; i < arrayof(KnownStructs); i++) {
        if (sizeRemaining > (Length = (ULONG)strlen(KnownStructs[i]) + 1) &&
            status == S_OK) {
            status = StringCbCopy(copyAt, sizeRemaining, KnownStructs[i]);

            sizeRemaining -= Length;
            copyAt += Length;
        }
        else {
            status = S_FALSE;
        }
        SizeNeeded += Length;
    }
    // Terminate multistring and return size copied
    *copyAt = 0;
    *bufferSize = SizeNeeded+1;

    EXT_LEAVE();    // Macro includes: return status;
}

HRESULT OnGetSingleLineOutput(PDEBUG_CLIENT client,
                              ULONG64 address,
                              PSTR structName,
                              PSTR buffer,
                              PULONG bufferSize)
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;

    ExtVerb("OnGetSingleLineOutput [%s]\n", structName);

    if (strcmp(structName, "System_String") == 0 ||
        strcmp(structName, "String") == 0) {
        String str;
        ExtVerb("OnGetSingleLineOutput [%s] is string\n", structName);
        EXT_CHECK(StringStruct.Read(address, &str));
        ExtVerb("OnGetSingleLineOutput [%s] is still string\n", structName);

        WCHAR data[256];
        ULONG len;

        len = (ULONG)str.m_stringLength;
        if (len > arrayof(data)) {
            len = arrayof(data);
        }
        if (len > *bufferSize - 20) {
            len = *bufferSize - 20;
        }

        if (len > 0) {
            EXT_CHECK(TraceRead(address + StringFields[0].offset,
                                data,
                                sizeof(data[0]) * len));
            ExtVerb("OnGetSingleLineOutput [%s] read %d of %d chars to %p\n",
                    structName, len, *bufferSize, buffer);
        }

        status = StringCbPrintf(buffer, *bufferSize, " { [%d] \"%.*ls\" }",
                                (ULONG)str.m_stringLength, len, data);
        ExtVerb("OnGetSingleLineOutput [%s] status = %x\n",
                structName, status);
    }
    else if (!strcmp(structName, "System_Threading_Thread") ||
             !strcmp(structName, "Thread")) {
        Thread thread;
        EXT_CHECK(ThreadStruct->Read(address, &thread));

        status = StringCbPrintf(buffer, *bufferSize, " { eip=%I64x ebp=%I64x esp=%I64x }",
                                thread.context.threadRecord.spill.ip,
                                thread.context.threadRecord.spill.bp,
                                thread.context.threadRecord.spill.sp);
    }
#if 0
    else if (!strcmp(structName, "Microsoft_Singularity_ProcessorContext") ||
             !strcmp(structName, "ProcessorContext")) {
        ProcessorContext pc;
        EXT_CHECK(ProcessorContext.Read(address, &pc));

        status = StringCbPrintf(buffer, *bufferSize, " { eip=%I64x ebp=%I64x esp=%I64x }",
                                thread.context.threadRecord.spill.ip,
                                thread.context.threadRecord.spill.bp,
                                thread.context.threadRecord.spill.sp);
    }
#endif
    else {
        status = E_INVALIDARG;
    }

    EXT_LEAVE();    // Macro includes: return status;
}

HRESULT OnGetSuppressTypeName(PDEBUG_CLIENT client, PSTR structName)
{
    UNREFERENCED_PARAMETER(structName);

    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    EXT_LEAVE();    // Macro includes: return status;
}
