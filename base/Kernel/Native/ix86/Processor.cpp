////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Processor.cpp
//
//  Note:
//

#include "hal.h"

#if SINGULARITY_KERNEL
#include "halkd.h"
#endif // SINGULARITY_KERNEL

/////////////////////////////////////////////////////////// Segment Selectors.
//
#define SEGMENT_SELECTOR(s) \
    (uint16)(offsetof(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt,s) \
             - offsetof(Struct_Microsoft_Singularity_Isal_IX_DescriptorTable_Gdt,nul))

/////////////////////////////////////////////////////////// Processor Context.
//
Class_Microsoft_Singularity_Processor *
Struct_Microsoft_Singularity_ProcessorContext::
m_GetProcessor(Struct_Microsoft_Singularity_ProcessorContext *self)
{
    return (Class_Microsoft_Singularity_Processor *) self->_processor;
}

void
Struct_Microsoft_Singularity_ProcessorContext::
m_UpdateAfterGC(Struct_Microsoft_Singularity_ProcessorContext * self,
                Class_Microsoft_Singularity_Processor *processor)
{
    self->_processor = processor;
}


//////////////////////////////////////////////////////////////////////////////
//

#if SINGULARITY_KERNEL

#if PAGING
extern void FakeSyscall();
#endif

void ProcessorInitialize(Class_Microsoft_Singularity_Hal_Cpu *pCpu)
{
    // The ProcessorContext can be found at a published offset in FS.  The DS-based address of this
    // context is available in the hal processor record

    Struct_Microsoft_Singularity_ProcessorContext *proc
      = (Struct_Microsoft_Singularity_ProcessorContext *) pCpu->CpuRecordPage;

    proc->halCpu = pCpu;

#if PAGING
    // XXX PBAR Set up MSRs for SYSENTER/SYSEXIT
    Class_Microsoft_Singularity_Isal_Isa::g_WriteMsr(0x174, SEGMENT_SELECTOR(pc));
    Class_Microsoft_Singularity_Isal_Isa::g_WriteMsr(0x175, proc->cpuRecord.interruptStackBegin + 0x2000);
    Class_Microsoft_Singularity_Isal_Isa::g_WriteMsr(0x176, (UINT64)FakeSyscall);
#endif
}

#endif // SINGULARITY_KERNEL

//
///////////////////////////////////////////////////////////////// End of File.
