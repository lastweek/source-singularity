////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Thread.cpp
//
//  Note:
//

#include "hal.h"

////////////////////////////////////////////////////////////// Thread Context.
//
void
Struct_Microsoft_Singularity_ThreadContext::
m_UpdateAfterGC(Struct_Microsoft_Singularity_ThreadContext * self,
                Class_System_Threading_Thread *thread)
{
    self->_thread = thread;
}

Class_System_Threading_Thread *
Struct_Microsoft_Singularity_ThreadContext::
m_GetThread(Struct_Microsoft_Singularity_ThreadContext * self)
{
    return (Class_System_Threading_Thread *) self->_thread;
}

#if SINGULARITY_KERNEL
void
Struct_Microsoft_Singularity_ThreadContext::
m_Initialize(Struct_Microsoft_Singularity_ThreadContext * self,
             int threadIndex,
             UIntPtr stackBegin,
             uint32 cr3)
{
    Struct_Microsoft_Singularity_Isa_SpillContext::m_Initialize(&self->threadRecord.spill, 
                                          stackBegin, 
                                          (UIntPtr) self->stackLimit,
                                          (UIntPtr)Class_System_Threading_Thread::g_ThreadStub,
                                          threadIndex, 
                                          (UIntPtr) cr3);
}

void
Struct_Microsoft_Singularity_ThreadContext::
m_InitializeIdle(Struct_Microsoft_Singularity_ThreadContext * self,
                 int threadIndex,
                 UIntPtr stackBegin,
                 uint32 cr3)
{
    Struct_Microsoft_Singularity_Isa_SpillContext::m_Initialize(&self->threadRecord.spill, 
                                          stackBegin,
                                          (UIntPtr) self->stackLimit,
                                          (UIntPtr)Class_System_Threading_Thread::g_DispatcherThreadStub,
                                          threadIndex, 
                                          (UIntPtr) cr3);
}
#endif // SINGULARITY_KERNEL

//
///////////////////////////////////////////////////////////////// End of File.
