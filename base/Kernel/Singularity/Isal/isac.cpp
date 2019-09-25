/////////////////////////////////////////////////////////////////////////////////////////////////
//
// Microsoft Research Singularity
//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//
// Native code for Isa class

#include "hal.h"

#if ISA_IX

#if SINGULARITY_KERNEL
void Class_Microsoft_Singularity_Isal_Isa::g_Halt(void)
{
    __halt();
}

void Class_Microsoft_Singularity_Isal_Isa::g_EnableInterrupts(void)
{
    _enable();
}

bool Class_Microsoft_Singularity_Isal_Isa::g_DisableInterrupts(void)
{
    bool enabled = (__readeflags() & Struct_Microsoft_Singularity_Isal_IX_EFlags_IF) != 0;
    _disable();
    return enabled;
}

bool Class_Microsoft_Singularity_Isal_Isa::g_AreInterruptsDisabled(void)
{
    return (__readeflags() & Struct_Microsoft_Singularity_Isal_IX_EFlags_IF) == 0;
}

void Class_Microsoft_Singularity_Isal_Isa::g_EnablePaging(uint32 pdpt)
{
    // use the pdpt argument directly as the cr3 value. This leaves
    // top-level write-through and cache-disable turned off.
    __writecr3(pdpt);

    uintptr cr0 = __readcr0();
    cr0 |= Struct_Microsoft_Singularity_Isal_IX_CR0_WP;
    cr0 |= Struct_Microsoft_Singularity_Isal_IX_CR0_PG;
    __writecr0(cr0);
}

void Class_Microsoft_Singularity_Isal_Isa::g_ChangePageTableRoot(uint32 pdpt)
{
    __writecr3(pdpt);
}

void Class_Microsoft_Singularity_Isal_Isa::g_DisablePaging()
{
    // Turn off paging.
    uintptr cr0 = __readcr0();
    cr0 &= ~Struct_Microsoft_Singularity_Isal_IX_CR0_WP;
    cr0 &= ~Struct_Microsoft_Singularity_Isal_IX_CR0_PG;
    __writecr0(cr0);

    // Flush and reset the TLB.
    __writecr3(0);
}

void Class_Microsoft_Singularity_Isal_Isa::g_InvalidateTLBEntry(UIntPtr pageAddr)
{
    __invlpg((void *) pageAddr);
}

UIntPtr Class_Microsoft_Singularity_Isal_Isa::g_GetPageTableRoot()
{
    return (UIntPtr) __readcr3();
}

#endif //SINGULARITY_KERNEL

void Class_Microsoft_Singularity_Isal_Isa::g_WriteMsr(uint32 reg, uint64 value)
{
    __writemsr(reg, value);
}

uint64 Class_Microsoft_Singularity_Isal_Isa::g_ReadMsr(uint32 reg)
{
    return __readmsr(reg);
}

void Class_Microsoft_Singularity_Isal_Isa::g_RepInS(uint32 count, uint16 port, uint8 *address)
{
    __inbytestring(port, address, count);
}

void Class_Microsoft_Singularity_Isal_Isa::g_RepOutS(uint32 count, uint16 port, uint8 *address)
{
    __outbytestring(port, address, count);
}

void Class_Microsoft_Singularity_Isal_Isa::g_Out(uint16 port, int value)
{
    __outdword(port, value);
}

uint64 Class_Microsoft_Singularity_Isal_Isa::g_GetCycleCount(void)
{
    return __rdtsc();
}

uint64 Class_Microsoft_Singularity_Isal_Isa::g_ReadPmc(uint32 offset)
{
    return __readpmc(offset);
}

void Class_Microsoft_Singularity_Isal_Isa::g_ReadCpuid(uint32 feature, 
                                                       uint32 *v0, uint32 *v1, 
                                                       uint32 *v2, uint32 *v3)
{
    int params[4];

    __cpuid(params, feature);

    *v0 = params[0];
    *v1 = params[1];
    *v2 = params[2];
    *v3 = params[3];
}

UIntPtr Class_Microsoft_Singularity_Isal_Isa::g_GetFrameReturnAddress(UIntPtr frame)
{
    if (frame < (UIntPtr)0x10000) {
        return 0;
    }
    return ((UIntPtr*)frame)[1];
}

UIntPtr Class_Microsoft_Singularity_Isal_Isa::g_GetFrameCallerFrame(UIntPtr frame)
{
    if (frame < (UIntPtr)0x10000) {
        return 0;
    }
    return ((UIntPtr*)frame)[0];
}

UIntPtr Class_Microsoft_Singularity_Isal_Isa::g_GetStackPointer()
{
    return (UIntPtr) _AddressOfReturnAddress();
}

#endif // ISA_IX
