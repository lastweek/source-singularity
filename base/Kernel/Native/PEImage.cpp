////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PEImage.cpp
//
//  Note:   Kernel Only
//

#include "hal.h"

//////////////////////////////////////////////////////////////// Image Loader.
//
#if PAGING
extern int syscallEntryTable[];

struct AbiStackHead
{
    uintptr    prevBegin;
    uintptr    prevLimit;
    uintptr    esp;
};

int FakeSyscallBegin(int abiIndex)
{
    // TODO: validate abiIndex, set fs, etc.
    return syscallEntryTable[abiIndex];
}

// TODO: these cannot be functions; we cannot trust the user stack
uintptr PushAbiStack(uintptr esp)
{
    Struct_Microsoft_Singularity_ThreadContext * context =
        Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext();
    AbiStackHead *head = (AbiStackHead *)(context->abiStackHead);
    head->prevBegin = context->stackBegin;
    head->prevLimit = context->stackLimit;
    head->esp = esp;
    context->stackBegin = context->abiStackBegin;
    context->stackLimit = context->abiStackLimit;
    return uintptr(head);
}

uintptr PopAbiStack(AbiStackHead *head)
{
    Struct_Microsoft_Singularity_ThreadContext * context =
        Class_Microsoft_Singularity_Processor::g_GetCurrentThreadContext();
    // HACK: if the ABI call changed stackBegin/stackLimit, keep the changes
    // (otherwise, switch back to original stack)
    if (context->stackBegin == context->abiStackBegin) {
        context->stackBegin = head->prevBegin;
        context->stackLimit = head->prevLimit;
    }
    return head->esp;
}

//#define SEGMENT_SELECTOR(s) \
//    (uint16)(offsetof(Struct_Microsoft_Singularity_CpuInfo,s) \
//             - offsetof(Struct_Microsoft_Singularity_CpuInfo,GdtNull))
//const uint16 ourFs = SEGMENT_SELECTOR(GdtPF);

__declspec(naked) void FakeSyscall()
{
    __asm
    {
#if 0
        push ecx
        push edx
        call AbiStackSegment
        pop edx
        pop ecx
        mov esp, eax // TODO: must set stackBase, stackLimit
        push edx
        call FakeSyscallBegin
        mov edx, eax
        mov eax, [esp] // eax = pointer to arg1
        call edx
        pop ecx // ecx = pointer to arg1
        sub ecx, 4 // ecx = pointer to return address
        mov esp, ecx
        ret 8
#else
        // user stack = ret arg1 arg2 ret arg3 ... argn ...
        // ecx = ABI index
        // edx = pointer to arg1
        push ecx
        push edx
        mov ecx, edx
        sub ecx, 4 // 1 word for return address
        call PushAbiStack
        pop edx
        pop ecx
        mov esp, eax

///        mov eax, edx
///        sub eax, 4 // 1 word for return address
///        mov esp, eax
        sti
        mov ax, ss
        mov ds, ax    // Copy stack segment selector to DS so we can access memory!
        mov es, ax    // Copy stack segment selector to ES so we can access memory!
//        push    (offsetof(Struct_Microsoft_Singularity_CpuInfo,GdtPF) - offsetof(Struct_Microsoft_Singularity_CpuInfo,GdtNull))
//        push    ourFs
//        pop     fs
        mov     ax, 0x38  // TODO: no more hexadecimal constants
        mov     fs, ax
//        push    fs;
//        pop     fs;    // refresh fs (TODO: don't trust user's fs)
        push edx
        call FakeSyscallBegin
        mov edx, eax
        pop eax // pointer to arg1
        // user stack = ret arg1 arg2 ret arg3 ... argn ...
        call edx
        call Class_Microsoft_Singularity_Isal_Isa::g_EnterUserMode

        // Any changes here must be reflected in EnterRing0
        mov ecx, esp
        push eax
        push edx
        call PopAbiStack
        mov ecx, eax
        pop edx
        pop eax
        mov esp, ecx

        ret 8
#endif
    }
}
__declspec(naked) void EnterRing0()
{
    __asm
    {
        add esp, 4 // discard return address (pointing to FakeSyscall)

        // Copied from FakeSyscall epilog:
        mov ecx, esp
        push eax
        push edx
        call PopAbiStack
        mov ecx, eax
        pop edx
        pop eax
        mov esp, ecx

        ret 8
    }
}
#endif // PAGING

int32 Class_Microsoft_Singularity_Loader_PEImage::
g_HalCallEntryPoint(UIntPtr entry, int threadIndex, bool runAtRing3)
{
    if (entry == 0) {
        __debugbreak();
        return -1;
    }

#if PAGING
    if (runAtRing3) {
        Class_Microsoft_Singularity_Isal_Isa::g_EnterUserMode();
    }
#else
    Assert(!runAtRing3);
#endif

    int32 retval = (( int32 (__fastcall *)(int32))entry)(threadIndex);

#if PAGING
    if (runAtRing3) {
        // We should still be running at ring-3 when the process unwinds
        Assert(Class_Microsoft_Singularity_Isal_Isa::g_IsInUserMode());

        // Call ABI zero, which drops us to ring-0. Why is this not
        // a gaping security hole? The kernel should verify that this
        // request only ever comes from its own (trusted) code (i.e.,
        // right here).
        __asm {
            mov ecx, 0
            push ecx
            push ecx
            mov edx, esp
            push done
            _emit   0x0f
            _emit   0x34  //sysenter
done:
        }
    }
#endif

    return retval;
}

//
///////////////////////////////////////////////////////////////// End of File.
