/////////////////////////////////////////////////////////////////////////////
//
//  apic.cpp - Extension to inspect APIC
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

#include "singx86.h"

inline static ULONG ApicRead32(const BYTE* apic, int offsetInBytes)
{
    return ((ULONG*) apic)[offsetInBytes / sizeof(ULONG)];
}

inline static BYTE ApicRead8(const BYTE* apic, int offsetInBytes)
{
    return apic[offsetInBytes];
}

inline static const char* TimerMode(ULONG flag)
{
    return (flag == 0) ? "One-shot" : "Periodic";
}

inline static const char* Mask(ULONG flag)
{
    return (flag == 0) ? "Unmasked" : "Masked  ";
}

inline static const char* TriggerMode(ULONG pmask, ULONG flag)
{
    if ((pmask & (1 << 15)) == 0)
        return "-----";
    return (flag == 0) ? "Edge " : "Level";
}

inline static const char* RemoteIRR(ULONG pmask, ULONG flag)
{
    if ((pmask & (1 << 14)) == 0)
        return "------";
    return (flag == 0) ? "No IRR" : "IRR   ";
}

inline static const char* PinPolarity(ULONG pmask, ULONG flag)
{
    if ((pmask & (1 << 13)) == 0)
        return "---------";
    return (flag == 0) ? "Active-Hi" : "Active-Lo";
}

inline static const char* DeliveryStatus(ULONG flag)
{
    return (flag == 0) ? "Idle" : "Pend";
}

inline static const char* DeliveryMode(ULONG pmask, ULONG value)
{
    if ((pmask & 0x700) == 0)
        return "---";
    const char * dm[8] = {
        "Fix", "Res", "SMI", "Res", "NMI", "INI", "Res", "Ext"
    };
    value = (value & 0x700u) >> 8;
    return dm[value];
}

static void DumpTimer(ULONG t)
{
    ExtOut("Timer:  %08x => Vector %02x ", t & 0x310ff, t & 0xff);
    ExtOut("%s %s %s\n", Mask(t & 0x10000), TimerMode(t & 0x20000),
           DeliveryStatus(t & 0x1000));
}

static void DumpLvt(const char* name, ULONG pmask, ULONG value)
{
    ExtOut("%s:  %08x => Vector %02x ", name, value & pmask, value & 0xff);
    ExtOut("%s  %s  %s  %s  %s  %s\n",
           Mask(value), TriggerMode(pmask, value),
           RemoteIRR(pmask, value), PinPolarity(pmask, value),
           DeliveryStatus(value), DeliveryMode(pmask, value));
}

static void DumpBits(const char* name, const BYTE* apic, int startOffset)
{
    ExtOut("%s: ", name);
    for (int w = 0; w < 8; w++)
    {
        ULONG bits = ApicRead32(apic, startOffset + w * 16);
        for (int i = 0; i < 32; i++)
        {
            if ((bits & (1 << i)) != 0)
            {
                ExtOut("0x%02x ", w * 32 + i);
            }
        }
    }
    ExtOut("\n");
}

EXT_DECL(apic) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    UNREFERENCED_PARAMETER(args);

    static const ULONG64 ApicBase = 0x00000000fee00000;
    BYTE apic[0x400];

    EXT_CHECK(g_ExtData->ReadPhysical(ApicBase, &apic, sizeof(apic), NULL));

    int maxLvt = ApicRead8(apic, 0x32);

    ExtOut("Apic Id %u Version %02x Max LVT %u\n",
           ApicRead8(apic, 0x23), ApicRead8(apic, 0x30), maxLvt);
    ExtOut("TPR %08x APR %08x PPR %08x\n",
           ApicRead32(apic, 0x80), ApicRead32(apic, 0x90),
           ApicRead32(apic, 0xa0));
    ExtOut("Logical Destination %08x Destination Format %08x\n",
           ApicRead32(apic, 0xd0), ApicRead32(apic, 0xe0));
    ExtOut("Spurious Interrupt Vector %08x\n", ApicRead32(apic, 0xf0));
    ExtOut("Fault Status %02x\n", ApicRead8(apic, 0x280));

    DumpTimer(ApicRead32(apic, 0x320));
    DumpLvt("LINT0", 0x1f7ff, ApicRead32(apic, 0x350));
    DumpLvt("LINT1", 0x1f7ff, ApicRead32(apic, 0x360));
    DumpLvt("Fault", 0x110ff, ApicRead32(apic, 0x370));

    if (maxLvt >= 4)
        DumpLvt("Perf ", 0x117ff, ApicRead32(apic, 0x340));

    if (maxLvt >= 5)
        DumpLvt("Therm", 0x117ff, ApicRead32(apic, 0x343));

    DumpBits("ISR", apic, 0x100);
    DumpBits("IRR", apic, 0x200);
    DumpBits("TMR", apic, 0x180);

    EXT_LEAVE();
}
