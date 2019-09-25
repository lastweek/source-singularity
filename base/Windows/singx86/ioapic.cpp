/////////////////////////////////////////////////////////////////////////////
//
//  apic.cpp - Extension to inspect APIC
//
//  Copyright Microsoft Corporation.  All rights reserved.
//

#include "singx86.h"

static ULONG64 ioApicAddress;

static ULONG IoApicRead(ULONG64 ioApicAddress, ULONG regAddr)
{
    ULONG value;
    g_ExtData->WritePhysical(ioApicAddress, &regAddr, sizeof(regAddr), NULL);
    g_ExtData->ReadPhysical(ioApicAddress + 0x10, &value, sizeof(value), NULL);
    return value;
}

static const char* DeliveryMode(ULONG lo)
{
    const char* dm[8] = { "Fixed", "LowPr", "SMI  ", "Rsvd ",
                          "NMI  ", "Init ", "Rsvd ", "ExInt" };
    return dm[(lo >> 8) & 0x7];
}

static const char* Destination(ULONG hi, ULONG lo)
{
    static char buf[16];
    if (lo & 0x0f00)
    {
        sprintf(buf, "Logical:%02x", (hi >> 24) & 0xff);
    } else {
        sprintf(buf, "PhysDst:%02x", (hi >> 24) & 0x0f);
    }
    return buf;
}

static const char* TriggerMode(ULONG lo)
{
    return (lo & 0xf000) ? "lvl" : "edg";
}

static const char* Masked(ULONG lo)
{
    return (lo & 0x10000) ? "masked" : "live  ";
}

static const char* DeliveryStatus(ULONG lo)
{
    return (lo & 0x1000) ? "pend" : "idle";
}

static const char* RemoteIrr(ULONG lo)
{
    return ((lo & 0xc000) == 0xc000) ? "remote-irr" : "          ";
}

static void DumpIoApic(ULONG64 address)
{
    ULONG value = IoApicRead(address, 0x01);
    ULONG entries = (value >> 16) & 0xff;
    ExtOut("IoApic @ %08x ID: %u Version %02x\n",
           (ULONG) address,
           (IoApicRead(address, 0x02) >> 24) & 0xf,
           value & 0xff);

    for (ULONG i = 0; i <= entries; i++)
    {
        ULONG lo = IoApicRead(address, 0x10 + i * 2);
        ULONG hi = IoApicRead(address, 0x11 + i * 2);
        ExtOut("Inti%02x.: %08x  Vec:%02x  %s  %s  %s  %s  %s  %s\n",
               i, lo, lo & 0xff,
               DeliveryMode(lo), Destination(hi, lo), TriggerMode(lo),
               Masked(lo), DeliveryStatus(lo), RemoteIrr(lo));
    }
}

EXT_DECL(ioapic) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER();    // Defines: HRESULT status = S_OK;
    UNREFERENCED_PARAMETER(args);

    // XXX TODO: Get Io Apic addresses from value from MP table.
    DumpIoApic(0xfec00000);

    EXT_LEAVE();
}
