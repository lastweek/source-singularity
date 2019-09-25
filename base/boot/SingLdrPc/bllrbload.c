//
//
//

#define NULL    0

typedef unsigned char       byte;
typedef unsigned short      ushort;
typedef unsigned int        uint;
typedef unsigned __int64    ulong;

#pragma pack(1)

typedef struct _GDTR {
    ushort  Limit;
    ulong   Base;
} GDTR, *PGDTR;

#pragma pack()

static ushort * pVideoBeg = (ushort *)0xb8000;
static ushort * pVideoEnd = (ushort *)0xb8fa0;
static ushort * pCursor;
static ushort wColor;

static byte * pTarget = (byte *) 0x7c00;
static char szHexDigits[] = "0123456789abcdef";

extern ulong BlMmGetCr3(void);
extern void BlMmSetCr3(ulong Value);
extern void BlMmGetGdtr(PGDTR Gdtr);
extern void BlMmSetGdtr(PGDTR Gdtr);
extern ulong BlMmGetRsp(void);


//
// Include: byte lomem_data[];
//
#include <singlrb.cpp>

void PrintChar(char c)
{
    if (c == '\n') {
        while (((pCursor - pVideoBeg) % 80) != 0) {
            *pCursor++ = wColor + ' ';
        }
    }
    else if (c == '\f') {
        while (pCursor > pVideoBeg) {
            *--pCursor = wColor + ' ';
        }
    }
    else {
        *pCursor++ = wColor + c;
    }
}

void PrintString(const char * psz)
{
    for (; *psz; psz++) {
        PrintChar(*psz);
    }
}

void PrintHexValueSub(ulong v, int digits)
{
    int i;
    for (i = 4 * (digits - 1); i >= 0; i -= 4) {
        *pCursor++ = wColor + szHexDigits[(v >> i) & 0xf];
    }
}

void PrintHex32(uint v)
{
    PrintHexValueSub((ulong)v, 8);
}

void PrintHexValue(ulong v)
{
    PrintHexValueSub(v, 16);
}

void PrintHexDigit(byte v)
{
    *pCursor++ = wColor + szHexDigits[(v >> 4) & 0xf];
    *pCursor++ = wColor + szHexDigits[v & 0xf];
}

void PrintDump(byte * data, int size, int pad)
{
    for (; size > 0; size--, pad--) {
        PrintHexDigit(*data++);
    }
    for (; pad > 0; pad--) {
        PrintString("  ");
    }
}

void PrintChars(byte * data, int size, int pad)
{
    for (; size > 0; size--, pad--) {
        byte b = *data++;
        if (b < ' ' || b > 127) {
            PrintChar('.');
        }
        else {
            PrintChar((char)b);
        }
    }
    for (; pad > 0; pad--) {
        PrintString(" ");
    }
}

int FindEntry(const byte *data, int size)
{
    const byte * walk = data;

    for (; size > 0; size--, walk++) {
        if (walk[0] == 'S' && walk[1] == 'I' && walk[2] == 'N' && walk[3] == 'G' &&
            walk[4] == 'L' && walk[5] == 'R' && walk[6] == 'B' && walk[7] == 0x00 &&
            walk[8] == 0xf8 && walk[9] == 0xf9 && walk[10] == 0xfa && walk[11] == 0xfb &&
            walk[12] == 0xfc && walk[13] == 0xfd && walk[14] == 0xfe && walk[15] == 0xff) {
            return ((walk + 32) - data);
        }
    }
    return -1;
}

void CopyMemory(byte * target, const byte * data, int size)
{
    PrintString("CopyMemory(");
    PrintHexValue((ulong)target);
    PrintString(",");
    PrintHexValue((ulong)data);
    PrintString(",");
    PrintHexValue((ulong)size);
    PrintString(")\n");

    for (; size > 0; size--) {
        *target++ = *data++;
    }
}

void PrintSegment32(ulong seg)
{
    PrintString("        ");
    PrintHexValueSub(seg >> 56, 2);
    PrintHexValueSub(seg >> 16, 6);
    PrintString(" ");
    PrintHexValueSub(seg >> 48, 1);
    PrintHexValueSub(seg >> 0, 4);
    PrintString(" ");
    PrintHexValueSub(seg >> 52, 1);
    PrintString(" ");
    PrintHexValueSub(seg >> 40, 2);
}

void PrintSegment64(ulong seg0, ulong seg1)
{
    PrintHexValueSub(seg1 >> 0, 8);
    PrintHexValueSub(seg0 >> 56, 2);
    PrintHexValueSub(seg0 >> 16, 6);
    PrintString(" ");
    PrintHexValueSub(seg0 >> 48, 1);
    PrintHexValueSub(seg0 >> 0, 4);
    PrintString(" ");
    PrintHexValueSub(seg0 >> 52, 1);
    PrintString(" ");
    PrintHexValueSub(seg0 >> 40, 2);
}

void * FindModuleInfo(uint *pConfig, uint find, uint * pSize)
{
    for (;;) {
        uint type = pConfig[0];
        uint size = pConfig[1];
        void *data = &pConfig[2];

        if (type == 0) {
            *pSize = 0;
            return NULL;
        }
        if (type == find) {
            *pSize = size;
            return data;
        }
        size = (size + 8 + 7) & ~7u;

        pConfig = (uint *)(((byte *)pConfig) + size);
    }
}

void PrintModuleInfo(uint *pConfig)
{
    PrintString("Module Info:\n");
    for (;;) {
        uint type = pConfig[0];
        uint size = pConfig[1];
        void *data = &pConfig[2];

        if (type == 0) {
            break;
        }

        PrintString("  ");
        PrintHex32((uint)pConfig);
        PrintString(":");
        PrintHex32(type);
        PrintString("[");
        PrintHex32(size);
        PrintString("]:");
        PrintDump((byte*)data, size < 16 ? size : 16, 16);
        PrintString(" ");
        PrintChars((byte*)data, size < 16 ? size : 16, 16);
        PrintString("\n");

        size = (size + 8 + 7) & ~7u;

        pConfig = (uint *)(((byte *)pConfig) + size);
    }
}

void __fastcall main(uint *pConfig, uint * pUnknown)
{
    int offset;
    void (*pStart)(void);
    byte * pbSmap;
    uint cbSmap;

    wColor = 0x4f00;
    pCursor = pVideoBeg;

    PrintString("Singularity Reloader " __DATE__ " " __TIME__ "\n");

    offset = FindEntry(lomem_data, sizeof(lomem_data));
    pStart = (void (*)(void))(pTarget + offset);

    PrintString("pConfig    = ");
    PrintHexValue((ulong)pConfig);
    PrintString("\n");
    PrintString("pUnknown   = ");
    PrintHexValue((ulong)pUnknown);
    PrintString("\n");
    PrintString("    ");
    PrintDump((byte*)pUnknown, 16, 16);
    PrintString(" ");
    PrintChars((byte*)pUnknown, 16, 16);
    PrintString("\n");
    PrintString("pTarget    = ");
    PrintHexValue((ulong)pTarget);
    PrintString("..");
    PrintHexValue((ulong)(pTarget + sizeof(lomem_data)));
    PrintString("\n");

    // PrintModuleInfo(pConfig);

#if 0
    PrintString("lomem      = ");
    PrintHexValue((ulong)lomem_data);
    PrintString("..");
    PrintHexValue((ulong)(lomem_data + sizeof(lomem_data)));
    PrintString("\n");
#endif

#if 0
    {
        ulong cr3;
        ulong *p;
        GDTR gdt;

        cr3 = BlMmGetCr3();
        PrintString("cr3        = ");
        PrintHexValue((ulong)cr3);
        PrintString("\n");
        p = (ulong *)cr3;
        PrintString("cr3.0      = ");
        PrintHexValue((ulong)p[0]);
        PrintString(" ");
        PrintHexValue((ulong)p[1]);
        PrintString(" ");
        PrintHexValue((ulong)p[2]);
        PrintString(" ");
        PrintHexValue((ulong)p[3]);
        PrintString("\n");

        p = (ulong *)(p[0] & 0xfffffffffffff000);
        PrintString("cr3.0.0    = ");
        PrintHexValue((ulong)p[0]);
        PrintString(" ");
        PrintHexValue((ulong)p[1]);
        PrintString(" ");
        PrintHexValue((ulong)p[2]);
        PrintString(" ");
        PrintHexValue((ulong)p[3]);
        PrintString("\n");

        p = (ulong *)(p[0] & 0xfffffffffffff000);
        PrintString("cr3.0.0.0  = ");
        PrintHexValue((ulong)p[0]);
        PrintString(" ");
        PrintHexValue((ulong)p[1]);
        PrintString(" ");
        PrintHexValue((ulong)p[2]);
        PrintString(" ");
        PrintHexValue((ulong)p[3]);
        PrintString("\n");

        p = (ulong *)cr3;
        p = (ulong *)(p[0] & 0xfffffffffffff000);
        p = (ulong *)(p[3] & 0xfffffffffffff000);
        PrintString("cr3.0.3.0  = ");
        PrintHexValue((ulong)p[0]);
        PrintString(" ");
        PrintHexValue((ulong)p[1]);
        PrintString(" ");
        PrintHexValue((ulong)p[2]);
        PrintString(" ");
        PrintHexValue((ulong)p[3]);
        PrintString("\n");

        BlMmGetGdtr(&gdt);
#if 0
        PrintString("gdt        = ");
        PrintHexValue((ulong)gdt.Base);
        PrintString("..");
        PrintHexValue((ulong)gdt.Limit);
        PrintString("\n");
#endif
        p = (ulong *)gdt.Base;

        PrintString("gdt.1      = ");
        PrintSegment32(p[1]);
        PrintString(" : ");
        PrintSegment64(p[1],p[2]);
        PrintString("\n");

        PrintString("gdt.2      = ");
        PrintSegment32(p[2]);
        PrintString(" : ");
        PrintSegment64(p[2],p[3]);
        PrintString("\n");

        PrintString("gdt.3      = ");
        PrintSegment32(p[3]);
        PrintString(" : ");
        PrintSegment64(p[3],p[4]);
        PrintString("\n");

        PrintString("gdt.4      = ");
        PrintSegment32(p[4]);
        PrintString(" : ");
        PrintSegment64(p[4],p[5]);
        PrintString("\n");

        PrintString("gdt.5      = ");
        PrintSegment32(p[5]);
        PrintString(" : ");
        PrintSegment64(p[5],p[6]);
        PrintString("\n");

        PrintString("gdt.6      = ");
        PrintSegment32(p[6]);
        PrintString(" : ");
        PrintSegment64(p[6],p[7]);
        PrintString("\n");

        PrintString("gdt.7      = ");
        PrintSegment32(p[7]);
        PrintString(" : ");
        PrintSegment64(p[7],p[8]);
        PrintString("\n");

        PrintString("gdt.8      = ");
        PrintSegment32(p[8]);
        PrintString(" : ");
        PrintSegment64(p[8],p[9]);
        PrintString("\n");

        PrintString("gdt.9      = ");
        PrintSegment32(p[9]);
        PrintString(" : ");
        PrintSegment64(p[9],p[10]);
        PrintString("\n");

        PrintString("gdt.a      = ");
        PrintSegment32(p[10]);
        PrintString(" : ");
        PrintSegment64(p[10],p[11]);
        PrintString("\n");
    }
#endif

    CopyMemory(pTarget, lomem_data, sizeof(lomem_data));

    pbSmap = (byte *)FindModuleInfo(pConfig, 0x9001, &cbSmap);
    if (pbSmap != NULL) {
        byte * pnew = (byte *)0x1000;
        CopyMemory(pnew, pbSmap, cbSmap);
        pbSmap = pnew;
    }

    for (offset = 0; offset < cbSmap; offset += 20) {
        PrintString("    SMAP[");
        PrintHexDigit((byte)(offset / 20));
        PrintString("] ");
        PrintHexValue(((ulong *)(pbSmap + offset + 0))[0]);
        PrintString(" x ");
        PrintHexValue(((ulong *)(pbSmap + offset + 8))[0]);
        PrintString(" ");
        PrintHex32(((uint *)(pbSmap + offset + 16))[0]);
        PrintString("\n");
    }

    ((uint *)pStart)[-4] = 0x600000;
    ((uint *)pStart)[-3] = (uint)pbSmap;
    ((uint *)pStart)[-2] = cbSmap;
    PrintString("pbSmap     = ");
    PrintHexValue((ulong)pbSmap);
    PrintString("\n");

    PrintString("pTarget    = ");
    PrintHexValue((ulong)pTarget);
    PrintString(" [");
    PrintDump((byte *)pTarget, 16, 16);
    PrintString("]\n");

    PrintString("pStart     = ");
    PrintHexValue((ulong)(pStart));
    PrintString(" [");
    PrintDump((byte *)pStart, 16, 16);
    PrintString("]\n");

#if 0
    {
        byte * pb = (byte *)0x600000;
        int bad = 0;
        int i;

        PrintString("Scanning:\n");
        for (i = 0; i < 0x800000; i++) {
            if (pb[i] != 0xee) {
                PrintString("   ");
                PrintHexValue((ulong)i);
                PrintString(": ");
                PrintDump(pb, i, 16);
                PrintString("\n");
                i += 16;
                bad++;
                if (bad > 20) {
                    for (;;);
                }
            }
        }
    }
#endif

#if 0
    PrintString("Test1\n");
    {
        uint target = 0x500000;
        uint offset;

        for (offset = 1; offset < 0x10000000; offset <<= 1) {
            PrintString("  ");
            PrintHex32(target + offset);
            PrintString(" : ");
            *((uint *)(target + offset)) = (0xff000000 | offset);
            PrintHex32(*((uint *)(target + offset)));
            PrintString("\n");
        }
    }
    PrintString("Test2\n");
    for(;;);
#endif

    pStart();

    PrintString("Halt.\n");

    for (;;);

    // pStart();
}
