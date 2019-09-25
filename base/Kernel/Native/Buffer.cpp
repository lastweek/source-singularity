////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Buffer.cpp
//
//  Note:   Kernel & Process
//

#include "hal.h"

#if ISA_IX86 || ISA_IX64
void Class_System_Buffer::g_MoveMemory(uint8* dmem, uint8* smem, int size)
{
    if (size % 64 == 0 && size >= 64 && (uintptr)dmem % 64 == 0 && (uintptr)smem % 64 == 0) {
        g_CopyPages(dmem, smem, size);
        return;
    }

    if (dmem <= smem) {
        // make sure the destination is dword aligned
        while ((((int)dmem ) & 0x3) != 0 && size >= 3) {
            *dmem++ = *smem++;
            size -= 1;
        }

        // copy 16 bytes at a time
        if (size >= 16) {
            size -= 16;
            do {
                ((int *)dmem)[0] = ((int *)smem)[0];
                ((int *)dmem)[1] = ((int *)smem)[1];
                ((int *)dmem)[2] = ((int *)smem)[2];
                ((int *)dmem)[3] = ((int *)smem)[3];
                dmem += 16;
                smem += 16;
            }
            while ((size -= 16) >= 0);
        }

        // still 8 bytes or more left to copy?
        if ((size & 8) != 0) {
            ((int *)dmem)[0] = ((int *)smem)[0];
            ((int *)dmem)[1] = ((int *)smem)[1];
            dmem += 8;
            smem += 8;
        }

        // still 4 bytes or more left to copy?
        if ((size & 4) != 0) {
            ((int *)dmem)[0] = ((int *)smem)[0];
            dmem += 4;
            smem += 4;
        }

        // still 2 bytes or more left to copy?
        if ((size & 2) != 0) {
            ((short *)dmem)[0] = ((short *)smem)[0];
            dmem += 2;
            smem += 2;
        }

        // still 1 byte left to copy?
        if ((size & 1) != 0) {
            dmem[0] = smem[0];
            dmem += 1;
            smem += 1;
        }
    } else {
        smem += size;
        dmem += size;

        // make sure the destination is dword aligned
        while ((((int)dmem) & 0x3) != 0 && size >= 3) {
            *--dmem = *--smem;
            size -= 1;
        }

        // copy 16 bytes at a time
        if (size >= 16) {
            size -= 16;
            do {
                dmem -= 16;
                smem -= 16;
                ((int *)dmem)[3] = ((int *)smem)[3];
                ((int *)dmem)[2] = ((int *)smem)[2];
                ((int *)dmem)[1] = ((int *)smem)[1];
                ((int *)dmem)[0] = ((int *)smem)[0];
            }
            while ((size -= 16) >= 0);
        }

        // still 8 bytes or more left to copy?
        if ((size & 8) != 0) {
            dmem -= 8;
            smem -= 8;
            ((int *)dmem)[1] = ((int *)smem)[1];
            ((int *)dmem)[0] = ((int *)smem)[0];
        }

        // still 4 bytes or more left to copy?
        if ((size & 4) != 0) {
            dmem -= 4;
            smem -= 4;
            ((int *)dmem)[0] = ((int *)smem)[0];
        }

        // still 2 bytes or more left to copy?
        if ((size & 2) != 0) {
            dmem -= 2;
            smem -= 2;
            ((short *)dmem)[0] = ((short *)smem)[0];
        }

        // still 1 byte left to copy?
        if ((size & 1) != 0) {
            dmem -= 1;
            smem -= 1;
            dmem[0] = smem[0];
        }
    }
}

void Class_System_Buffer::g_ZeroMemory(uint8* dmem, int size)
{
    // Align dmem to 8-bytes for g_ZeroPages
    while ((((int)dmem) & 0x7) != 0 && size > 0) {
        *dmem++ = 0;
        size   -= 1;
    }

    if (size >= 64) {
        // g_ZeroPages expects 8-byte alignment and a block size of n*64 bytes.
        int toZero = size & ~63;
        g_ZeroPages(dmem, toZero);
        dmem += toZero;
        size -= toZero;
    }

    if (size >= 16) {
        size -= 16;
        do {
            ((int*)dmem)[0] = 0;
            ((int*)dmem)[1] = 0;
            ((int*)dmem)[2] = 0;
            ((int*)dmem)[3] = 0;
            dmem += 16;
        } while ((size -= 16) >= 0);
    }
    if ((size & 8) > 0) {
        ((int*)dmem)[0] = 0;
        ((int*)dmem)[1] = 0;
        dmem += 8;
    }
    if ((size & 4) > 0) {
        ((int*)dmem)[0] = 0;
        dmem += 4;
    }
    if ((size & 2) != 0) {
        ((short*)dmem)[0] = 0;
        dmem += 2;
    }
    if ((size & 1) != 0) {
        *dmem++ = 0;
    }
}
#endif

//
///////////////////////////////////////////////////////////////// End of File.
