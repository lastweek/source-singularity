// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

int main ()
{
    __asm {
        //call printhellomp;
        // myloop: jmp myloop;
        // jmp mydone;
        //printhellomp:
        mov   ebx, 0xb8000;
        add   ebx, 7680;
        mov   [ebx+0], 0x0020;
        mov   [ebx+1], 0x00e0;
        mov   [ebx+2], 0x0048;
        mov   [ebx+3], 0x00e0;
        mov   [ebx+4], 0x0069;
        mov   [ebx+5], 0x00e0;
        mov   [ebx+6], 0x0021;
        mov   [ebx+7], 0x00e0;
        mov   [ebx+8], 0x0020;
        mov   [ebx+9], 0x00e0;
        // ret;
        // mydone:
    }
    // return 0x9876543;
}
