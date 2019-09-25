// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#include "singx86.h"

struct ByteVector {
    ULONG64 ulDataOffset;
    ULONG64 ulDataLength;
};

EXT_DECL(bytev) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER(); // Defines: HRESULT status = S_OK;

    if (!isalpha(args[0])) {
        ExtOut("Usage:\n    !bytev <var>\n");
        goto Exit;
    }

    ULONG64 indirect = 0;
    EXT_CHECK(g_ExtSymbols->GetOffsetByName(args, &indirect));

    ULONG64 offset = 0;
    EXT_CHECK(TraceReadPointer(1, indirect, &offset));

    // Add type check here.
    ULONG typeId;
    ULONG64 module;
    EXT_CHECK(g_ExtSymbols->GetSymbolTypeId(args, &typeId, &module));

    CHAR szTypeName[255];
    const SIZE_T cbTypeName = sizeof(szTypeName) / sizeof(szTypeName[0]);
    EXT_CHECK(g_ExtSymbols->GetTypeName(module, typeId,
                                        szTypeName, cbTypeName, NULL));

    const CHAR szExpected[] = "unsigned char**";
    const SIZE_T cbExpected = sizeof(szExpected) / sizeof(szExpected[0]);
    if (strncmp(szTypeName, szExpected, cbExpected)) {
        ExtOut("%s is not a byte vector.\n", args);
        goto Exit;
    }

    struct ByteVector bv;
    EXT_CHECK(TraceReadPointer(2, offset, (PULONG64)&bv));
    ExtOut("Byte vector %s : address 0x%p length 0x%p\n",
           args, bv.ulDataOffset, bv.ulDataLength);
    EXT_LEAVE();
}
