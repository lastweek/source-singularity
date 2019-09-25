// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#include "singx86.h"

struct CharVector {
    ULONG64 ulDataOffset;
    ULONG64 ulDataLength;
};

EXT_DECL(charv) // Defines: PDEBUG_CLIENT Client, PCSTR args
{
    EXT_ENTER(); // Defines: HRESULT status = S_OK;

    if (!isalpha(args[0])) {
        ExtOut("Usage:\n    !charv <var>\n");
        goto Exit;
    }

    ULONG64 indirect = 0;
    EXT_CHECK(g_ExtSymbols->GetOffsetByName(args, &indirect));

    ULONG64 offset = 0;
    EXT_CHECK(TraceReadPointer(1, indirect, &offset));

    ULONG typeId;
    ULONG64 module;
    EXT_CHECK(g_ExtSymbols->GetSymbolTypeId(args, &typeId, &module));

    CHAR szTypeName[255];
    const SIZE_T cbTypeName = sizeof(szTypeName) / sizeof(szTypeName[0]);
    EXT_CHECK(g_ExtSymbols->GetTypeName(module, typeId,
                                        szTypeName, cbTypeName, NULL));

    const CHAR   szExpected[] = "char**";
    const SIZE_T cbExpected   = sizeof(szExpected) / sizeof(szExpected[0]);
    if (strncmp(szTypeName, szExpected, cbExpected)) {
        ExtOut("%s is not a char vector.\n", args);
        goto Exit;
    }

    struct CharVector cv;
    EXT_CHECK(TraceReadPointer(2, offset, (PULONG64)&cv));

    SIZE_T cChars = (SIZE_T) cv.ulDataLength / sizeof(WCHAR);
    PWCHAR pwcText = new WCHAR[cChars + 1];
    pwcText[cChars] = UNICODE_NULL;

    HRESULT hRR =
        TraceRead(cv.ulDataOffset,
                  pwcText,
                  (ULONG)cv.ulDataLength);
    if (S_OK == hRR) {
        g_ExtControl->Output(DEBUG_OUTPUT_NORMAL,
                             "Char vector %s : address 0x%p length " \
                             "0x%p\nValue = \"",
                             args, cv.ulDataOffset,
                             (cv.ulDataLength / sizeof(WCHAR)));
        g_ExtControl->OutputWide(DEBUG_OUTPUT_NORMAL, pwcText);
        g_ExtControl->Output(DEBUG_OUTPUT_NORMAL, "\"\n");
    }
    else {
        ExtVerb("ReadVirtual failed (%p)", hRR);
    }

    delete [] pwcText;

    EXT_LEAVE();
}
