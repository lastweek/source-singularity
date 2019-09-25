// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*============================================================
**
** Interface: AsyncCallbackDelegate
**
** Purpose: Type of callback for async operations
**
===========================================================*/
namespace System
{
    using System.Runtime.CompilerServices;

    //| <include path='docs/doc[@for="AsyncCallback"]/*' />
    [RequiredByBartok]
    public delegate void AsyncCallback(IAsyncResult ar);

}
