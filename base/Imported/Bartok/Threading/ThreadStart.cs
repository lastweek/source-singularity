// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==
/*=============================================================================
**
** Class: ThreadStart
**
** Purpose: This class is a Delegate which defines the start method
**  for starting a thread.  That method must match this delegate.
**
=============================================================================*/

namespace System.Threading
{
    using System.Runtime.CompilerServices;
    using System.Threading;

    // Define the delegate
    // NOTE: If you change the signature here, there is code in COMSynchronization
    //  that invokes this delegate in native.
    //| <include path='docs/doc[@for="ThreadStart"]/*' />
    [RequiredByBartok]
    public delegate void ThreadStart();
}
