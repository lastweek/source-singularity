//
// Copyright (c) Microsoft Corporation.   All rights reserved.
//

/*******************************************************************/
/*                           WARNING                               */
/* This file should be identical in the Bartok and Singularity     */
/* depots. Master copy resides in Bartok Depot. Changes should be  */
/* made to Bartok Depot and propagated to Singularity Depot.       */
/*******************************************************************/

namespace System.GCs
{

    using System.Threading;
    using System.Runtime.CompilerServices;

    internal abstract unsafe class RememberedSet
    {
        // Record a pointer fromAddr->toAddr
        internal abstract void RecordReference(ref Object reference,
                                               Object toObj);
        internal abstract void RecordReference(UIntPtr* fromAddr,
                                               Object toObj);
        internal abstract void RecordClonedObject(Object obj);
        // Clean out stale entries for all threads
        internal abstract void Clean();
        // Clean out stale entries for given thread
        internal abstract void Clean(Thread thread);
        // Visit all locations in remset
        internal abstract void Scan(NonNullReferenceVisitor visitor,
                                             PageType genToCollect);
         // Remove all entries in remset
        internal abstract void Reset();
        // Remove duplicates in remset
        internal abstract void Uniquify();
    }

}
