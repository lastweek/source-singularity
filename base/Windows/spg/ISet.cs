// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;

namespace Microsoft.Singularity.Applications
{
    interface ISet : ICollection
    {
        bool Contains(Object elem);
        void Add(Object elem);
        bool ContainsAll(ISet coll);
        void AddAll(ICollection cool);
        void Remove(Object elem);
    }
}
