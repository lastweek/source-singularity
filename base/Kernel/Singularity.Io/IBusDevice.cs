///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IBusDevice.cs
//
//  Note:
//

using System.Collections;

namespace Microsoft.Singularity.Io
{
    public interface IBusDevice : IDevice
    {
        SortedList Enumerate();
    }
}
