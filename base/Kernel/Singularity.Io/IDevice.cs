///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IDevice.cs
//
//  Note:
//

using System;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity.Io
{
    public interface IDevice
    {
        void Initialize();
        void Finalize();
    }
} // namespace Microsoft.Singularity.Io
