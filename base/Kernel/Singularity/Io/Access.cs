///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Access.cs
//

using System;

namespace Microsoft.Singularity.Io
{
    [Flags]
    public enum Access
    {
        None        = 0x00,
        Read        = 0x01,
        Write       = 0x02,
        ReadWrite   = (Read | Write),
        Execute     = 0x04,
    };
}
