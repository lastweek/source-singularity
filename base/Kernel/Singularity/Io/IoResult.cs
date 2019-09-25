///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   IoStatusCode.cs
//
//  Note:
//

using System;

namespace Microsoft.Singularity.Io
{
    public enum IoResult : int
    {
        Success           = 0,
        ReadNotSupported  = 1,
        WriteNotSupported = 2,
        AccessOutOfRange  = 4,
    }
}
