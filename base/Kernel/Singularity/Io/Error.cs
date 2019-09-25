///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Error.cs
//
//  Note:
//

using System;

namespace Microsoft.Singularity.Io
{
    internal class Error
    {
        internal static void ReadNotSupported() {
            throw new
                NotSupportedException("NotSupported_ReadOnPortOrMemory");
        }

        internal static void WriteNotSupported() {
            throw
                new NotSupportedException("NotSupported_WriteOnPortOrMemory");
        }

        internal static void AccessOutOfRange() {
            throw
                new NotSupportedException("NotSupported_AccessOutOfRange");
        }

    }
}
