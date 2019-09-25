///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   FileImage.cs
//

using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Microsoft.Singularity.Io
{
    [NoCCtor]
    [CLSCompliant(false)]
    [StructLayout(LayoutKind.Sequential, Pack=4)]
    [AccessedByRuntime("referenced in c++")]
    public struct FileImage
    {
        [AccessedByRuntime("referenced in c++")]
        internal UIntPtr Address;

        [AccessedByRuntime("referenced in c++")]
        internal uint    Size;

        internal FileImage(UIntPtr address, uint size)
        {
            this.Address = address;
            this.Size    = size;
        }
    }
}
