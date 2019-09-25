// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

namespace System
{
    public enum ProcessExitCode : int
    {
        Success = 0,
        ErrorDefault = -1,
        MainMax = 0x3fffffff,
        MainMin = -0x3fffffff,
        StopMax = -0x7fff0000,
        StopMin = Int32.MinValue,
        StopDefault = StopMin,
    }
}
