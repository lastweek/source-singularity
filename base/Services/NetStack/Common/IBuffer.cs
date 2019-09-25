// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using System.Collections;
using System.Diagnostics;
using System;

using Drivers.Net;

namespace NetStack.Common
{
    public interface IBuffer
    {
        int Available { get; }

        bool Read8(out byte x);
        bool ReadNet16(out ushort x);
        bool ReadNet32(out uint x);
        bool ReadNet64(out ulong x);
        bool ReadBytes(byte []! buf, int index, int count);
        bool ReadEthernetAddress(out EthernetAddress addr);
        bool ReadZeroTerminatedString(out string s);

        byte PeekAvailable(int offset);
    }
} // namespace Drivers.Net
