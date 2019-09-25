///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   HalScreenNull.cs
//
//
using System;
using System.Runtime.CompilerServices;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;

[assembly: System.Reflection.AssemblyVersionAttribute("1.0.0.0")]
[assembly: System.Reflection.AssemblyKeyFileAttribute(@"..\public.snk")]
[assembly: System.Reflection.AssemblyDelaySignAttribute(true)]

namespace Microsoft.Singularity.Hal
{
    [CLSCompliant(false)]
    public class HalScreenNull : HalScreen
    {
        public HalScreenNull(IoConfig config)
        {
        }

        [NoHeapAllocation]
        public override void CursorFlash()
        {
        }

        [NoHeapAllocation]
        public override void CursorHide()
        {
        }

        [NoHeapAllocation]
        public override void CursorShow()
        {
        }

        [NoHeapAllocation]
        public override void Clear()
        {
        }

        [NoHeapAllocation]
        public override void GetDisplayDimensions(out int columns, out int rows)
        {
            columns = 1;
            rows = 1;
        }

        [NoHeapAllocation]
        public override void GetCursorPosition(out int column, out int row)
        {
            column = 0;
            row = 0;
        }

        [NoHeapAllocation]
        public override void SetCursorSizeLarge()
        {
        }

        [NoHeapAllocation]
        public override void SetCursorSizeSmall()
        {
        }

        [NoHeapAllocation]
        public override bool SetCursorPosition(int column, int row)
        {
            return true;
        }

        [NoHeapAllocation]
        public override void ClearCursorToEndOfLine()
        {
        }

        [NoHeapAllocation]
        public override bool PutCharAt(char c, int column, int row)
        {
            return true;
        }

        [NoHeapAllocation]
        public override void PutChar(char c)
        {
        }

        [NoHeapAllocation]
        public override void Write(byte[] buffer, int offset, int count)
        {
        }
    }
} // namespace Microsoft.Singularity.Hal
