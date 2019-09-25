///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   HalScreen.cs
//

using System;
using System.Runtime.CompilerServices;

namespace Microsoft.Singularity.Hal
{
    public abstract class HalScreen
    {
        [NoHeapAllocation]
        public abstract void Clear();

        [NoHeapAllocation]
        public abstract void GetDisplayDimensions(out int columns, out int rows);

        [NoHeapAllocation]
        public abstract void GetCursorPosition(out int column, out int row);

        [NoHeapAllocation]
        public abstract bool SetCursorPosition(int column, int row);

        [NoHeapAllocation]
        public abstract void SetCursorSizeLarge();

        [NoHeapAllocation]
        public abstract void SetCursorSizeSmall();

        [NoHeapAllocation]
        public abstract void Write(byte[] buffer, int offset, int count);

        [NoHeapAllocation]
        public abstract void PutChar(char c);

        [NoHeapAllocation]
        public abstract bool PutCharAt(char c, int column, int row);

        [NoHeapAllocation]
        public abstract void ClearCursorToEndOfLine();

        [NoHeapAllocation]
        public abstract void CursorFlash();

        [NoHeapAllocation]
        public abstract void CursorHide();

        [NoHeapAllocation]
        public abstract void CursorShow();
    }
} // namespace Microsoft.Singularity.Hal
