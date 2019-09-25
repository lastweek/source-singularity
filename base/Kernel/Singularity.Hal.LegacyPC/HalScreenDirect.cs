///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   HalScreenDirect.cs
//
//  Note:
//    The Indispensable PC Hardware Book (Third Edition), pp1055-1066.

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
    // declare resources for the kernel manifest
    [DriverCategory]
    public sealed class HalScreenResources : DriverCategoryDeclaration
    {
        [IoFixedPortRange(Base = 0x03d4, Length = 0x01, Shared = true)]
        public IoPortRange indexPort;

        [IoFixedPortRange(Base = 0x03d5, Length = 0x01, Shared = true)]
        public IoPortRange dataPort;

        [IoFixedMemoryRange(Base = 0xb8000, Length = 8000, Shared = true)]
        public IoMemoryRange screenMemory;

        // TODO: how can we represent endpoints here?
        //[ServiceEndpoint(typeof(ConsoleDeviceContract.Exp),
        //                 CustomName = "HalScreen")]
        //TRef<ServiceProviderContract.Exp:Start> conoutsp;
    }

    [CLSCompliant(false)]
    public class HalScreenDirect : HalScreen
    {
        public const int Columns    = 80;
        public const int Rows       = 50;
        public const int ScreenSize = Columns * Rows;

        public const ushort CGA_INDEX_PORT = 0x3d4;
        public const ushort CGA_DATA_PORT  = 0x3d5;
        public const byte SmallCursorStart = 6;
        public const byte LargeCursorStart = 0;

        private enum Coloring
        {
            Dim     = 0x1700,
            Yellow  = 0x1e00,
            Green   = 0x1a00,
            Red     = 0x1c00,
            Normal  = 0x1f00
        }

        private ushort color           = (ushort)Coloring.Normal;
        private int    cursor          = 0;
        private bool   cursorVisible   = false;
        private byte   cursorStartLine = SmallCursorStart;

        private const byte CGA_CURSOR_START = 0xa;
        private const byte CGA_CURSOR_MSB   = 0xe;
        private const byte CGA_CURSOR_LSB   = 0xf;

        private IoPort indexRegister = null;
        private IoPort dataRegister = null;
        private IoMemory screenBuffer = null;

        public HalScreenDirect(IoConfig config)
        {
            indexRegister =
                ((IoPortRange) config.FixedRanges[0]).PortAtOffset(
                    0, 1, Access.Write);
            dataRegister =
                ((IoPortRange) config.FixedRanges[1]).PortAtOffset(
                    0, 1, Access.Write);
            screenBuffer =
                ((IoMemoryRange) config.FixedRanges[2]).MemoryAtOffset(
                    0, ScreenSize * 2, Access.ReadWrite);
            Clear();
            WriteLine("Singularity HAL Console Driver.");
            UpdateCursor(true);
        }

        public HalScreenDirect()
        {
            // For compatibility with .csi compiled file
            DebugStub.Break();
        }

        [NoHeapAllocation]
        public void Dim()
        {
            color = (ushort)Coloring.Dim;
        }

        [NoHeapAllocation]
        public void Yellow()
        {
            color = (ushort)Coloring.Yellow;
        }

        [NoHeapAllocation]
        public void Green()
        {
            color = (ushort)Coloring.Green;
        }

        [NoHeapAllocation]
        public void Red()
        {
            color = (ushort)Coloring.Red;
        }

        [NoHeapAllocation]
        public void Normal()
        {
            color = (ushort)Coloring.Normal;
        }

        [NoHeapAllocation]
        public override void CursorFlash()
        {
            ushort was;

            screenBuffer.Read16NoThrow(0, out was);
            was &= (ushort)0xff00;
            screenBuffer.Write16NoThrow(0, was);
        }

        [NoHeapAllocation]
        public override void CursorHide()
        {
            UpdateCursor(false);
        }

        [NoHeapAllocation]
        public override void CursorShow()
        {
            UpdateCursor(true);
        }

        [NoHeapAllocation]
        public override void Clear()
        {
            if (screenBuffer == null) {
                DebugStub.Break();
                return;
            }
            ushort zip = (ushort)(color | ' ');
            IoResult result = screenBuffer.Write16NoThrow(0, zip, ScreenSize);
            DebugStub.Assert(IoResult.Success == result);

            cursor = 0;
            UpdateCursor(cursorVisible);
        }

        [NoHeapAllocation]
        public override void GetDisplayDimensions(out int columns, out int rows)
        {
            columns = Columns;
            rows    = Rows;
        }

        [NoHeapAllocation]
        public override void GetCursorPosition(out int column, out int row)
        {
            column = cursor % Columns;
            row    = cursor / Columns;
        }

        [NoHeapAllocation]
        public override void SetCursorSizeLarge()
        {
            cursorStartLine = LargeCursorStart;
            ForcedCursorUpdate();
        }

        [NoHeapAllocation]
        public override void SetCursorSizeSmall()
        {
            cursorStartLine = SmallCursorStart;
            ForcedCursorUpdate();
        }

        [NoHeapAllocation]
        private void ForcedCursorUpdate()
        {
            bool saved      = cursorVisible;
            cursorVisible   = !cursorVisible;
            UpdateCursor(saved);
        }

        [NoHeapAllocation]
        private void UpdateCursor(bool newVisibleState)
        {
            IoResult result;

            if (newVisibleState != cursorVisible) {
                byte cgaStart = 32; // Cursor off
                if (newVisibleState) {
                    cgaStart = (byte)(64 + cursorStartLine);  // Cursor on
                }

                result = indexRegister.Write8NoThrow(CGA_CURSOR_START);
                DebugStub.Assert(IoResult.Success == result);

                result = dataRegister.Write8NoThrow(cgaStart);
                DebugStub.Assert(IoResult.Success == result);

                cursorVisible = newVisibleState;
            }

            if (newVisibleState) {
                // Write cursor location
                result = indexRegister.Write8NoThrow(CGA_CURSOR_MSB);
                DebugStub.Assert(IoResult.Success == result);
                result = dataRegister.Write8NoThrow((byte)(cursor >> 8));
                DebugStub.Assert(IoResult.Success == result);
                result = indexRegister.Write8NoThrow(CGA_CURSOR_LSB);
                DebugStub.Assert(IoResult.Success == result);
                result = dataRegister.Write8NoThrow((byte)(cursor & 0xff));
                DebugStub.Assert(IoResult.Success == result);
            }
        }

        [NoHeapAllocation]
        public override bool SetCursorPosition(int column, int row)
        {
            if (column < 0 || column >= Columns ||
                row < 0 || row >= Rows) {
                return false;
            }
            cursor = column + row * Columns;
            UpdateCursor(cursorVisible);
            return true;
        }

        [NoHeapAllocation]
        public override void ClearCursorToEndOfLine()
        {
            // Writing to the screen is slow.  We might
            // want to track how many characters are written per line
            // to speed this up.
            int column = cursor % Columns;
            int row    =  cursor / Columns;
            while (column != Columns) {
                PutCharAt(' ', column++, row);
            }
        }

        [NoHeapAllocation]
        public override bool PutCharAt(char c, int column, int row)
        {
            if (column < 0 || column >= Columns ||
                row < 0 || row >= Rows) {
                return false;
            }
            int offset = (column + row * Columns) * 2;
            IoResult result = screenBuffer.Write16NoThrow(offset,
                                                          (ushort)(color | c));
            DebugStub.Assert(IoResult.Success == result);
            return true;
        }

        [NoHeapAllocation]
        public override void PutChar(char c)
        {
            PutChar((byte)c);
        }

        [NoHeapAllocation]
        public void PutChar(byte c)
        {
            if (screenBuffer == null) {
                return;
            }

            if (c == (byte)'\b') {
                cursor--;
            }
            else if (c == (byte)'\r') {
                int left = Columns - (cursor % Columns);

                cursor -= cursor % Columns;
            }
            else if (c == (byte)'\n') {
                cursor += Columns - (cursor % Columns);
            }
            else {
                IoResult result =
                    screenBuffer.Write16NoThrow(cursor++ * 2,
                                                (ushort)(color | (c & 0x7f)));
                DebugStub.Assert(IoResult.Success == result);
            }

            if (cursor >= ScreenSize) {
                IoResult result;
                // Scroll up 1-line
                result = screenBuffer.Copy8NoThrow(Columns * 2, 0,
                                                   (ScreenSize - Columns) * 2);
                DebugStub.Assert(IoResult.Success == result);
                // Blank bottom line
                result =
                    screenBuffer.Write16NoThrow((ScreenSize - Columns) * 2,
                                                (ushort)(color | ' '),
                                                Columns);
                DebugStub.Assert(IoResult.Success == result);
                // Reel in cursor
                cursor -= Columns;
            }

            UpdateCursor(cursorVisible);
        }

        [NoHeapAllocation]
        public override void Write(byte[] buffer, int offset, int count)
        {
            for (int i = 0; i < count; i++) {
                PutChar(buffer[offset + i]);
            }
        }

        private void WriteLine(String value)
        {
            for (int i = 0; i < value.Length; i++) {
                PutChar((byte)value[i]);
            }
            PutChar((byte)'\r');
            PutChar((byte)'\n');
        }
    }
} // namespace Microsoft.Singularity.Hal
