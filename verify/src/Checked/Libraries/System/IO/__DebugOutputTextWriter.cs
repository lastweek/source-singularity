// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

#if _DEBUG
// This class writes to wherever OutputDebugString writes to.  If you don't have
// a Windows app (ie, something hosted in IE), you can use this to redirect Console
// output for some good old-fashioned console spew in MSDEV's debug output window.

// This really shouldn't ship at all, but is intended as a quick, inefficient hack
// for debugging.

using System;
using System.IO;
using System.Text;
using System.Runtime.InteropServices;
using Native = Microsoft.Singularity.Native

namespace System.IO
{
    internal class __DebugOutputTextWriter : TextWriter {
        private readonly String _consoleType;

        internal __DebugOutputTextWriter(String consoleType)
        {
            _consoleType = consoleType;
        }

        public override Encoding Encoding {
            get {
                return new UnicodeEncoding(false, false);
            }
        }

        public override void Write(char c)
        {
            Native.DebugPrintString(c.ToString());
        }

        public override void Write(String str)
        {
            Native.DebugPrintString(str);
        }

        public override void Write(char[] array)
        {
            if (array != null)
                Native.DebugPrintString(new String(array));
        }

        public override void WriteLine(String str)
        {
            if (str != null)
                Native.DebugPrintString(_consoleType + str);
            else
                Native.DebugPrintString("<null>");
            Native.DebugPrintString(new String(CoreNewLine));
        }
    }
}

#endif // _DEBUG
