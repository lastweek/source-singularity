// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

using System;
using System.IO;
using System.Text;
using System.Runtime.InteropServices;

// [Bartok]:
namespace System
{
    public class __ConsoleTextWriter : TextWriter {
        public __ConsoleTextWriter()
        {
        }

        public override Encoding Encoding {
            get {
                return Encoding.Default;
            }
        }

        public override void Write(char[] buffer, int index, int count)
        {
            Console.Write(buffer, index, count);
        }

        public override void Write(String str)
        {
            Console.Write(str);
        }

        public override void WriteLine(char[] buffer, int index, int count)
        {
            Console.WriteLine(buffer, index, count);
        }

        public override void WriteLine(String str)
        {
            Console.WriteLine(str);
        }
    }
}
