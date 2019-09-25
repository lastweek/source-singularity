///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//

using System;
using System.Text;
using System.Runtime.CompilerServices;
using Microsoft.Singularity;

namespace Microsoft.Singularity.Applications
{
    public class Breaker
    {
        private static Object ToObject(StringBuilder sb)
        {
            return (Object)sb;
        }

        public static void Break(int how)
        {
            if (how == 2) {
                Console.WriteLine("Breaking into kernel debugger with write to page zero.");
                DebugStub.WriteLine("About to write to page zero.");
                StringBuilder sb = new StringBuilder(128);
                Object o = ToObject(sb);
                unsafe {
                    byte *buffer = null;
                    *buffer = 0xff;
                }
                sb = new StringBuilder(256);
                DebugStub.WriteLine("sb={0}, o={1}", __arglist(sb, o));
            }
            else if (how == 1) {
                Console.WriteLine("Breaking into kernel debugger with read from page zero.");
                DebugStub.WriteLine("About to read from page zero.");
                StringBuilder sb = new StringBuilder(128);
                Object o = ToObject(sb);
                byte b;
                unsafe {
                    byte *buffer = null;
                    b = *buffer;
                }
                sb = new StringBuilder(256);
                DebugStub.WriteLine("sb={0}, o={1}, b={2}", __arglist(sb, o, b));
            }
            else if (how == 2) {
                Console.WriteLine("Breaking into kernel debugger.");
                DebugStub.WriteLine("About to break into kernel debugger");
                StringBuilder sb = new StringBuilder(128);
                Object o = ToObject(sb);

                DebugStub.Break();
                sb = new StringBuilder(256);
                DebugStub.WriteLine("sb={0}, o={1}", __arglist(sb, o));
            }
        }
    }
}
