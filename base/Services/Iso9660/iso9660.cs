// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using Console = System.Console;
using Environment = System.Environment;
using Exception = System.Exception;
using System;
using System.IO;
using System.Collections;
using System.Diagnostics;
using Int32 = System.Int32;
using IntPtr = System.IntPtr;
using System.Threading;
using System.Text;
using DateTime = System.DateTime;
using TimeSpan = System.TimeSpan;
using Hashtable = System.Collections.Hashtable;
using Microsoft.Singularity;

using Microsoft.SingSharp;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.V1.Services;

//
// Some utility classes and functions.
// 

namespace Iso9660
{

    public class LongId{
        public static System.Int64 New(int hi, int low){
            System.Int64 x = ((System.Int64)hi) << 32;
            return x | (0xffff & (uint)low);
        }

        public static int GetHi(long id) {
            return (int)(0xffffffff & (id >> 32));
        }

        public static int GetLo(long id) {
            return (int)(0xffffffff & id);
        }

        public static string ToString(long x) {
            return String.Format("<{0:x}:{1}>", GetHi(x), GetLo(x));
        }
    }

public class system {
    public enum MODULE : int {SYSTEM = 0, ALLOCCLERK = 1, BTREE = 2,
        NEWONES = 3};

    public class Ticks {
        long time;

        private Ticks(long t) {
            time = t;
        }

        public static bool operator <(Ticks x, Ticks y) {
            return x.time < y.time;
        }

        public static bool operator >(Ticks x, Ticks y) {
            return x.time > y.time;
        }
        public static bool operator <=(Ticks x, Ticks y) {
            return x.time <= y.time;
        }

        public static bool operator >=(Ticks x, Ticks y) {
            return x.time >= y.time;
        }

        public static Ticks Now {
            get {
                return new Ticks(DateTime.Now.Ticks);
            }
        }

        public long DurationInMSecs(Ticks t) {
            return (t.time - time + 5000)/10000;
        }

        public static Ticks Minimum {
            get {
                return new Ticks(DateTime.MinValue.Ticks);
            }
        }

        public override string! ToString() {
            DateTime d = new DateTime(this.time);
            int milliseconds = d.Millisecond;
            return (d.ToString () + ", " + milliseconds.ToString() + "ms");
            // + " ticks= " + this.time);
        }
    }

    public static void Assert(bool assertion) {
        if (!assertion) {
            DebugStub.WriteLine("assertion failure, stack trace:");
#if !SINGULARITY
            StackTrace st = new StackTrace(true);
            string stackIndent = "";
            for (int i = 0; i < st.FrameCount; i++) {
                // Low down the call stack there are four
                // stack frames, one for each method invocation.
                StackFrame sf = st.GetFrame(i);
                Console.WriteLine("\n" + stackIndent + " Method: {0}",
                                  sf.GetMethod() );
                Console.WriteLine(  stackIndent + " File: {0}", sf.GetFileName());
                Console.WriteLine(  stackIndent + " Line Number: {0}",
                                    sf.GetFileLineNumber());
                stackIndent += "  ";
            }
#endif
            DebugStub.Break();
            throw new Exception("Assertion failed");
        }
    }

    public static void panic(string s) {
        DebugStub.WriteLine("panic: {0}", __arglist(s));
        DebugStub.Break();
        throw new Exception("panic");
    }
}
}

