////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using System;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal Parameters();

        internal int AppMain() {
            return Cast.AppMain(this);
        }
    }

    public class Cast
    {
        private class CastTest
        {
            int value;
        }

        private class CastTestChild : CastTest
        {
        }

        private static bool TestIs(CastTest c)
        {
            return c is CastTestChild;
        }

        private static bool TestTypeOf(CastTest! c)
        {
            return c.GetType() == typeof(CastTestChild);
        }

        private static CastTestChild TestAs(CastTest c)
        {
            return c as CastTestChild;
        }

        private static CastTestChild TestCast(CastTest c)
        {
            return (CastTestChild)c;
        }

        //[ShellCommand("cast", "Test speed of cast operations")]
        internal static int AppMain(Parameters! config)
        {
            Console.WriteLine("CPU TSC as reference for delay yields:");

            ulong beg;
            ulong end;

            CastTest c = new CastTestChild();

            Console.Write("Testing Is:   ");
            beg = Processor.CycleCount;
            for (int i = 0; i < 1000; i++) {
                TestIs(c);
            }
            end = Processor.CycleCount;
            Console.WriteLine("{0,15}", (end - beg) / 1000);

            Console.Write("Testing Typeof:   ");
            beg = Processor.CycleCount;
            for (int i = 0; i < 1000; i++) {
                TestTypeOf(c);
            }
            end = Processor.CycleCount;
            Console.WriteLine("{0,15}", (end - beg) / 1000);

            Console.Write("Testing As:   ");
            beg = Processor.CycleCount;
            for (int i = 0; i < 1000; i++) {
                TestAs(c);
            }
            end = Processor.CycleCount;
            Console.WriteLine("{0,15}", (end - beg) / 1000);

            Console.Write("Testing Cast: ");
            beg = Processor.CycleCount;
            for (int i = 0; i < 1000; i++) {
                TestCast(c);
            }
            end = Processor.CycleCount;
            Console.WriteLine("{0,15}", (end - beg) / 1000);

            return 0;
        }
    }
}
