////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using System;
using Microsoft.Singularity.V1.Services;
using Microsoft.Contracts;
using Microsoft.Singularity.Channels;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
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

        [BoolParameter( "set", Default=false, HelpMessage="Run set test.")]
        internal bool doSetTest;

        reflective internal Parameters();

        internal int AppMain() {
            return Collect.AppMain(this);
        }
    }

    public class Collect
    {
        class LinkedList
        {
            private LinkedList next;
            private LinkedList prev;
            public int value;
            private byte[]! data;

            private LinkedList(int i, [Delayed] LinkedList _prev)
            {
                prev = _prev;
                value = i;

                if (i <= 1) {
                    next = null;
                }
                else {
                    next = new LinkedList(i - 1, this);
                }
                data = new byte [24576 + 1024 * i];
            }

            ~LinkedList()
            {
                DebugStub.Print("Finalizer called for Value={0}.\n", __arglist(value));
            }

            public void Print()
            {
                Console.WriteLine("Print {0}", value);
            }

            public void PrintNext()
            {
                Console.WriteLine("Linked Data: [{0} items]", value);
                PrintNext(value);
            }

            private void PrintNext(int _value)
                requires next != null;
            {
                Console.WriteLine("  Value = {0} [Next] {1}, {2} bytes payload",
                    value, next.value, data.Length);
                if (next.value != _value) {
                    next.PrintNext(_value);
                }
            }

            public void PrintPrev()
            {
                Console.WriteLine("PrintPrev {0}", value);
                PrintPrev(value);
            }

            private void PrintPrev(int _value)
                requires prev != null;
            {
                Console.WriteLine("  Value = {0} [Prev] {1}", value, prev.value);
                if (prev.value != _value) {
                    prev.PrintPrev(_value);
                }
            }

            private LinkedList! Last()
            {
                if (next != null) {
                    return next.Last();
                }
                return this;
            }

            public static LinkedList! CreateCycle(int links)
            {
                LinkedList root = new LinkedList(links, null);
                LinkedList last = root.Last();

                root.prev = last;
                last.next = root;

                return root;
            }
        }

        internal static int AppMain(Parameters! config)
        {
            LinkedList root = LinkedList.CreateCycle(4);
            root.PrintNext();
            root = null;

            Console.WriteLine();

            Console.WriteLine("Collecting garbage [before heap: {0,8} bytes]",
                GC.GetTotalMemory(false));
            GC.Collect();
            Console.WriteLine("Collecting garbage [after heap:  {0,8} bytes]",
                GC.GetTotalMemory(false));
            return 0;
        }
    }
}
