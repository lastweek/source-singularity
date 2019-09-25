////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   This file contains the main entry point for the C#
//          portion of Singularity.
//

//#define TEST_MEMORY_ABI 1
//#define TEST_STACK_ABI 1

using Microsoft.Singularity.V1.Services;
using System;
using System.Runtime.CompilerServices;
using System.Threading;

namespace Microsoft.Singularity
{
    [CCtorIsRunDuringStartup]
    public class Nulltest
    {
#if TEST_MEMORY_ABI
        public static uint Probe(uint addr)
        {
            uint begin;
            uint bytes;
            bool used = PageTableService.Query(addr, out begin, out bytes);
            DebugStub.Print("   ");
            DebugStub.Print((ulong)begin);
            DebugStub.Print("..");
            DebugStub.Print((ulong)begin + bytes);
            DebugStub.Print("  ");
            if (used) {
                DebugStub.Print("[used]");
            }
            DebugStub.Print("\n");
            return begin + bytes;
        }
#endif // TEST_MEMORY_ABI

        public static int ThreadMain(int threadIndex)
        {
            DebugStub.Print("Hello from NullTest::ThreadMain(threadIndex=");
            DebugStub.Print(threadIndex);
            DebugStub.Print(")\n");
#if TEST_STACK_ABI
            Test1(1);
#endif // TEST_STACK_ABI
            DebugStub.Print("Exiting.\n");
            return 998;
        }

        public static int Main()
        {
#if TEST_CONSOLE
            int i = 10;
            long l = 100;
            byte b = 1;
            bool o = true;
#endif
            DebugStub.Print("Hello from NullTest::Main\n");
#if TEST_CONSOLE
            DebugStub.Print(b);
            DebugStub.Print("\n");
            DebugStub.Print(i);
            DebugStub.Print("\n");
            DebugStub.Print(l);
            DebugStub.Print("\n");
            DebugStub.Print(o);
            DebugStub.Print("\n");
#endif

#if TEST_MEMORY_ABI
            uint tag = PageTableService.GetProcessTag();
            DebugStub.Print("Process Tag: ");
            DebugStub.Print((ulong)tag);
            DebugStub.Print("\n");

            uint pages = PageTableService.GetPageCount();
            DebugStub.Print("Pages:       ");
            DebugStub.Print(pages);
            DebugStub.Print("\n");

            uint addr = PageTableService.Allocate(0x1000);
            DebugStub.Print("Allocation:  ");
            DebugStub.Print((ulong)addr);
            DebugStub.Print("\n");

            Probe(addr);

            addr = 1;
            for (i = 0; i < 20 && addr != 0 && addr < 0xc0000000; i++) {
                addr = Probe(addr);
            }
#endif // TEST_MEMORY_ABI
#if TEST_STACK_ABI
            Test1(1);
#endif // TEST_STACK_ABI

            return 0;
        }

#if TEST_STACK_ABI
        [NoInline]
        internal static int Test1(int a)
        {
            DebugStub.Print("[Test1. ");
            DebugStub.Print("("); DebugStub.Print(a);
            DebugStub.Print(")\n");
            a = Test2(a, a + 1) + 1;
            DebugStub.Print(".Test1] = ");
            DebugStub.Print(a);
            DebugStub.Print("\n");
            return a;
        }

        [NoInline]
        internal static int Test2(int a, int b)
        {
            DebugStub.Print("[Test2. ");
            DebugStub.Print("("); DebugStub.Print(a);
            DebugStub.Print(","); DebugStub.Print(b);
            DebugStub.Print(")\n");
            a = Test3(a, a + 1, a + 2) + 1;
            DebugStub.Print(".Test2] = ");
            DebugStub.Print(a);
            DebugStub.Print("\n");
            return a;
        }

        [NoInline]
        internal static int Test3(int a, int b, int c)
        {
            DebugStub.Print("[Test3. ");
            DebugStub.Print("("); DebugStub.Print(a);
            DebugStub.Print(","); DebugStub.Print(b);
            DebugStub.Print(","); DebugStub.Print(c);
            DebugStub.Print(")\n");
            a = Test4(a, a + 1, a + 2, a + 3) + 1;
            DebugStub.Print(".Test3] = ");
            DebugStub.Print(a);
            DebugStub.Print("\n");
            return a;
        }

        [NoInline]
        internal static int Test4(int a, int b, int c, int d)
        {
            DebugStub.Print("[Test4. ");
            DebugStub.Print("("); DebugStub.Print(a);
            DebugStub.Print(","); DebugStub.Print(b);
            DebugStub.Print(","); DebugStub.Print(c);
            DebugStub.Print(","); DebugStub.Print(d);
            DebugStub.Print(")\n");
            a = Test5(a, a + 1, a + 2, a + 3, a + 4) + 1;
            DebugStub.Print(".Test4] =");
            DebugStub.Print(a);
            DebugStub.Print("\n");
            return a;
        }

        [NoInline]
        internal static int Test5(int a, int b, int c, int d, int e)
        {
            DebugStub.Print("[Test5. ");
            DebugStub.Print("("); DebugStub.Print(a);
            DebugStub.Print(","); DebugStub.Print(b);
            DebugStub.Print(","); DebugStub.Print(c);
            DebugStub.Print(","); DebugStub.Print(d);
            DebugStub.Print(","); DebugStub.Print(e);
            DebugStub.Print(")\n");
            a = Test6(a, a + 1, a + 2, a + 3, a + 4, a + 5) + 1;
            DebugStub.Print(".Test5] = ");
            DebugStub.Print(a);
            DebugStub.Print("\n");
            return a;
        }

        [NoInline]
        internal static int Test6(int a, int b, int c, int d, int e, int f)
        {
            DebugStub.Print("[Test6. ");
            DebugStub.Print("("); DebugStub.Print(a);
            DebugStub.Print(","); DebugStub.Print(b);
            DebugStub.Print(","); DebugStub.Print(c);
            DebugStub.Print(","); DebugStub.Print(d);
            DebugStub.Print(","); DebugStub.Print(e);
            DebugStub.Print(","); DebugStub.Print(f);
            DebugStub.Print(")\n");
            a = a + 100;
            DebugStub.WalkStack();
            DebugStub.Print(".Test6] = ");
            DebugStub.Print(a);
            DebugStub.Print("\n");
            return a;
        }
#endif // TEST_STACK_ABI
    }
}
