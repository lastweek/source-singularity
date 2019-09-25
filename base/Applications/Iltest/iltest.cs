////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   This file contains the main entry point for the C#
//          portion of Singularity.
//

using Microsoft.Singularity.V1.Services;
using System;
using System.Runtime.CompilerServices;
using System.Threading;

namespace Microsoft.Singularity
{
    [CCtorIsRunDuringStartup]
    public class Iltest
    {
#if TEST_MEMORY_ABI
        public static uint Probe(uint addr)
        {
            uint begin;
            uint bytes;
            bool used = PageTableService.Query(addr, out begin, out bytes);
            DebugService.Print(' ');
            DebugService.Print((ulong)begin);
            DebugService.Print('.');
            DebugService.Print((ulong)begin + bytes);
            DebugService.Print(' ');
            if (used) {
                DebugService.Print('u');
            }
            DebugService.Print('\n');
            return begin + bytes;
        }
#endif // TEST_MEMORY_ABI

        public static int ThreadMain(int threadIndex)
        {
            DebugService.Print('t');
            DebugService.Print(threadIndex);
            DebugService.Print('\n');
#if TEST_STACK_ABI
            Test1(1);
#endif // TEST_STACK_ABI
            DebugService.Print('.');
            return 998;
        }

        public static int Main()
        {
            int i = 10;
            long l = 100;
            byte b = 1;
            bool o = true;

            DebugService.Print('H');
            DebugService.Print(b);
            DebugService.Print(',');
            DebugService.Print(i);
            DebugService.Print(',');
            DebugService.Print(l);
            DebugService.Print(',');
            DebugService.Print(o);
            DebugService.Print('\n');

#if TEST_MEMORY_ABI
            uint tag = PageTableService.GetProcessTag();
            DebugService.Print('p');
            DebugService.Print((ulong)tag);
            DebugService.Print('\n');

            uint pages = PageTableService.GetPageCount();
            DebugService.Print('n');
            DebugService.Print(pages);
            DebugService.Print('\n');

            uint addr = PageTableService.Allocate(0x1000);
            DebugService.Print('a');
            DebugService.Print((ulong)addr);
            DebugService.Print('\n');

            Probe(addr);

            addr = 1;
            for (i = 0; i < 20 && addr != 0 && addr < 0xc0000000; i++) {
                addr = Probe(addr);
            }
#endif // TEST_MEMORY_ABI
#if TEST_STACK_ABI
            Test1(1);
#endif // TEST_STACK_ABI

            return 999;
        }

#if TEST_STACK_ABI
        [NoInline]
        internal static int Test1(int a)
        {
            DebugService.Print('1');
            DebugService.Print('('); DebugService.Print(a);
            DebugService.Print(')');
            a = Test2(a, a + 1) + 1;
            DebugService.Print('=');
            DebugService.Print(a);
            DebugService.Print('\n');
            return a;
        }

        [NoInline]
        internal static int Test2(int a, int b)
        {
            DebugService.Print('2');
            DebugService.Print('('); DebugService.Print(a);
            DebugService.Print(','); DebugService.Print(b);
            DebugService.Print(')');
            a = Test3(a, a + 1, a + 2) + 1;
            DebugService.Print('=');
            DebugService.Print(a);
            DebugService.Print('\n');
            return a;
        }

        [NoInline]
        internal static int Test3(int a, int b, int c)
        {
            DebugService.Print('3');
            DebugService.Print('('); DebugService.Print(a);
            DebugService.Print(','); DebugService.Print(b);
            DebugService.Print(','); DebugService.Print(c);
            DebugService.Print(')');
            a = Test4(a, a + 1, a + 2, a + 3) + 1;
            DebugService.Print('=');
            DebugService.Print(a);
            DebugService.Print('\n');
            return a;
        }

        [NoInline]
        internal static int Test4(int a, int b, int c, int d)
        {
            DebugService.Print('4');
            DebugService.Print('('); DebugService.Print(a);
            DebugService.Print(','); DebugService.Print(b);
            DebugService.Print(','); DebugService.Print(c);
            DebugService.Print(','); DebugService.Print(d);
            DebugService.Print(')');
            a = Test5(a, a + 1, a + 2, a + 3, a + 4) + 1;
            DebugService.Print('=');
            DebugService.Print(a);
            DebugService.Print('\n');
            return a;
        }

        [NoInline]
        internal static int Test5(int a, int b, int c, int d, int e)
        {
            DebugService.Print('5');
            DebugService.Print('('); DebugService.Print(a);
            DebugService.Print(','); DebugService.Print(b);
            DebugService.Print(','); DebugService.Print(c);
            DebugService.Print(','); DebugService.Print(d);
            DebugService.Print(','); DebugService.Print(e);
            DebugService.Print(')');
            a = Test6(a, a + 1, a + 2, a + 3, a + 4, a + 5) + 1;
            DebugService.Print('=');
            DebugService.Print(a);
            DebugService.Print('\n');
            return a;
        }

        [NoInline]
        internal static int Test6(int a, int b, int c, int d, int e, int f)
        {
            DebugService.Print('6');
            DebugService.Print('('); DebugService.Print(a);
            DebugService.Print(','); DebugService.Print(b);
            DebugService.Print(','); DebugService.Print(c);
            DebugService.Print(','); DebugService.Print(d);
            DebugService.Print(','); DebugService.Print(e);
            DebugService.Print(','); DebugService.Print(f);
            DebugService.Print(')');
            a = a + 100;
            DebugService.WalkStack();
            DebugService.Print('=');
            DebugService.Print(a);
            DebugService.Print('\n');
            return a;
        }
#endif // TEST_STACK_ABI
    }
}
