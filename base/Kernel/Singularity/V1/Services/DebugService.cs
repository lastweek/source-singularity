////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity - Singularity ABI
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DebugService.cs
//
//  Note:
//

using System;
using System.Runtime.CompilerServices;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Memory;
using Microsoft.Singularity.Isal;

namespace Microsoft.Singularity.V1.Services
{
    public struct DebugService
    {
        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe void PrintBeginImpl(
            char * * buffer,
            int * length)
        {
            PrintBegin(out *buffer, out *length);
        }

        [CLSCompliant(false)]
        public static unsafe void PrintBegin(out char * buffer, out int length)
        {
            DebugStub.PrintBegin(out buffer, out length);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe void PrintComplete(char * buffer, int used)
        {
            DebugStub.PrintComplete(buffer, used);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe void Print(char * buffer)
        {
            DebugStub.Print(buffer);
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static unsafe void Print(char * buffer, int length)
        {
            DebugStub.Print(buffer, length);
        }

        [ExternalEntryPoint]
        public static void Print(bool value)
        {
            DebugStub.Print("{0}", __arglist(value));
        }

        [ExternalEntryPoint]
        public static void Print(char value)
        {
            DebugStub.Print("{0}", __arglist(value));
        }

        [ExternalEntryPoint]
        public static void Print(byte value)
        {
            DebugStub.Print("{0}", __arglist(value));
        }

        [ExternalEntryPoint]
        public static void Print(int value)
        {
            DebugStub.Print("{0}", __arglist(value));
        }

        [CLSCompliant(false)]
        [ExternalEntryPoint]
        public static void Print(uint value)
        {
            DebugStub.Print("{0}", __arglist(value));
        }

        [ExternalEntryPoint]
        public static void Print(long value)
        {
            DebugStub.Print("{0}", __arglist(value));
        }

        [CLSCompliant(false)]
        [ExternalEntryPoint]
        public static void Print(ulong value)
        {
            DebugStub.Print("{0}", __arglist(value));
        }

        [ExternalEntryPoint]
        public static void Break()
        {
            Tracing.Log(Tracing.Warning, "DebugService.Break()");
            DebugStub.Print("DebugService.Break()\n");
            DebugStub.Break();
        }

        [ExternalEntryPoint]
        public static void WalkStack()
        {
            Stacks.WalkStack(Isa.GetFramePointer());
        }

        [ExternalEntryPoint]
        public static bool IsDebuggerPresent()
        {
            return DebugStub.IsDebuggerPresent();
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static ulong ReadPerfCounter(uint which)
        {
            switch (which) {
                case 0: return DebugStub.perfCounter0;
                case 1: return DebugStub.perfCounter1;
                case 2: return DebugStub.perfCounter2;
                case 3: return DebugStub.perfCounter3;
                case 4: return DebugStub.perfCounter4;
                case 5: return DebugStub.perfCounter5;
                case 6: return DebugStub.perfCounter6;
                case 7: return DebugStub.perfCounter7;
                case 8: return DebugStub.perfCounter8;
                case 9: return DebugStub.perfCounter9;
                case 10: return DebugStub.perfCounter10;
                case 11: return DebugStub.perfCounter11;
                case 12: return DebugStub.perfCounter12;
                case 13: return DebugStub.perfCounter13;
                case 14: return DebugStub.perfCounter14;
                case 15: return DebugStub.perfCounter15;
                default: return 0;
            }
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static bool WritePerfCounter(uint which, ulong value)
        {
            switch (which) {
                case 0: DebugStub.perfCounter0 = value; return true;
                case 1: DebugStub.perfCounter1 = value; return true;
                case 2: DebugStub.perfCounter2 = value; return true;
                case 3: DebugStub.perfCounter3 = value; return true;
                case 4: DebugStub.perfCounter4 = value; return true;
                case 5: DebugStub.perfCounter5 = value; return true;
                case 6: DebugStub.perfCounter6 = value; return true;
                case 7: DebugStub.perfCounter7 = value; return true;
                case 8: DebugStub.perfCounter8 = value; return true;
                case 9: DebugStub.perfCounter9 = value; return true;
                case 10: DebugStub.perfCounter10 = value; return true;
                case 11: DebugStub.perfCounter11 = value; return true;
                case 12: DebugStub.perfCounter12 = value; return true;
                case 13: DebugStub.perfCounter13 = value; return true;
                case 14: DebugStub.perfCounter14 = value; return true;
                case 15: DebugStub.perfCounter15 = value; return true;
                default: return false;
            }
        }

        [ExternalEntryPoint]
        [CLSCompliant(false)]
        public static bool AddToPerfCounter(uint which, ulong value)
        {
            switch (which) {
                case 0: Interlocked.Add(ref DebugStub.perfCounter0, value); return true;
                case 1: Interlocked.Add(ref DebugStub.perfCounter1, value); return true;
                case 2: Interlocked.Add(ref DebugStub.perfCounter2, value); return true;
                case 3: Interlocked.Add(ref DebugStub.perfCounter3, value); return true;
                case 4: Interlocked.Add(ref DebugStub.perfCounter4, value); return true;
                case 5: Interlocked.Add(ref DebugStub.perfCounter5, value); return true;
                case 6: Interlocked.Add(ref DebugStub.perfCounter6, value); return true;
                case 7: Interlocked.Add(ref DebugStub.perfCounter7, value); return true;
                case 8: Interlocked.Add(ref DebugStub.perfCounter8, value); return true;
                case 9: Interlocked.Add(ref DebugStub.perfCounter9, value); return true;
                case 10: Interlocked.Add(ref DebugStub.perfCounter10, value); return true;
                case 11: Interlocked.Add(ref DebugStub.perfCounter11, value); return true;
                case 12: Interlocked.Add(ref DebugStub.perfCounter12, value); return true;
                case 13: Interlocked.Add(ref DebugStub.perfCounter13, value); return true;
                case 14: Interlocked.Add(ref DebugStub.perfCounter14, value); return true;
                case 15: Interlocked.Add(ref DebugStub.perfCounter15, value); return true;
                default: return false;
            }
        }
    }
}
