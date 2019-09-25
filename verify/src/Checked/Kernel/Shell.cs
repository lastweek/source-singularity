//
// Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Runtime.CompilerServices;
using kernel;

public class Shell: ThreadStart
{
    KeyboardDriver keyboardDriver;
    Semaphore keyboardWaiter;
    uint offsetLo;
    uint offsetHi;
    uint offset;
    uint backgroundColor;

    public Shell(KeyboardDriver keyboardDriver, Semaphore keyboardWaiter, uint offsetLo, uint offsetHi, uint backgroundColor)
    {
        this.keyboardDriver = keyboardDriver;
        this.keyboardWaiter = keyboardWaiter;
        this.offsetLo = offsetLo;
        this.offsetHi = offsetHi;
        this.offset = offsetLo;
        this.backgroundColor = backgroundColor;
        for (uint i = offsetLo; i < offsetHi; i++)
        {
            INucleusCalls.VgaTextWrite(i, backgroundColor);
        }
    }

    public override void Run()
    {
        System.DebugStub.Print("Shell@" + Kernel.CurrentThread + ". ");
        while (true)
        {
            keyboardWaiter.Wait();
            char ch = (keyboardDriver.LastChar); // TODO: channels!

/*
            if (ch == 'a') {
                impact.othello.othello.Main(new System.String[1]{"-d"});
            } else if (ch == 'b') {
                impact.li_130.xlisp.Main(new System.String[0]);
            } else if (ch == 'c') {
                Crafty.Net.OO.Crafty.Main(new System.String[0]);
            } else if (ch == 'd') {
                SharpSAT.SATSolver.Main(new System.String[0]);
            }
*/

            INucleusCalls.VgaTextWrite(offset, backgroundColor + ch);
            offset++;
            if (offset == offsetHi) offset = offsetLo;
        }
    }
}

public class KeyboardDriver: ThreadStart
{
    Kernel kernel;
    Semaphore[] listeners;

    const int ASCII_TABLE_SIZE = 0x40;
    const int BUFFER_SIZE = 0x100;
    const int LSHIFT_SCAN = 0x2a;
    const int RSHIFT_SCAN = 0x36;
    const int CTRL_SCAN = 0x1d;
    const int ALT_SCAN = 0x38;
    const char z = (char)0;

    private bool shift = false;
    private bool ctrl = false;
    private bool alt = false;

    public volatile char LastChar; // TODO: channels!

    public KeyboardDriver(Kernel kernel, Semaphore[] listeners)
    {
        this.kernel = kernel;
        this.listeners = listeners;
    }

    static BinaryTree t;
    ThreadStart b1;
    ThreadStart b2;

    static char[] SCAN_ASCII =
    {
        /* 00 */  z,    z,   '1',  '2',  '3',  '4',  '5',  '6',
        /* 08 */ '7',  '8',  '9',  '0',  '-',  '=',  '\b', '\t',
        /* 10 */ 'q',  'w',  'e',  'r',  't',  'y',  'u',  'i',
        /* 18 */ 'o',  'p',  '[',  ']',  '\n',  z,   'a',  's',
        /* 20 */ 'd',  'f',  'g',  'h',  'j',  'k',  'l',  ';',
        /* 28 */ '\'', '`',   z,   '\\', 'z',  'x',  'c',  'v',
        /* 30 */ 'b',  'n',  'm',  ',',  '.',  '/', z,  z,
        /* 38 */ z, ' ', z, z, z, z, z,  z,
    };

    static char[] SHIFT_SCAN_ASCII =
    {
        /* 00 */  z, z,   '!',  '@',  '#',  '$',  '%',  '^',
        /* 08 */ '&',  '*',  '(',  ')',  '_',  '+',  '\b', '\t',
        /* 10 */ 'Q',  'W',  'E',  'R',  'T',  'Y',  'U',  'I',
        /* 18 */ 'O',  'P',  '{',  '}',  '\n',  z,   'A',  'S',
        /* 20 */ 'D',  'F',  'G',  'H',  'J',  'K',  'L',  ':',
        /* 28 */ '"',  '~', z,   '|',  'Z',  'X',  'C',  'V',
        /* 30 */ 'B',  'N',  'M',  '<',  '>',  '?', z,  z,
        /* 38 */ z, ' ', z, z, z, z, z,  z,
    };

    public override void Run()
    {
        System.DebugStub.Print("KeyboardDriver@" + Kernel.CurrentThread + ". ");
        uint listener = 0;
        Semaphore done = kernel.NewSemaphore(0);
        b1 = new BenchmarkAlloc(done);
        b2 = new BenchmarkAlloc2(done);

        while (true)
        {
            Kernel.kernel.Yield();
            uint key = INucleusCalls.TryReadKeyboard();
            char ch = z;

            bool key_down = (key >> 7 == 0);

            key &= 0x7f;

            switch (key)
            {
                case LSHIFT_SCAN:
                case RSHIFT_SCAN:
                    shift = key_down;
                    continue;

                case CTRL_SCAN:
                    ctrl = key_down;
                    continue;

                case ALT_SCAN:
                    alt = key_down;
                    continue;

                default:
                    if (key_down && key <= ASCII_TABLE_SIZE)
                    {
                        ch = shift ? SHIFT_SCAN_ASCII[key] : SCAN_ASCII[key];
                        break;
                    }
                    continue;
            }

            if (key == 2)
            {
                // '1'
                kernel.NewThread(
                    new BenchmarkYieldTo(kernel, done, 0));
                done.Wait();
            }
            else if (key == 3)
            {
                // '2'
                kernel.NewThread(
                    new BenchmarkSemaphore(kernel, done, 0));
                done.Wait();
            }
            else if (key == 4)
            {
                // '3'
                kernel.NewThread(b1);
                done.Wait();
            }
            else if (key == 5)
            {
                // '4'
                kernel.NewThread(b2);
                done.Wait();
            }
            else if (key == 6)
            {
                // '5'
                t = new BinaryTree(23); // 16 * 2^(23+1) = 16 * 16MB = 256MB
            }
            else if (key == 7)
            {
                // '6'
                //if (t != null) t.Flip();
                //t = null;
            }
            if (ch != z)
            {
                if (ch == '\t' && ctrl && !shift)
                {
                    listener++;
                    if (listener >= listeners.Length)
                    {
                        listener = 0;
                    }
                }
                else if (ch == '\t' && ctrl && shift)
                {
                    listener--;
                    if (listener >= listeners.Length)
                    {
                        listener = (uint)listeners.Length - 1;
                    }
                }
                else
                {
                    LastChar = ch;
                    listeners[listener].Signal();
                }
            }
        }
    }
}

public class BenchmarkSemaphore: ThreadStart
{
    Kernel kernel;
    Semaphore mySemaphore;
    Semaphore doneSemaphore; // only set for me == 0
    int me;
    BenchmarkSemaphore other;

    public BenchmarkSemaphore(Kernel kernel, Semaphore doneSemaphore, int me)
    {
        this.kernel = kernel;
        this.doneSemaphore = doneSemaphore;
        this.me = me;
        if (me == 0)
        {
            other = new BenchmarkSemaphore(kernel, null, 1);
            other.other = this;
            mySemaphore = kernel.NewSemaphore(0);
            other.mySemaphore = kernel.NewSemaphore(0);
        }
    }

    public override void Run()
    {
        int nIter = 1048576;
        if (me == 0)
        {
            kernel.NewThread(other);
            Semaphore s0 = mySemaphore;
            Semaphore s1 = other.mySemaphore;
            kernel.Yield();
            INucleusCalls.DebugPrintHex(50, 0);
            long t1 = INucleusCalls.Rdtsc();
            for (int i = 0; i < nIter; i++)
            {
                s1.Signal();
                s0.Wait();
            }
            long t2 = INucleusCalls.Rdtsc();
            uint diff = (uint)((t2 - t1) >> 20);
            INucleusCalls.DebugPrintHex(50, diff);
            doneSemaphore.Signal();
        }
        else
        {
            Semaphore s1 = mySemaphore;
            Semaphore s0 = other.mySemaphore;
            kernel.Yield();
            for (int i = 0; i < nIter; i++)
            {
                s1.Wait();
                s0.Signal();
            }
        }
    }
}

public class BenchmarkAlloc: ThreadStart
{
    Semaphore doneSemaphore;
    public BenchmarkAlloc(Semaphore doneSemaphore)
    {
        this.doneSemaphore = doneSemaphore;
    }

    public override void Run()
    {
        int nIter = 1048576;
        INucleusCalls.DebugPrintHex(50, 0);
        long t1 = INucleusCalls.Rdtsc();
        {
            new BinaryTree(0);
        }
        long t2 = INucleusCalls.Rdtsc();
        uint diff = (uint)((t2 - t1) >> 20);
        INucleusCalls.DebugPrintHex(50, diff);
        doneSemaphore.Signal();
    }
    private static int foo = 10;
}

public class BenchmarkAlloc2: ThreadStart
{
    Semaphore doneSemaphore;
    public BenchmarkAlloc2(Semaphore doneSemaphore)
    {
        this.doneSemaphore = doneSemaphore;
    }

    public override void Run()
    {
        int nIter = 65536;
        INucleusCalls.DebugPrintHex(50, 0);
        long t1 = INucleusCalls.Rdtsc();
        for (int i = 0; i < nIter; i++)
        {
            (new byte[1000])[0]++;
        }
        long t2 = INucleusCalls.Rdtsc();
        uint diff = (uint)((t2 - t1) >> 16);
        INucleusCalls.DebugPrintHex(50, diff);
        doneSemaphore.Signal();
    }
}

public class BinaryTree
{
    public BinaryTree left, right;
    public BinaryTree(int depth)
    {
        if (depth != 0)
        {
            left = new BinaryTree(depth - 1);
            right = new BinaryTree(depth - 1);
        }
    }
    public void Flip()
    {
        BinaryTree t = left;
        left = right;
        right = t;
        if (left != null) left.Flip();
        if (right != null) right.Flip();
    }
}

public class BenchmarkYieldTo: ThreadStart
{
    Kernel kernel;
    Semaphore doneSemaphore; // only set for me == 0
    int me;
    uint myId; // only set for me == 0
    BenchmarkYieldTo other;

    public BenchmarkYieldTo(Kernel kernel, Semaphore doneSemaphore, int me)
    {
        this.kernel = kernel;
        this.doneSemaphore = doneSemaphore;
        this.me = me;
        if (me == 0)
        {
            other = new BenchmarkYieldTo(kernel, null, 1);
            other.other = this;
        }
    }

    public override void Run()
    {
        int nIter = 1048576;
        if (me == 0)
        {
            myId = Kernel.CurrentThread;
            Thread otherT = kernel.NewThread(other);
            uint otherId = otherT.id;
            kernel.Yield();
            try
            {
                CompilerIntrinsics.Cli();
                NucleusCalls.DebugPrintHex(50, 0);
                long t1 = NucleusCalls.Rdtsc();
                for (int i = 0; i < nIter; i++)
                {
                    NucleusCalls.YieldTo(otherId);
                }
                long t2 = NucleusCalls.Rdtsc();
                uint diff = (uint)((t2 - t1) >> 20);
                NucleusCalls.DebugPrintHex(50, diff);
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
            doneSemaphore.Signal();
        }
        else
        {
            uint otherId = other.myId;
            kernel.Yield();
            try
            {
                CompilerIntrinsics.Cli();
                for (int i = 0; i < nIter; i++)
                {
                    NucleusCalls.YieldTo(otherId);
                }
            }
            finally
            {
                CompilerIntrinsics.Sti();
            }
        }
    }
}

public class B {
}

public class C : B {
}

public class D : C {
}

public class E : C {
}

public interface I {
    int m(int x);
}

public interface J {
    int mj(int x);
}

public class C1 : I {
    public int m(int x) {
        return x;
    }
}

public class C2 : I, J {
    public C2(int f) { this.f = f; }
    public int m(int x) {
        return x + x;
    }
    public int mj(int x) {
        return x * 10;
    }

    private int f;
}

public class Benchmark3: ThreadStart
{
    Semaphore doneSemaphore;
    public Benchmark3(Semaphore doneSemaphore)
    {
        this.doneSemaphore = doneSemaphore;
    }

    public override void Run()
    {
        //int nIter = 1048576;
        int nIter = 65536;
        INucleusCalls.DebugPrintHex(50, 0);
        long t1 = INucleusCalls.Rdtsc();

        /* int array
         * int[] a = new int[9];
        for (int i = 0; i < nIter; i++)
        {
            if (i < 9) a[i] = i;
            new BinaryTree(0);
        }
        for (int i = 0; i < 9; i++) {
            System.Console.WriteLine(" i => " + a[i]);
        }*/
        
        // cast/instance of/array store

        /*B[] a = new C[10];
        for (int i = 0; i < 10; i++) {
            if (i < 2) a[i] = new C();
            else if (i < 4) a[i] = new D();
            else a[i] = new E();
        }

        // instance of
        for (int i = 0; i < 10; i++) {
            if (a[i] is D) {
                INucleusCalls.DebugPrintHex(20, (uint)i);
            }
        }

        // cast
        for (int i = 0; i < 10; i++) {
            if (i > 4) {
                E e = (E)a[i];
                INucleusCalls.DebugPrintHex(20, (uint)i);
            }
        }

        // box/unboxing
        System.Object[] a = new System.Object[9];
        for (int i = 0; i < 9; i++) {
            a[i] = i;
        }
        for (int i = 0; i < 9; i++) {
            int j = (int)a[i];
            INucleusCalls.DebugPrintHex(20, (uint)j);
        } 

        // interface lookup
        C1 c1 = new C1();
        C2 c2 = new C2(1);
        I i = null;
        if (foo == 2) i = c1;
        else i = c2;
        foo = i.m(3);
        INucleusCalls.DebugPrintHex(20, (uint)foo); 

        System.Object o = null;
        if (foo == 2) o = c1;
        else o = c2;
        J oj = (J)o;
        int result = oj.mj(3);
        INucleusCalls.DebugPrintHex(20, (uint)result); 

        // int[][]
        int[][] board = new int[8][];

        for (int i = 0; i < 8; i++) {
            board[i] = new int[8] { 0, 1, 2, 3, 4, 5, 6, 7 };
        }
        for (int i=0; i<8; i++) {
            for (int j=0; j<8; j++) {
                INucleusCalls.DebugPrintHex(20, (uint)i);
                INucleusCalls.DebugPrintHex(30, (uint)j);
                INucleusCalls.DebugPrintHex(40, (uint)board[i][j]);
            }
        }*/

        
        //impact.othello.othello.Main(new System.String[1] { "-d" });
        //Crafty.Net.OO.Crafty.Main(new System.String[0]);
        //SharpSAT.SATSolver.Main(new System.String[1]{"input"});
        //impact.li_130.xlisp.Main(new System.String[0]);

        long t2 = INucleusCalls.Rdtsc();
        uint diff = (uint)((t2 - t1) >> 16);
        INucleusCalls.DebugPrintHex(50, diff);
        doneSemaphore.Signal();
    }
}
