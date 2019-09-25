////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   This file contains the main entry point for the C#
//          portion of Singularity.
//
using Microsoft.Singularity;
using System;
using System.Runtime.CompilerServices;
using System.Threading;

namespace Microsoft.Singularity
{
    public class Iltest
    {
        public static int Main(String[] args)
        {
            int i = 10;
            long l = 100;
            byte b = 1;

            DebugStub.Print("Hello from TestApp.cs\n");
            DebugStub.Print("byte: {0}, int: {1}, long: {2}\n",
                            __arglist(b, i, l));

            return 999;
        }
    }
}
