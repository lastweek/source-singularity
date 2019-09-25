////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using System;

namespace Microsoft.Singularity.Applications
{
    public class HelloMp
    {
        public static int Main(String[] args)
        {
            Console.WriteLine("If you see this message, it means you haven't");
            Console.WriteLine("run Applications/HelloMpAsm/load-hack.cmd");
            Console.WriteLine("Please run the command AFTER msb Distro\\small.proj");
            return 0;
        }
    }
}
