////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program.
//
using System;

[assembly: System.Reflection.AssemblyVersionAttribute("1.0.0.0")]
[assembly: System.Reflection.AssemblyKeyFileAttribute("public.snk")]
[assembly: System.Reflection.AssemblyDelaySignAttribute(true)]

namespace Microsoft.Singularity.Applications
{
    public class Hello
    {
        public static int Main(String[] args)
        {
            Console.WriteLine("Hello World!");
            return 0;
        }
    }
}
