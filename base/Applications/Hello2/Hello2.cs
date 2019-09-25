////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Simple Singularity test program that uses reflections.
//
using System;
using System.Text;
using System.Threading;
using Microsoft.Singularity;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.FileSystem;
using Microsoft.Singularity.V1.Services;

using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;

[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{

    [ConsoleCategory(HelpMessage="Writes hello world to stdout", DefaultAction=true)]
    internal class Parameters
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DirectoryServiceContract.Imp:Start> nsRef;

        reflective internal Parameters();

        internal int AppMain() {
            return Hello2.AppMain(this);
        }
    }

    public class Hello2
    {
        internal static int AppMain(Parameters! config)
        {
            DebugStub.Print("About to write to console\n");
            Console.WriteLine("Hello World!");
            DebugStub.Print("Wrote to console\n");

            return 0;
        }
    }
}
