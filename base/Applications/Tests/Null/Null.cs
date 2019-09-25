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

using Microsoft.Singularity.Channels;
using Microsoft.Contracts;
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

        reflective internal Parameters();

        internal int AppMain() {
            return Null.AppMain(this);
        }
    }
    public class Null
    {
        //[ShellCommand("null", "Test null reference access")]
        internal static int AppMain(Parameters! config)
        {
            DebugStub.Print("Calling null.ToString\n");
            Object obj = null;
            String s = obj.ToString();
            DebugStub.Print("Output: " + s);
            return 0;
        }
    }
}
