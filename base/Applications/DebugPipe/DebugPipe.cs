////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Utility to pipe stdin to debugger.
//

using System;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(HelpMessage="Echo stdin to debugger", DefaultAction=true)]
    internal class Parameters 
    {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal Parameters();

        internal int AppMain() {
            return DebugPipe.AppMain(this);
        }
    }

    public class DebugPipe
    {
        internal static int AppMain(Parameters! config)
        {
            while (true) {
                string a = Console.ReadLine();
                if ((a == null) || (a == "@exit")) {
                    break; 
                } 
                DebugStub.WriteLine(a);
                Console.WriteLine(a);
            }
            return 0;
        }
    }
}

