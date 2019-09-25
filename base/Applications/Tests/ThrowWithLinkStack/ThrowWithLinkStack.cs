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
using System.Runtime.CompilerServices;

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
            return ThrowWithLinkStack.AppMain(this);
        }
    }

    public class ThrowWithLinkStack
    {
        //[ShellCommand("throwWithLinkStack", "Throw an exception with link stack")]
        internal static int AppMain(Parameters! config)
        {
            try {
                DebugStub.Print("About to throw exception\n");
                Throw();
            }
            catch (Exception e) {
                Console.WriteLine("Throw with Link Stack Caught exception {0}", e);
            }
            return 0;
        }

        [RequireStackLink]
        public static int Throw() {
                throw new ApplicationException("AppException");
        }
    }
}
