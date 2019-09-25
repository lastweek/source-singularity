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
            return Throw.AppMain(this);
        }
    }
    
    public class Throw
    {
        //[ShellCommand("throw", "Throw an exception")]
        internal static int AppMain(Parameters! config)
        {
            string args = "something"; 
            
            try {
                DebugStub.Print("About to throw exception\n");
                if (args == null) {
                    throw new ArgumentNullException("ArgNullException");
                }
                throw new ApplicationException("AppException");
            }
            catch (Exception e) {
                Console.WriteLine("Caught exception {0}", e);
            }
            return 0;
        }
    }
}
