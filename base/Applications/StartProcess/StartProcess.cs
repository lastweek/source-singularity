////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Run test code, as identified by the distro's test.xml manifest
//

using FileSystem.Utils;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Xml;
using System;
using System.Collections;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.V1.Services;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Applications;
using Microsoft.Contracts;
using Microsoft.Singularity.Configuration;

[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{

    [ConsoleCategory(HelpMessage="Test harness", DefaultAction=true)]
    internal sealed class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DirectoryServiceContract.Imp:Start> nsRef;

        [StringArrayParameter( "EveryThingElse", Mandatory=false)]
        internal string[] Args;

        reflective internal Parameters();

        internal int AppMain() {
            return RunTests.AppMain(this);
        }
    }
    
    public class RunTests
    {
        //[ShellCommand("StartProcess", "tests lib routine to start process with Manifest")]
        internal static int AppMain(Parameters! config)
        {
            DirectoryServiceContract.Imp ds = null;
            if (config.nsRef != null) ds = config.nsRef.Acquire(); 
            if (ds == null) { 
                throw new Exception("Unable to acquire handle to the Directory Service root"); 
            } 
            ds.RecvSuccess();

            // Make ourselves a new output pipe
            UnicodePipeContract.Exp! newOutputExp;
            UnicodePipeContract.Imp! newOutputImp;
            UnicodePipeContract.NewChannel(out newOutputImp, out newOutputExp);

            // Retrieve our real stdOut and start using the one we just created
            // instead
            UnicodePipeContract.Imp stdOut = ConsoleOutput.Swap(newOutputImp);

            if (stdOut == null) {
                Console.WriteLine("runtests expects a STDOUT pipe");
                delete newOutputExp;
                delete ds; 
                return 1;
            }

            // Use a mux to splice our own output together with the child
            // processes we will run.
            PipeMultiplexer! outputMux = PipeMultiplexer.Start(stdOut, newOutputExp);

            string[] args = config.Args;
            if (args != null && args[0] != null) RunProcess(ds, args ,outputMux);
            outputMux.Dispose();
            delete ds; 
            return 0;
        }


        private static int RunProcess(DirectoryServiceContract.Imp! ds,
                                      string[] args,
                                      PipeMultiplexer! outputMux)
        {
            Process child = Binder.CreateProcess(ds,args,outputMux);
            if (child != null) {
                child.Start();
                child.Join();
                return 0;
            }
            return -1;
        }
    }
}
