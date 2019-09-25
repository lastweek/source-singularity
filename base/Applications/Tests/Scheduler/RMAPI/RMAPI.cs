///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Threading;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.UnitTest;
using Microsoft.Singularity.V1.Services;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(HelpMessage="Utility to test Resource Management APIs. Run selected tests.",
                     DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DirectoryServiceContract.Imp:Start> nsRef;

        [BoolParameter("ProcessWithOutput", Default = false,
            HelpMessage="Run process creation test with children output to console.")]
        public bool runProcessWithOutput;

        [BoolParameter("ProcessNoOutputLoop", Default = false,
            HelpMessage="Run process creation test where children don't output to console. Run in infinit loop")]
        public bool runProcessWithOutputLoop;

        [BoolParameter("ProcessNoOutput", Default = false,
            HelpMessage="Run process creation test where children don't output to console.")]
        public bool runProcessNoOutput;

        reflective internal Parameters();

        internal int AppMain() {
            TestsToRun testsToRun = TestsToRun.None;
            if (runProcessWithOutput) {
                testsToRun |= TestsToRun.ProcessWithOutput;
            }
            if (runProcessNoOutput) {
                testsToRun |= TestsToRun.ProcessNoOutput;
            }
            if (runProcessWithOutputLoop) {
                testsToRun |= TestsToRun.ProcessNoOutputLoop;
            }
            return RMAPI.AppMain(testsToRun);
        }
    }
   
    [ConsoleCategory(HelpMessage="Utility to test Resource Management APIs. Run all tests.",
                     Action="all")]
    internal class AllTestsParameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<DirectoryServiceContract.Imp:Start> nsRef;

        reflective internal AllTestsParameters();

        internal int AppMain() {
            return RMAPI.AppMain(TestsToRun.All);
        }
    }

    [Flags]
    internal enum TestsToRun
    {
        None                = 0x0,
        ProcessWithOutput   = 0x1,
        ProcessNoOutput     = 0x2,
        ProcessNoOutputLoop = 0x4,
        All                 = 0xF,
    }

    internal sealed class RMAPI
    {
        internal static int AppMain(TestsToRun testsToRun)
        {
            // Run test cases where the child processes don't output to the console
            if ((testsToRun & TestsToRun.ProcessNoOutput) != 0) {
                TestProcessCreation.RunWithNoChildOutput();
            }
            
            // Run test cases where the child processes output to the console
            if ((testsToRun & TestsToRun.ProcessWithOutput) != 0) {
                TestProcessCreation.RunWithChildOutput();
            }

            // Run test cases where the child processes don't output to the console
            if ((testsToRun & TestsToRun.ProcessNoOutputLoop) != 0) {
                for (int i = 0; ; i++) {
                    Console.Write(i);
                    Console.Write('.');
                    TestProcessCreation.RunWithNoChildOutput();
                    Thread.Sleep(1000);
                }
            }

            return 0;
        }
    }
}


