///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   print and return the boot count.

using System;
using System.IO;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;

using Microsoft.Singularity.V1.Services;

using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Channels;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(HelpMessage="Display and return the boot count", DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal Parameters();

        internal int AppMain() {
            return BootCount.AppMain(this);
        }
    }

    class BootCount
    {
       internal static int AppMain(Parameters! config) {
            int boots = (int) ProcessService.GetKernelBootCount();
            Console.WriteLine(boots);
            return boots;
        }
    }
}
