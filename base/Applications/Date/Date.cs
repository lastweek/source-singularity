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


using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{
    [ConsoleCategory(HelpMessage="Show attributes associated with a file", DefaultAction=true)]
    internal class Parameters {
        [InputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [OutputEndpoint("data")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal Parameters();

        internal int AppMain() {
            return Date.AppMain(this);
        }
    }

    public class Date
    {
        private static void ConsoleWriteDateTime(string preamble, DateTime dt)
        {
            Console.WriteLine("{0}{1:d4}/{2:d2}/{3:d2} {4:d2}:{5:d2}:{6:d2}.{7:d3}",
                preamble, dt.Year, dt.Month, dt.Day,
                dt.Hour, dt.Minute, dt.Second, dt.Millisecond);
        }

        private static void ConsoleWriteTimeSpan(string preamble, TimeSpan sp)
        {
            Console.WriteLine("{0}{1:d5} days {2:d2}:{3:d2}:{4:d2}.{5:d3}",
                preamble, sp.TotalDays,
                sp.Hours, sp.Minutes, sp.Seconds, sp.Milliseconds);
        }

        //[ShellCommand("date", "Display date and time")]
        internal static int AppMain(Parameters! config)
        {
            ConsoleWriteTimeSpan("Kernel: ", ProcessService.GetUpTime());
            ConsoleWriteDateTime("UTC:    ", DateTime.UtcNow);
            return 0;
        }
    }
}
