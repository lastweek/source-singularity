////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Shell utility to pause execution.
//

using System;
using System.Threading;
// using Microsoft.Singularity.V1.Services;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Channels;
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

        [LongParameter( "seconds", Mandatory=true, Position=0, HelpMessage="seconds")]
        internal long seconds;

        [BoolParameter( "m", Default=false , HelpMessage="treat time as milliseconds")]
        internal bool doMilli;

        [BoolParameter( "v", Default=false , HelpMessage="verbose output")]
        internal bool doVerbose;

        reflective internal Parameters();

        internal int AppMain() {
            return Sleep.AppMain(this);
        }
    }
    
    public class Sleep
    {
        private static void ConsoleWriteDateTime(string preamble, DateTime dt)
        {
            Console.WriteLine("{0}{1:d4}/{2:d2}/{3:d2} {4:d2}:{5:d2}:{6:d2}.{7:d3}",
                              preamble, dt.Year, dt.Month, dt.Day,
                              dt.Hour, dt.Minute, dt.Second, dt.Millisecond);
        }

        private static void ConsoleWriteDateTime(string preamble, TimeSpan sp)
        {
            Console.WriteLine("{0}{1}", preamble, sp.ToString());

        }


        private static void DoDate(string pre)
        {
            Console.WriteLine(pre + "cycles: {0}", Processor.CycleCount );
            ConsoleWriteDateTime(pre , DateTime.UtcNow);
        }

        internal static int AppMain(Parameters! config)
        {
             try {
                uint seconds = (uint) config.seconds; 
                
                if (config.doVerbose) DoDate(" pre  ");
                if (config.doMilli) {
                    Thread.Sleep(TimeSpan.FromMilliseconds(seconds));
                }
                else {
                    Thread.Sleep(TimeSpan.FromSeconds(seconds));
                }
                if (config.doVerbose) DoDate(" post ");
                return 0;
            }
            catch (ArgumentOutOfRangeException) {    // From Thread.Sleep
                Console.WriteLine("Value too large :- \"{0}\"", config.seconds);
            }
            return 1;
        }
    }
}
