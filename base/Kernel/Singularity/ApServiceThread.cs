////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ApServiceThread.cs
//
//  Note:
//

using System.Threading;

using Microsoft.Singularity;


namespace Microsoft.Singularity
{
    internal class ApServiceThread
    {
        public static AutoResetEvent abiEvent;

        internal static void Initialize()
        {
            abiEvent = new AutoResetEvent(false);
            Thread.CreateThread(Thread.CurrentProcess, new ThreadStart(ApServiceLoop)).Start();
        }

        private static void ApServiceLoop()
        {
            DebugStub.WriteLine("ApServiceThread is initialized and sleeping ...");
            MpExecution.MpCall mpCall;
            bool iflag;

            while (true) {
                abiEvent.WaitOne();

                DebugStub.WriteLine
                    ("HSG: ** cpu.{0} receives AbiCall interrupt",
                     __arglist(Processor.GetCurrentProcessorId()));

                // Current design: the boot processor will get all
                // unserved abi call. So we don't need to worry
                // missing any calls
                while (true) {

                    iflag = Processor.DisableInterrupts();
                    mpCall = MpExecution.GetMpCall(Processor.GetCurrentProcessorId());
                    Processor.RestoreInterrupts(iflag);


                    // There is no unserved abi call, just break
                    if (mpCall == null) {
                        break;
                    }

                    BspAbiStub.ProcessMpCall(Processor.GetCurrentProcessorId(), mpCall);
                }
            }
        }
    }
}
