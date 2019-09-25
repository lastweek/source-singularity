// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

#if false
using System;
// using System.Diagnostics;
using System.Threading;
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity.NetStack2
{
    public abstract class StopThreadContract
    {
        public abstract void Terminate();
    }

    public abstract class StoppableThread: IThreadStart
    {
        protected abstract void Run(StopThreadContract/*.Exp*/ terminator);

        Thread thread;
        ManualResetEvent doneEvent;

        bool running;
        readonly /*TRef*/StopThreadContract/*.Imp*/ terminatorImpRef;
        readonly /*TRef*/StopThreadContract/*.Exp*/ terminatorExpRef;

        protected StoppableThread()
        {
            StopThreadContract/*.Imp*/ terminator_imp;
            StopThreadContract/*.Exp*/ terminator_exp;
            StopThreadContract.NewChannel(out terminator_imp, out terminator_exp);

            terminatorImpRef = (terminator_imp);
            terminatorExpRef = (terminator_exp);
            running = false;

            thread = null;
        }

        private void ThreadRoutine()
        {
            StopThreadContract/*.Exp*/ terminator_exp = terminatorExpRef.Acquire();
            try {
                Run(terminator_exp);
            }
            finally {
                //delete terminator_exp;
            }
        }

        public void Start()
        {
            if (thread != null)
                throw new InvalidOperationException("This thread has already been started.");

            Thread t = new Thread(this);
            thread = t;
            t.Start();
            running = true;
        }

        public void Run()
        {
            doneEvent = new ManualResetEvent();
            ThreadRoutine();
            doneEvent.Set();
        }

        public void Stop()
        {
            if (!running)
                return;

            DebugStub.WriteLine(String.Format("StoppableThread: Asking thread {0} to stop...", thread.ToString()));

            VTable.Assert(thread != null);
            StopThreadContract/*.Imp*/ terminatorImp = this.terminatorImpRef.Acquire();
            terminatorImp.SendTerminate();

            bool timeout_occurred = false;
/* TODO
            bool done;
            do {
                switch receive {
                    case terminatorImp.AckTerminate():
                        done = true;
                        break;

                    case terminatorImp.ChannelClosed():
                        // good enough
                        done = true;
                        DebugStub.WriteLine(String.Format("Warning: Thread {0} closed its termination channel.", thread.ToString()));
                        DebugStub.WriteLine("The thread may have terminated unexpectedly (thrown an exception).");
                        break;

                    case timeout(TimeSpan.FromSeconds(10)):
                        DebugStub.WriteLine(String.Format("Warning: Thread {0} is ignoring request to terminate.", thread.ToString()));
                        done = false;
                        timeout_occurred = true;
                        break;
                }
            } while (!done);
*/

            //delete terminatorImp;
            running = false;

            while (!doneEvent.WaitOne(TimeSpan.FromSeconds(10))) {
                DebugStub.WriteLine(String.Format("Warning: Thread {0} acknowledge stop request, but has not yet terminated.", thread.ToString()));
                timeout_occurred = true;
            }

            if (timeout_occurred) {
                DebugStub.WriteLine(String.Format("StoppableThread: Thread {0} successfully stopped.", thread.ToString()));
            }
        }
    }
}
#endif
