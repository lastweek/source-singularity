///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   WatchDogTimer.cs
//
//  Note:
//

using System;
using System.Threading;

namespace Microsoft.Singularity.UnitTest
{
    /// <remarks> A class to watch for timeouts.</remarks>
    public sealed class WatchDogTimer
    {
        private TimeSpan        timeout;
        private Thread          worker;
        private volatile bool   running;
        private AutoResetEvent! workEvent;

        public WatchDogTimer(TimeSpan timeout)
        {
            this.timeout = timeout;
            this.running = false;
            this.workEvent   = new AutoResetEvent(false);
        }

        public void Start()
        {
            lock (this) {
                if (!this.running) {
                    this.running = true;
                    this.worker = new Thread(new ThreadStart(WorkerMain));
                    this.worker.Start();
                }
            }
        }

        public void Stop()
        {
            Thread toJoin = null;
            lock (this) {
                if (this.running) {
                    this.running = false;
                    this.workEvent.Set();
                    toJoin = this.worker;
                    this.worker = null;
                }
            }
            if (toJoin != null) {
                toJoin.Join();
            }
        }

        public void Defer()
        {
            lock (this) {
                Assert.True(this.running,
                            "Watch dog timer expired or stopped.");
                workEvent.Set();
            }
        }

        public bool Running
        {
            get { return this.running; }
        }

        private void LockedWorkerExpire()
        {
            try {
                Assert.True(false, "Watch-dog timed out.");
            }
            catch (FailedAssertionException) {
                // Expected
            }
            this.running = false;
        }

        private void WorkerMain()
        {
            bool done = false;
            while (!done) {
                bool signalled = WaitOne(this.workEvent, this.timeout);
                lock (this) {
                    if (signalled) {
                        done = !this.running;
                    }
                    else {
                        LockedWorkerExpire();
                        done = true;
                    }
                }
            }
        }

        private static bool WaitOne(WaitHandle /*!*/ w, TimeSpan t)
        {
#if SINGULARITY
            return w.WaitOne(t);
#else
            return w.WaitOne(t, false);
#endif
        }
    }
}
