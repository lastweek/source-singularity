///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   NetStackThreadPool.sg
//
//  Note: adapted from CassiniThreadPool.sg
//

//#if THREAD_POOL

using VTable = System.VTable;
using DebugStub = System.DebugStub;
using System.Collections;
using System.Threading;

namespace Microsoft.Singularity.NetStack2
{
    /// <remarks>This class implements a non-Singleton
    /// threadpool and has a configurable work queue
    /// size. </remarks>
    public sealed class NetStackThreadPool: IThreadStart
    {
        MonitorLock                       monitor;
        Queue                             commands; // Queue of IThreadStart
        int                               queuedItems;
        readonly int                      maxQueuedItems;
        volatile int                      threadCount;
        volatile bool                     shutdown;
        ManualResetEvent                  shutdownEvent;

        [Microsoft.Contracts.NotDelayed]
        public NetStackThreadPool(int maxThreads, int maxQueuedItems)
            //requires maxThreads > 0;
            //requires maxQueuedItems > 0;
            //requires maxThreads <= maxQueuedItems;
        {
            this.monitor          = new MonitorLock();
            this.commands         = new Queue();
            this.queuedItems      = 0;
            this.maxQueuedItems   = maxQueuedItems;
            this.threadCount      = maxThreads;
            this.shutdown         = false;
            this.shutdownEvent    = new ManualResetEvent(false);

            for (int i = 0; i < maxThreads; i++) {
                Thread t = new Thread(this);
                t.Start();
            }
        }

        public void Run()
        {
            WorkerMain();
        }

        /// <summary> Queues call to constructor supplied
        /// delegate with user supplied object.  This method
        /// blocks if maximum queue size is reached.  </summary>
        public void QueueUserWorkItem(IThreadStart command)
        {
            Monitor.Enter(this.monitor);
            while (this.queuedItems == this.maxQueuedItems) {
                Monitor.Wait(this.monitor);
            }
            commands.Enqueue(command);
            this.queuedItems++;
            Monitor.Pulse(this.monitor);
            Monitor.Exit(this.monitor);
        }

        private void WorkerMain()
        {
            while (true) {
                IThreadStart command;
                using (this.monitor.Lock()) {
                    while (queuedItems == 0 && !shutdown) {
                        Monitor.Wait(this.monitor);
                    }

                    if (queuedItems == 0 && shutdown) {
                        break;
                    }

                    command = (IThreadStart) (commands.Dequeue());
                    VTable.Assert(command != null);

                    if (this.queuedItems-- == this.maxQueuedItems) {
                        Monitor.Pulse(this.monitor);
                    }
                }
                command.Run();
            }

            using (this.monitor.Lock()) {
                if (--this.threadCount == 0) {
                    shutdownEvent.Set();
                }
            }
        }

        /// <summary>
        /// Shutdown thread pool instance.  Caller blocks until
        /// the threads in the pool have finished outstanding
        /// work items.
        /// </summary>
        internal void Shutdown()
        {
            using (this.monitor.Lock()) {
                shutdown = true;
                Monitor.PulseAll(this.monitor);
            }

            shutdownEvent.WaitOne();
            shutdownEvent.Reset();

            DebugStub.Assert(commands.Count == 0);
        }
    }
}

//#endif // THREAD_POOL
