///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//
using System;
using System.Collections;
using System.Threading;
#if SINGULARITY
using Microsoft.Contracts;
#endif

namespace Microsoft.Singularity.Applications
{
    /// <remarks>This class implements a non-Singleton
    /// threadpool and has a configurable work queue
    /// size. </remarks>
    public sealed class ThreadPool
    {
        internal class WorkItem {
            public WorkCallback callback; 
            public object userObject; 
            
            public WorkItem(WorkCallback callback, object userObject)
            {
                this.callback   = callback;
                this.userObject = userObject;
            }
        }
        
        public delegate void WorkCallback(object userObject);

        Queue /* ! */          workItems; 
        WorkCallback /* ! */    workCallback;
        int              maxQueuedItems;
        volatile int     threadCount;
        volatile bool    shutdown;
        ManualResetEvent shutdownEvent;

#if SINGULARITY
        [NotDelayed]
#endif
        public ThreadPool(int maxThreads,
                               int maxQueuedItems,
                               WorkCallback/* ! */ workCallback)
#if SINGULARITY                               
            requires maxThreads > 0;
            requires maxQueuedItems > 0;
            requires maxThreads <= maxQueuedItems;
#endif            
        {
            this.workCallback   = workCallback;
            this.workItems      = new Queue(maxQueuedItems);
            this.maxQueuedItems = maxQueuedItems;
            this.threadCount    = maxThreads;
            this.shutdown       = false;
            this.shutdownEvent  = new ManualResetEvent(false);
#if SINGULARITY
            base();
#endif
            for (int i = 0; i < maxThreads; i++) {
                Thread t = new Thread(new ThreadStart(WorkerMain));
                t.Start();
            }
        }

        /// <summary>
        /// Queues call to constructor supplied delegate with
        /// user supplied object.  If queuing request causes queue to
        /// become full, false is returned and no further items should
        /// be enqueued until delegate has been called.
        /// </summary>
        public  bool QueueUserWorkItem(object userObject)
        {
            bool queueIsFull = false;
            lock (this) {
                if (workItems.Count == maxQueuedItems) {
                    queueIsFull =  true; 
                }
                else {
#if SINGULARITY
                    assert workItems.Count < maxQueuedItems;
                    assert shutdown == false;
#endif
                    WorkItem work = new WorkItem(this.workCallback, userObject);
                    workItems.Enqueue(work);
                    queueIsFull = (workItems.Count == maxQueuedItems);
                    if (workItems.Count == 1) {
                    }
                        Monitor.Pulse(this);
                }
            }
            return queueIsFull;
        }

        /// <summary>
        /// Queues call to supplied delegate with
        /// user supplied object.  If queuing request causes queue to
        /// become full, false is returned and no further items should
        /// be enqueued until delegate has been called.
        /// </summary>
        public  bool QueueUserWorkItem(WorkCallback callback, object userObject)
        {
            bool queueIsFull = false;
            lock (this) {
                if (workItems.Count == maxQueuedItems) {
                    queueIsFull =  true; 
                }
                else {
#if SINGULARITY
                    assert workItems.Count < maxQueuedItems;
                    assert shutdown == false;
#endif
                    WorkItem work = new WorkItem(callback, userObject);
                    workItems.Enqueue(work);
                    queueIsFull = (workItems.Count == maxQueuedItems);
                    if (workItems.Count == 1) {
                    }
                        Monitor.Pulse(this);
               }
            }
            return queueIsFull;
        }

        /// <summary>
        /// Shutdown thread pool instance.  Caller blocks until
        /// the threads in the pool have finished outstanding
        /// work items.
        /// </summary>
        public void Shutdown()
        {
            lock (this) {
                shutdown = true;
                Monitor.PulseAll(this);
            }
            shutdownEvent.WaitOne();
        }

        private void WorkerMain()
        {
            while (true) {
                object workItem = null;
                lock (this) {
                    while  (workItems.Count == 0 && !shutdown) {
                        Monitor.Wait(this);
                    }
                    if (workItems.Count == 0 && shutdown) {
                        break;
                    }
                    workItem = workItems.Dequeue();
                }
                if (workItem != null) {
                    WorkItem w  = workItem as WorkItem;
#if SINGULARITY
                    assert w != null; 
                    assert w.callback != null;
#endif
                    w.callback(w.userObject);
            }

                if (--threadCount == 0) {
                    shutdownEvent.Set();
                }
            }
        }
    }
}

