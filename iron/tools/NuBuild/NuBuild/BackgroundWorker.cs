//---
//- <copyright file="BackgroundWorker.cs" company="Microsoft Corporation">
//-     Copyright (c) Microsoft Corporation.  All rights reserved.
//- </copyright>
//---

namespace NuBuild
{
    using System;
    using System.Collections.Generic;
    using System.Threading;
    using System.Threading.Tasks;

    /
    /
    /
    /
    /
    public delegate void BackgroundWorkerProcedure(object argument1, object argument2);

    /
    /
    /
    /
    /
    /
    /
    /
    public class BackgroundWorker : IDisposable
    {
        /
        /
        /
        private Thread workerThread;

        /
        /
        /
        private Queue<BackgroundWorkerQueueItem> workQueue;

        /
        /
        /
        private Mutex workQueueLock;

        /
        /
        /
        private AutoResetEvent workQueueHasNewWork;

        /
        /
        /
        private volatile uint workItemsQueued;

        /
        /
        /
        private volatile uint workItemsPerformed;

        /
        /
        /
        private volatile uint workItemsFailed;

        /
        /
        /
        private volatile bool ourWorkIsNotDone;

        /
        /
        /
        private bool disposed;

        /
        /
        /
        public BackgroundWorker()
        {
            this.workQueue = new Queue<BackgroundWorkerQueueItem>();
            this.workQueueLock = new Mutex();
            this.workQueueHasNewWork = new AutoResetEvent(false);
            this.workItemsQueued = 0;
            this.workItemsPerformed = 0;
            this.workItemsFailed = 0;
            this.ourWorkIsNotDone = true;
            this.disposed = false;

            this.workerThread = new Thread(new ThreadStart(this.WorkerThreadMain));

            
            this.workerThread.Start();
        }

        /
        /
        /
        public uint GetWorkItemsQueued
        {
            get { return this.workItemsQueued; }
        }

        /
        /
        /
        /
        public uint GetWorkItemsPerformed
        {
            get { return this.workItemsPerformed; }
        }

        /
        /
        /
        public uint GetWorkItemsFailed
        {
            get { return this.workItemsFailed; }
        }

        /
        /
        /
        /
        /
        /
        /
        /
        public void QueueWork(BackgroundWorkerProcedure procedure, object argument1, object argument2)
        {
            BackgroundWorkerQueueItem workItem = new BackgroundWorkerQueueItem(procedure, argument1, argument2);

            this.workQueueLock.WaitOne();
            this.workQueue.Enqueue(workItem);
            this.workItemsQueued++;
            this.workQueueLock.ReleaseMutex();

            this.workQueueHasNewWork.Set();
        }

        /
        /
        /
        /
        public void StopWork()
        {
            this.QueueWork(this.StopWorkerThread, null, null);
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        /
        public void WaitForCompletion()
        {
            this.workerThread.Join();
        }

        /
        /
        /
        public void Dispose()
        {
            this.Dispose(true);
            GC.SuppressFinalize(this);
        }

        /
        /
        /
        /
        protected virtual void Dispose(bool disposing)
        {
            if (this.disposed)
            {
                return;
            }

            if (disposing)
            {
                this.workQueueLock.Dispose();
                this.workQueueHasNewWork.Dispose();
            }

            this.disposed = true;
        }

        /
        /
        /
        /
        /
        /
        /
        /
        /
        private void StopWorkerThread(
            object unused1,
            object unused2)
        {
            this.ourWorkIsNotDone = false;
        }

        /
        /
        /
        private void WorkerThreadMain()
        {
            List<BackgroundWorkerQueueItem> toDoList = new List<BackgroundWorkerQueueItem>();

            //- -
            //- Run until we're told to stop.
            //- -
            while (this.ourWorkIsNotDone)
            {
                //- -
                //- Wait for new work to be added to the queue.
                //- -
                if (this.workQueueHasNewWork.WaitOne())
                {
                    toDoList.Clear();

                    //- -
                    //- Pull all queued work items off the global work queue
                    //- (while holding the lock), and place them on our
                    //- thread-local toDoList.
                    //- -
                    this.workQueueLock.WaitOne();

                    while (this.workQueue.Count > 0)
                    {
                        toDoList.Add(this.workQueue.Dequeue());
                    }

                    this.workQueueLock.ReleaseMutex();

                    //- -
                    //- Do the requested work.
                    //- -
                    foreach (BackgroundWorkerQueueItem workItem in toDoList)
                    {
                        try
                        {
                            workItem.Procedure(workItem.Argument1, workItem.Argument2);
                            this.workItemsPerformed++;
                        }
                        catch
                        {
                            //- -
                            //- Swallow all errors caused by the work item.
                            //- But count how often this happens.
                            //- -
                            this.workItemsFailed++;
                        }
                    }
                }
            }
        }

        /
        /
        /
        private class BackgroundWorkerQueueItem
        {
            /
            /
            /
            private BackgroundWorkerProcedure procedure;

            /
            /
            /
            private object argument1;

            /
            /
            /
            private object argument2;

            /
            /
            /
            /
            /
            /
            public BackgroundWorkerQueueItem(
                BackgroundWorkerProcedure procedure,
                object argument1,
                object argument2)
            {
                this.procedure = procedure;
                this.argument1 = argument1;
                this.argument2 = argument2;
            }

            /
            /
            /
            public BackgroundWorkerProcedure Procedure
            {
                get { return this.procedure; }
            }

            /
            /
            /
            public object Argument1
            {
                get { return this.argument1; }
            }

            /
            /
            /
            public object Argument2
            {
                get { return this.argument2; }
            }
        }
    }
}
