using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Threading;

namespace NuBuild
{
    class AsyncRunner
    {
        //- Breaking and examining variables on a second thread has caused strange VS behavior.
        //- As a debug-mode workaround, this flag runs everything on a single thread,
        //- sacrificing any IVerb.Execute() concurrency.
        const bool debugOneThread = false;

        VerbToposorter verbToposorter;

        ManualResetEvent completionEvent; //- threads executing verbs signal client Scheduler here

        ReaderWriterLock verbStateLock;  //- Protects runnableVerbs, startedVerbs, completedVerbs
        HashSet<IVerb> runnableVerbs;
        HashSet<IVerb> startedVerbs;
        //- Invariant: every verb that has ever been submitted appears in
        //- either runnableVerbs or startedVerbs. They stay in the latter
        //- forever so we never try to re-run one.


        int jobParallelism;

        public class TaskCompletion
        {
            public IVerb verb;
            public Disposition disposition;
            public TaskCompletion(IVerb verb, Disposition disposition)
            {
                this.verb = verb;
                this.disposition = disposition;
            }
        }
        List<TaskCompletion> taskCompletions;
        ReaderWriterLock taskCompletionsLock;

        int runningTasks;

        public AsyncRunner(VerbToposorter verbToposorter, int jobParallelism)
        {
            this.verbToposorter = verbToposorter;
            this.jobParallelism = jobParallelism;
            completionEvent = new ManualResetEvent(true);

            verbStateLock = new ReaderWriterLock();
            runnableVerbs = new HashSet<IVerb>();
            startedVerbs = new HashSet<IVerb>();

            taskCompletions = new List<TaskCompletion>();
            taskCompletionsLock = new ReaderWriterLock();

            runningTasks = 0;
        }

        public void submitVerb(IVerb verb)
        {
            verbStateLock.AcquireWriterLock(Timeout.Infinite);
            //- If lock contention were an issue, we could accumulate these
            //- on a thread-local collection, then batch them into runnableVerbs
            //- during the lock inside scheduleAndWait.
            if (!startedVerbs.Contains(verb))
            {
                runnableVerbs.Add(verb);
            }
            verbStateLock.ReleaseLock();
        }

        private void dbgUpdateProgress(Scheduler dbgScheduler)
        {
            dbgScheduler.dbgUpdateProgress(runnableVerbs.Count(), runningTasks);
        }

        public List<TaskCompletion> scheduleAndWait(Scheduler dbgScheduler)
        {
            while (true)
            {
                List<TaskCompletion> taskCompletionBatch;

                //- Loop until something gets done.
                while (true)
                {
                    dbgUpdateProgress(dbgScheduler);

                    taskCompletionsLock.AcquireWriterLock(Timeout.Infinite);
                    taskCompletionBatch = taskCompletions;
                    taskCompletions = new List<TaskCompletion>();
                    completionEvent.Reset();
                    taskCompletionsLock.ReleaseLock();

                    bool canProcessCompletedTask = (taskCompletionBatch.Count() > 0);
                    bool canStartNewTask = (runnableVerbs.Count()>0) && (jobParallelism > runningTasks);
                    if (!(canProcessCompletedTask || canStartNewTask))
                    {
                        //- Nothing will change until a running task finishes. Snooze.
                        if (runningTasks == 0)
                        {
                            dbgScheduler.dbgDumpWaitIndex();
                            Util.Assert(false);
                        }
                        completionEvent.WaitOne();
                        continue;
                    }
                    break;
                }

                int numCompletedTasks = taskCompletionBatch.Count();
                Say(String.Format("marking {0} tasks completing; runningTasks now {1}", numCompletedTasks, runningTasks));
                runningTasks -= numCompletedTasks;

                int idleTasks = jobParallelism - runningTasks;

                if (idleTasks > 0)
                {
                    verbStateLock.AcquireWriterLock(Timeout.Infinite);

                    List<IVerb> runnableVerbsBatch = new List<IVerb>(runnableVerbs);
                    Say("AsyncRunner toposorting " + runnableVerbsBatch.Count() + " verbs");
                    runnableVerbsBatch.Sort(verbToposorter);







                    for (int i = 0; i < idleTasks && i < runnableVerbsBatch.Count(); i++)
                    {
                        IVerb verb = runnableVerbsBatch[i];
                        startTask(verb);
                        runnableVerbs.Remove(verb);
                        startedVerbs.Add(verb);
                    }

                    verbStateLock.ReleaseLock();
                }

                if (taskCompletionBatch.Count() > 0 || runningTasks == 0)
                {
                    //- Something actually got done, so the caller could meaningfully schedule more work.
                    return taskCompletionBatch;
                }
            }
        }

        static void Say(string msg)
        {
            if (Scheduler.debug)
            {
#pragma warning disable 162
                Logger.WriteLine("[async] " + msg);
#pragma warning restore 162
            }
        }

        void startTask(IVerb verb)
        {
            runningTasks += 1;
            IVerbWorker worker = verb.getWorker();
            if (worker.isSync() == IsSync.Sync)
            {
                completeTask(verb, worker);
            }
            else
            {
                AsyncVerbTask task = new AsyncVerbTask(this, worker, verb);
                Say(String.Format("scheduling {0}", verb));
#pragma warning disable 162
                if (debugOneThread)
                {
                    task.Run();
                }
                else
                {
                    new Thread(new ThreadStart(task.Run)).Start();
                }
#pragma warning restore 162
            }
        }

        class AsyncVerbTask
        {
            AsyncRunner runner;
            IVerbWorker worker;

            //- Don't call any methods on this verb object from the async thread!
            //- It's just here to carry back to the TaskCompletion on the main thread.
            IVerb verb;

            public AsyncVerbTask(AsyncRunner runner, IVerbWorker worker, IVerb verb)
            {
                this.runner = runner;
                this.worker = worker;
                this.verb = verb;
            }

            public void Run()
            {
                Say(String.Format("launching {0}", verb));
                Logger.WriteLine(String.Format("{0} launched", verb));
                worker.runAsync();
                runner.completeTask(verb, worker);
                Say(String.Format("completed {0}", verb));
            }
        }

        void completeTask(IVerb verb, IVerbWorker worker)
        {
            taskCompletionsLock.AcquireWriterLock(Timeout.Infinite);
            Disposition disp = worker.complete();
            TaskCompletion tc = new TaskCompletion(verb, disp);
            taskCompletions.Add(tc);
            completionEvent.Set();
            taskCompletionsLock.ReleaseWriterLock();
        }
    }
}
