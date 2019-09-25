////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   ThreadLocalServiceRequest.cs
//
//  Note:
//

using Microsoft.Singularity;
using System.Runtime.CompilerServices;

namespace System.Threading
{
    internal enum ThreadLocalServiceRequestTag
    {
        SuspendProcess,
        SuspendProcessRecursive,
        ResumeProcess,
        ResumeProcessRecursive,
        StopProcess,
        ThreadStopped,
    }

    // Some service request objects should not be allocated on demand, because
    // they are needed in low-memory situations.  To handle these situations, each
    // thread contains a preallocated, reusable ThreadLocalServiceRequest
    // object whose tag describes the precise purpose of each request.
    // This object should only be used by its own thread.  The thread
    // will block until the request is finished.  After one request finishes,
    // the thread may reuse its ThreadLocalServiceRequest for another
    // request.
    public class ThreadLocalServiceRequest : ServiceRequest
    {
        ThreadLocalServiceRequestTag tag;
        Process targetProcess; // only relevant to SuspendProcess, SuspendProcessRecursive, ResumeProcess, ResumeProcessRecursive, StopProcess
        Thread targetThread; // only relevant to ThreadStopped
        int exitCode; // only relevant to StopProcess
        AutoResetEvent requestFinished = new AutoResetEvent(false);
        bool processStarted; // only relevant to SuspendProcess, ResumeProcess

        [CLSCompliant(false)]
        public static bool SuspendProcess(Process process, bool recursive)
        {
            ThreadLocalServiceRequest req = Thread.CurrentThread.localServiceRequest;
            req.tag = (recursive)?
                (ThreadLocalServiceRequestTag.SuspendProcessRecursive):
                (ThreadLocalServiceRequestTag.SuspendProcess);
            req.targetProcess = process;
            ServiceThread.Request(req);
            req.requestFinished.WaitOne();
            return req.processStarted;
        }

        [CLSCompliant(false)]
        public static bool ResumeProcess(Process process, bool recursive)
        {
            ThreadLocalServiceRequest req = Thread.CurrentThread.localServiceRequest;
            req.tag = (recursive)?
                (ThreadLocalServiceRequestTag.ResumeProcessRecursive):
                (ThreadLocalServiceRequestTag.ResumeProcess);
            req.targetProcess = process;
            ServiceThread.Request(req);
            req.requestFinished.WaitOne();
            return req.processStarted;
        }

        [CLSCompliant(false)]
        public static void StopProcess(Process process, int exitCode)
        {
            ThreadLocalServiceRequest req = Thread.CurrentThread.localServiceRequest;
            req.tag = ThreadLocalServiceRequestTag.StopProcess;
            req.targetProcess = process;
            req.exitCode = exitCode;
            ServiceThread.Request(req);
            req.requestFinished.WaitOne();
            process.Join();
        }

        [NoHeapAllocation]
        [CLSCompliant(false)]
        public static void ThreadStopped(Thread threadToStop)
        {
            ThreadLocalServiceRequest req = threadToStop.localServiceRequest;
            req.tag = ThreadLocalServiceRequestTag.ThreadStopped;
            req.targetThread = threadToStop;
            ServiceThread.Request(req);
        }

        protected override internal void Service()
        {
            try {
                switch (tag) {
                    case ThreadLocalServiceRequestTag.SuspendProcess:
                        processStarted = targetProcess.ServiceSuspend(false);
                        break;
                    case ThreadLocalServiceRequestTag.SuspendProcessRecursive:
                        processStarted = targetProcess.ServiceSuspend(true);
                        break;
                    case ThreadLocalServiceRequestTag.ResumeProcess:
                        processStarted = targetProcess.ServiceResume(false);
                        break;
                    case ThreadLocalServiceRequestTag.ResumeProcessRecursive:
                        processStarted = targetProcess.ServiceResume(true);
                        break;
                    case ThreadLocalServiceRequestTag.StopProcess:
                        targetProcess.ServiceStop(exitCode);
                        break;
                    case ThreadLocalServiceRequestTag.ThreadStopped:
                        targetThread.ServiceStopped();
                        break;
                }
            }
            finally {
                requestFinished.Set();
            }
        }
    }
}
