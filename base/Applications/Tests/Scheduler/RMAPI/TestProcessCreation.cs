///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Diagnostics;
using System.Collections;
using System.Threading;
using Microsoft.SingSharp;
using Microsoft.Singularity.UnitTest;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Channels;

namespace Microsoft.Singularity.Applications
{
    /// <summary>
    ///     Test cases for creating processes in parallel.
    /// </summary>
    internal sealed class TestProcessCreation
    {
        private const int numThreads = 16;
        private const int iterations = 16;
        private const string commandLine = "fib";
        private static int idGenerator;
        private static ManualResetEvent evtGate;

        /// <summary>
        ///     Run test to create processes. The child processes don't output 
        ///     to the console. Instead, we swallow their output with a null pipe.
        /// </summary>
        internal static void RunWithNoChildOutput()
        {
            Console.Write("    test parallel process creation with no child output... ");

            evtGate = new ManualResetEvent(false);

            // Start the worker threads
            Thread[] threads = new Thread[numThreads];
            for (int i = 0; i < threads.Length; i++) {
                threads[i] = new Thread(new ThreadStart(ProcessCreationMainWithNoOutput));
                ((!)threads[i]).Start();
                Thread.Yield();
            }

            // Give the worker threads a bit time to initialize
            // then signal the start
            Thread.Sleep(1000);
            evtGate.Set();

            // Wait for all worker threads to finish
            for (int i = 0; i < threads.Length; i++) {
                ((!)threads[i]).Join();
            }

            // If we didn't crash, then this test is successful.
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Run test to create processes in parallel. The child
        ///     processes output to the console through PipeMultiplexer.
        /// </summary>
        internal static void RunWithChildOutput()
        {
            Console.Write("    test parallel process creation with child output... ");

            evtGate = new ManualResetEvent(false);

            // Start the worker threads
            WorkerThread[] threads = new WorkerThread[numThreads];
            for (int i = 0; i < threads.Length; i++) {
                PipeMultiplexer! mux = CreatePipeMultiplexer();
                WorkerThread worker = new WorkerThread(mux);
                worker.thread = new Thread(worker.ThreadRoutine);
                threads[i] = worker;
            }

            // We want to create all of the muxes first, then create
            // all of the threads, then start them.

            foreach (WorkerThread! worker in threads) {
                worker.thread.Start();
                Thread.Yield();
            }

            // Give the worker threads a bit time to initialize
            // then signal the start
            Thread.Sleep(1000);
            evtGate.Set();

            // Wait for all worker threads to finish
            foreach (WorkerThread! worker in threads) {
                worker.thread.Join();
            }

            foreach (WorkerThread! worker in threads) {
                PipeMultiplexer! mux = worker.muxRef.Acquire();
                delete mux;
            }

            // If we didn't crash, then this test is successful.
            Console.WriteLine();
            Console.WriteLine("OK");
        }

        /// <summary>
        ///     Thread main function that creates processes. The child
        ///     processes don't output to the console. Instead, we swallow
        ///     their output with a null pipe.
        /// </summary>
        private static void ProcessCreationMainWithNoOutput()
        {
            int id = Interlocked.Increment(ref idGenerator) - 1;

            NullPipeControl.Imp:START! control = StartNullPipe();
            DirectoryServiceContract.Imp! directoryService = 
                    DirectoryService.NewClientEndpoint();

            // Wait for the signal
            evtGate.WaitOne();

            // Create many processes
            Process[] children = new Process[iterations];
            try {
                for (int i = 0; i < iterations; i++) {
                    UnicodePipeContract.Imp! childStdInImp;
                    UnicodePipeContract.Exp! childStdInExp;
                    UnicodePipeContract.NewChannel(out childStdInImp, out childStdInExp);

                    UnicodePipeContract.Imp! childStdOutImp = CreateNullPipeClient(control);

                    //Manifest manifest;
                    children[i] = Binder.CreateProcess(directoryService,
                            new string[1]{commandLine}, childStdInExp, childStdOutImp);
                    delete childStdInImp;
                    if (children[i] == null) {
                        throw new ProcessCreateException("Failed to create process");
                    }
                    
                    ((!)children[i]).Start();
                    if (id == 0) {
                        Console.Write('.');
                    }
                }
            }
            finally {
                delete directoryService;
                delete control;
            }

            // Wait for all children to finish
            for (int i = 0; i < children.Length; i++) {
                ((!)children[i]).Join();
            }
        }

        private contract NullPipeControl 
        {
            in message NewInput(UnicodePipeContract.Exp:EXPMOVABLE! client);
            out message Ack();

            state START: NewInput? -> Ack! -> START;
        }

        private static UnicodePipeContract.Imp:READY! CreateNullPipeClient(
                NullPipeControl.Imp:START! control) 
        {
            UnicodePipeContract.Imp! client;
            UnicodePipeContract.Exp! exp;
            UnicodePipeContract.NewChannel(out client, out exp, 
                        UnicodePipeContract.EXPMOVABLE.Value);
            control.SendNewInput(exp);
            switch receive {
                case control.Ack():
                    switch receive {
                        case client.Moved():
                            return client;

                        case client.ChannelClosed():
                            throw new ProcessCreateException(
                                    "Failed to create null pipe: client receve");
                    }

                 case control.ChannelClosed():
                    throw new ProcessCreateException(
                            "Failed to create null pipe: control receive");
            }
        }

        private static NullPipeControl.Imp:START! StartNullPipe()
        {
            NullPipeControl.Imp! controlImp;
            NullPipeControl.Exp! controlExp;
            NullPipeControl.NewChannel(out controlImp, out controlExp);

            NullPipeThread pipeThread = new NullPipeThread(controlExp);

            Thread t = new Thread(new ThreadStart(pipeThread.PumpMessage));
            t.Start();
            return controlImp;
        }

        private class NullPipeThread 
        {
            TRef<NullPipeControl.Exp:START>! controlExp;

            internal NullPipeThread([Claims] NullPipeControl.Exp:START! control)
            {
                this.controlExp = new TRef<NullPipeControl.Exp:START>(control);
            }

            internal void PumpMessage() 
            {
                NullPipeControl.Exp:START! control = this.controlExp.Acquire();
                ESet<UnicodePipeContract.Exp:READY> clients = 
                    new ESet<UnicodePipeContract.Exp:READY>();

                bool done = false;

                try {
                    while (!done) {
                        switch receive {

                        case control.NewInput(client):
                            client.SendMoved();
                            clients.Add(client);
                            control.SendAck();
                            break;

                        case control.ChannelClosed():
                            done = true; 
                            break;

                        case client.Write(buffer, index, count) in clients:
                            client.SendAckWrite(buffer);
                            clients.Add(client);
                            continue;

                        case client.ChannelClosed() in clients:
                            delete client;
                            continue;
                        }
                    }
                }
                finally {
                    clients.Dispose();
                    delete control;
                }
            }
        }

        private class WorkerThread
        {
            public WorkerThread([Claims]PipeMultiplexer! mux)
            {
                this.muxRef = new TContainer<PipeMultiplexer>(mux);
            }

            public TContainer<PipeMultiplexer>! muxRef;

            public Thread thread;

            public void ThreadRoutine()
            {
                int totalProcessesCreated = 0;
                int goalCountProcessesCreated = 0x100;
                int maxActiveProcesses = 0x10;

                ArrayList processes = new ArrayList();

                PipeMultiplexer! mux = muxRef.Acquire();
                
                DirectoryServiceContract.Imp! rootdir = DirectoryService.NewClientEndpoint();

                try {

                    for (;;) {
                        Thread.Yield();

                        // scan child processes and remove dead ones
                        int i = 0;
                        while (i < processes.Count) {
                            Process! process = (Process!)processes[i];
                            if (process.Join(TimeSpan.Zero)) {
                                // oooo, it's dead.
                                // Debug.WriteLine(String.Format("yay, process {0} died", process.Id));
                                process.Dispose(true);
                                processes.RemoveAt(i);
                            }
                            else {
                                // process not dead yet
                                i++;
                            }
                        }


                        bool canCreateProcess = (processes.Count < maxActiveProcesses
                            && totalProcessesCreated < goalCountProcessesCreated);

                        if (canCreateProcess) {
                            string[] childArgs = new string[1]{ commandLine };
                            Process process = Binder.CreateProcess(rootdir, childArgs, mux);
                            if (process == null) {
                                Debug.WriteLine("FAILED to create child process.");
                                Debugger.Break();
                                break;
                            }
                            processes.Add(process);
                            process.Start();
                            // Debug.WriteLine(String.Format("created child process (id {0}), this is {1}/{2}", process.Id, totalProcessesCreated, goalCountProcessesCreated));
                            totalProcessesCreated++;
                        }

                        if (!canCreateProcess) {
                            // Debug.WriteLine("snore");
                            Thread.Sleep(250);
                        }

                        if (processes.Count == 0 && totalProcessesCreated == goalCountProcessesCreated) {
                            Debug.WriteLine("goal has been created.  worker thread terminating.");
                            break;
                        }
                    }

                    foreach (Process! process in processes) {
                        Debug.WriteLine("Terminating child process: " + process.Id);
                        process.Stop();
                    }
                    foreach (Process! process in processes) {
                        Debug.WriteLine("Waiting for child process: " + process.Id);
                        process.Join();
                        process.Dispose(true);
                    }
                    processes.Clear();
                }
                finally {
                    delete rootdir;
                    muxRef.Release(mux);
                }
            }
        }

        // Redirect our standard output into a multiplexer so we can interleave
        // output from child processes
        private static PipeMultiplexer! CreatePipeMultiplexer()
        {
            // Swap our real stdOut with a newly created one
            UnicodePipeContract.Exp! newOutputExp;
            UnicodePipeContract.Imp! newOutputImp;
            UnicodePipeContract.NewChannel(out newOutputImp, out newOutputExp);
            UnicodePipeContract.Imp stdOut = ConsoleOutput.Swap(newOutputImp);
            if (stdOut == null) {
                throw new Exception("test expects a STDOUT pipe");
            }
            // Use a mux to splice our own output together with the child
            // processes we will run.
            return PipeMultiplexer.Start(stdOut, newOutputExp);
        }

    }
}
