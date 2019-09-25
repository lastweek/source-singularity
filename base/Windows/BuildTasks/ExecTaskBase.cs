// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

//
//
//This file contains code for running an external program, as an MSBuild task.
//It is essentially a replacement for the Exec task, and this implementation
//solves a problem with the MSBuild Exec task implementation.  The MSBuild
//version does not pump messages while it waits for the external program.
//This means that Exec is practically useless for building from within Visual
//Studio, because Visual Studio invokes the MSBuild engine (and therefore
//all of its tasks) on the VS GUI thread.
//
//The key problem is that we need to meet all of these needs:
//
//Receive stdout and stderr messages and call IBuildEngine.LogMessage on 
//the same thread that called ITask.Execute().
//
//Receive notification of the termination of child process.
//
//Receive and dispatch USER32 (GUI) messages, on the same thread that
//called ITask.Execute().
//
//I tried a lot of different approaches, and none of them were satisfying.
//In the end, the simplest and most reliable approach was to use P/Invoke
//to directly call USER32!GetMessage, TranslateMessage, and DispatchMessage
//directly.  The background (worker) threads wake up the main thread by
//posting WM_NULL to the main thread.  Rather than communicating data by
//passing values in the wParam or lParam, we use a CLR monitor lock to
//synchronize access to a shared data structure.  The worker threads lock
//that data structure, modify it (queue messages), then unlock and post
//a message to the main thread.  Whenever the main thread returns from
//calling GetMessage, it locks the shared data structure and checks to
//see if it needs to do any work.  This is simple and reliable.
//
//Since we're P/Invoking directly to Win32, some of the fancy CLR wiring
//will be disabled while we're waiting for GetMessage or DispatchMessage.
//Fine -- I tried forty different ways of implementing this, and they are
//all severe pains in the neck, and I am sick of coddling the broken
//threading model and incomplete managed API.  Directly calling into USER32 
//is the least painful option of all.
//
//

using System;
using System.Runtime.InteropServices;
using System.IO;
using System.Threading;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text;
using System.Text.RegularExpressions;
using Microsoft.Build.Framework;
using Windows;
using System.ComponentModel;

namespace Microsoft.Singularity.BuildTasks
{
    public abstract class ExecTaskBase : TaskBase
    {
        ///
        //<summary>
        //  This method executes a program and redirects its output to the MSBuild
        //  logger.
//
        //  This method pumps STA messages while the program is executing.  This is
        //  necessary in order to keep the VS IDE responsive, since the IDE (to my
        //  great horror) invokes MSBuild on its UI thread.
        //</summary>
        //

        protected bool ExecuteProgram(string exepath, IEnumerable<String> args)
        {
            if (_showDetailedProgramArguments) {
                LogMessage("Arguments:");
                foreach (string arg in args) {
                    LogMessage("   " + arg);
                }
            }

            // Now build the single-string command line that we will execute.

            StringBuilder buffer = new StringBuilder();

            // buffer.Append(AddQuotesIfNecessary(sgc_exe));

            foreach (string arg in args) {
                buffer.Append(' ');
                bool needs_quotes = Util.NeedsQuotes(arg);
                if (needs_quotes)
                    buffer.Append("\"");
                buffer.Append(arg);
                if (needs_quotes)
                    buffer.Append("\"");
            }

            string args_single_string = buffer.ToString();

            return ExecuteProgram(exepath, args_single_string);
        }

        bool _showDetailedProgramArguments;
        public bool ShowDetailedProgramArguments
        {
            get { return _showDetailedProgramArguments; }
            set { _showDetailedProgramArguments = value; }
        }

        bool _showCommandLine;
        public bool ShowCommandLine
        {
            get { return _showCommandLine; }
            set { _showCommandLine = value; }
        }

        ProcessPriorityClass _processPriorityClass = ProcessPriorityClass.Normal;
        public ProcessPriorityClass ProcessPriorityClass
        {
            get { return _processPriorityClass; }
            set
            {
                if (!Enum.IsDefined(typeof(ProcessPriorityClass), value))
                    throw new InvalidEnumArgumentException("ProcessPriorityClass", (int)value, typeof(ProcessPriorityClass));
                _processPriorityClass = value;
            }
        }

        protected bool ExecuteProgram(string exepath, string args)
        {
            if (String.IsNullOrEmpty(exepath)) {
                LogError("Internal error: No program path was specified for task.");
                return false;
            }

            try {
                if (_showCommandLine)
                    LogMessage(MessageImportance.High, exepath + " " + args);

                // Create the process and execute it.

                this.messages = new Queue<String>();

                using (Process process = new Process())
                using (AutoResetEvent pushEvent = new AutoResetEvent(false)) {
                    this.process = process;
                    this.notifyMainEvent = pushEvent;

                    process.StartInfo.UseShellExecute = false;
                    process.StartInfo.FileName = exepath;
                    process.StartInfo.Arguments = args;
                    process.StartInfo.CreateNoWindow = true;
                    process.StartInfo.RedirectStandardInput = true;
                    process.StartInfo.RedirectStandardOutput = true;
                    process.StartInfo.RedirectStandardError = true;

                    Closure stdout_pump = this.PumpStdout;
                    Closure stderr_pump = this.PumpStderr;
                    Closure exit_watcher = this.WaitForProcessExit;

                    process.Start();
                    process.PriorityClass = _processPriorityClass;
                    process.StandardInput.Close();

                    IAsyncResult stdout_result = stdout_pump.BeginInvoke(null, null);
                    IAsyncResult stderr_result = stderr_pump.BeginInvoke(null, null);
                    IAsyncResult exit_result = exit_watcher.BeginInvoke(null, null);

                    IntPtr pushEventHandle = pushEvent.SafeWaitHandle.DangerousGetHandle();

                    // Dequeue lines from stdout/stderr in batches.
                    string[] dequeued_lines = new string[0x20];

                    bool quit = false;
                    while (!quit) {

                        Kernel32.WaitResult waitResult;
                        unsafe { waitResult = User32.MsgWaitForMultipleObjects(1, &pushEventHandle, false, User32.InfiniteTimeout, User32.QS_ALLEVENTS); }

                        switch (waitResult) {
                            case Kernel32.WaitResult.Object0: {
                                    // One of the worker threads has changed shared state.
                                    bool has_more_lines;
                                    do {
                                        int dequeued_line_count = 0;

                                        lock (SharedStateLock) {
                                            // Acknowledge signal from worker threads.
                                            Debug.Assert(notifyingMain, "Expected notifyingMain to be true");

                                            for (;;) {
                                                if (messages.Count == 0) {
                                                    has_more_lines = false;
                                                    break;
                                                }
                                                if (dequeued_line_count == dequeued_lines.Length) {
                                                    has_more_lines = true;
                                                    break;
                                                }
                                                string line = messages.Dequeue();
                                                dequeued_lines[dequeued_line_count] = line;
                                                dequeued_line_count++;
                                            }

                                            if (!has_more_lines && processExited && stdoutDone && stderrDone) {
                                                quit = true;
                                            }

                                            // If we are not going to run the lock-loop again (no more lines available), then allow
                                            // worker threads to signal pushEvent again.
                                            if (!has_more_lines)
                                                notifyingMain = false;
                                        }

                                        for (int i = 0; i < dequeued_line_count; i++) {
                                            string line = dequeued_lines[i];
                                            dequeued_lines[i] = null;
                                            LogMessage(MessageImportance.High, line);
                                        }
                                    } while (has_more_lines);
                                    break;
                                }

                            case Kernel32.WaitResult.Object1: {
                                    // A USER32 message is ready.
                                    unsafe {
                                        MSG msg;
                                        if (User32.PeekMessageW(& msg, IntPtr.Zero, 0, 0, User32.PM_REMOVE)) {
                                            User32.TranslateMessage(&msg);
                                            User32.DispatchMessageW(&msg);
                                        }
                                        else {
                                            Debug.WriteLine("Received WM_QUIT, or PeekMessage failed");
                                            break;
                                        }
                                    }
                                    break;
                                }

                            case Kernel32.WaitResult.Timeout:
                                // Should never happen
                                Debug.Fail("MsgWaitForMultipleObjects returned WAIT_TIMEOUT?!");
                                break;

                            case Kernel32.WaitResult.Failed:
                                break;

                            default:
                                Debug.Fail("Unrecognized return value from MsgWaitForMultipleObjects");
                                break;
                        }
                    }

                    // Synchronize with the termination of the worker routines.
                    // This is equivalent to Thread.Join(), but we used async delegates, not threads.
                    // EndInvoke is guaranteed to wait for the async operation to complete.
                    exit_watcher.EndInvoke(exit_result);
                    stdout_pump.EndInvoke(stdout_result);
                    stderr_pump.EndInvoke(stderr_result);

                    process.StandardOutput.Close();
                    process.StandardInput.Close();

                    process.WaitForExit();

                    if (process.ExitCode == 0) {
                        LogMessage("Process exited successfully.");
                        return true;
                    }
                    else {
                        LogError("The compiler terminated with an error code.");
                        return false;
                    }
                }
            }
            finally {
                this.process = null;
                this.notifyMainEvent = null;
                this.messages = null;
            }
        }

        private object SharedStateLock { get { return this; } }

        public Process process;
        public bool processExited;
        public bool stdoutDone;
        public bool stderrDone;
        public bool notifyingMain;
        public AutoResetEvent notifyMainEvent;
        public Queue<String> messages;

        void WriteLine(string line)
        {
            lock (SharedStateLock) {
                messages.Enqueue(line);
                NotifyMainThreadLocked();
            }
        }

        void PumpStream(StreamReader reader)
        {
            if (reader == null)
                return;

            for (;;) {
                string line;
                try {
                    line = reader.ReadLine();
                }
                catch (Exception ex) {
                    WriteLine("exception from reader: " + ex.Message);
                    break;
                }
                if (line == null)
                    break;

                lock (SharedStateLock) {
                    WriteLine(line);
                }
            }
        }

        public void PumpStdout()
        {
            PumpStream(process.StandardOutput);
            lock (SharedStateLock) {
                stdoutDone = true;
                NotifyMainThreadLocked();
            }
        }

        public void PumpStderr()
        {
            PumpStream(process.StandardError);
            lock (SharedStateLock) {
                stderrDone = true;
                NotifyMainThreadLocked();
            }
        }

        internal void NotifyMainThreadLocked()
        {
            if (notifyingMain)
                return;
            notifyingMain = true;
            notifyMainEvent.Set();
        }

        public void WaitForProcessExit()
        {
            process.WaitForExit();
            lock (SharedStateLock) {
                this.processExited = true;
                NotifyMainThreadLocked();
            }
        }
        static readonly Regex diagnosticRegex = new Regex(@"(?<filename> [a-zA-Z0-9._-]+?):(?<msg>.*)$", RegexOptions.IgnorePatternWhitespace);

        void ParseAndLogProcessOutputLine(string line)
        {
            Match match = diagnosticRegex.Match(line);
            if (match.Success) {

                string msg = match.Groups["msg"].Value;
                string filename = match.Groups["filename"].Value;
                // BuildMessageEventArgs e = new BuildMessageEventArgs(line, null, null, MessageImportance.Normal);
                Console.WriteLine("msg      ({0})", msg);
                Console.WriteLine("filename ({0})", filename);

                LogMessage(MessageImportance.High, line);

            }
            else {
                LogMessage(MessageImportance.High, line);
            }
        }
    }

    delegate void Closure();

    class InvalidTaskParametersException : Exception
    {
        public InvalidTaskParametersException()
            : base("One or more parameters for this task are not valid.")
        {
        }

        public InvalidTaskParametersException(string msg)
            : base(msg)
        {
        }

    }
}
