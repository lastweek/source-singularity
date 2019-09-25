// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Text;
using Microsoft.Build.Framework;

#if ENABLE_INTEROP
using System.Runtime.InteropServices;
using System.Threading;
using Windows;
#endif

namespace Microsoft.Singularity.BuildTasks
{
    public abstract class TaskBase : Microsoft.Build.Framework.ITask
    {
        protected TaskBase()
        {
            _taskname = null;
            _disableMessagePumping = true;
        }

        string _taskname;

        protected string TaskName
        {
            get {
                if (_taskname == null) {
                    _taskname = this.GetType().Name;
                }
                return _taskname;
            }
            set { _taskname = value; }
        }

        protected void LogMessage(string msg)
        {
            BuildMessageEventArgs e = new BuildMessageEventArgs(msg, null, this.TaskName, MessageImportance.Normal);
            _engine.LogMessageEvent(e);
        }

        protected void LogError(string msg)
        {
            BuildErrorEventArgs e = new BuildErrorEventArgs(null, null, null, 0, 0, 0, 0, msg, null, this.TaskName);
            _engine.LogErrorEvent(e);
        }

        protected void LogMessage(MessageImportance importance, string msg)
        {
            BuildMessageEventArgs e = new BuildMessageEventArgs(msg, null, this.TaskName, importance);
            _engine.LogMessageEvent(e);
        }

        protected abstract bool Execute();

        bool ITask.Execute()
        {
            if (_engine == null)
                throw new InvalidOperationException("The BuildEngine property must be set before calling the Execute method.");

#if false
            if (_host == null)
                throw new InvalidOperationException("The Host property must be set before calling the Execute method.");
#endif

            if (_disableMessagePumping)
                return this.Execute();

            bool returnValue = false;
            ExecuteMethodAndPump(delegate() { returnValue = this.Execute(); });
            return returnValue;
        }

        ITaskHost _host;
        IBuildEngine _engine;

        public IBuildEngine BuildEngine
        {
            get { return _engine; }
            set { _engine = value; }
        }

        public ITaskHost HostObject
        {
            get { return _host; }
            set { _host = value; }
        }

        bool _disableMessagePumping;

        public bool DisableMessagePumping
        {
            get { return _disableMessagePumping; }
            set { _disableMessagePumping = value; }
        }

#if ENABLE_INTEROP
        #region Code for pumping messages while executing tasks

        unsafe void ExecuteMethodAndPump(SimpleMethod method)
        {
            if (method == null)
                throw new ArgumentNullException("method");

            if (_disableMessagePumping) {
                LogMessage("Message pumping is disabled - executing method directly");
                method();
                return;
            }

            if (Thread.CurrentThread.GetApartmentState() == ApartmentState.MTA) {
                LogMessage("Message pumping is disabled - this thread is an MTA thread");
                method();
                return;
            }

            bool quit = false;
            uint mainThreadId = Kernel32.GetCurrentThreadId();
            // LogMessage("main thread id = " + mainThreadId);
            Exception worker_exception = null;

            Thread thread = new Thread(delegate()
            {
                try {
                    method();
                    worker_exception = null;
                }
                catch (Exception ex) {
                    worker_exception = ex;
                }
                quit = true;
                User32.PostThreadMessageW(mainThreadId, User32.WM_NULL, IntPtr.Zero, IntPtr.Zero);
            });

            thread.Start();

            for (;;) {
                if (quit) {
                    // LogMessage("Main thread received quit notification.  Quitting.");
                    break;
                }

                MSG msg = new MSG();
                if (Windows.User32.GetMessageW(& msg, IntPtr.Zero, 0, 0)) {
                    User32.TranslateMessage(&msg);
                    User32.DispatchMessageW(&msg);
                }
                else {
                    LogMessage("Received WM_QUIT or GetMessage failed!  Bailing.");
                    break;
                }
            }

            // LogMessage("Waiting for worker thread to finish...");
            thread.Join();
            // LogMessage("Worker thread is done.");

            if (worker_exception != null) {
                throw worker_exception;
            }
        }

        void ExecuteMethodAndPumpThreadMain(object untyped_method)
        {
            SimpleMethod method = (SimpleMethod)untyped_method;
        }

        #endregion
#endif


        #region Helper methods that don't have a better place to live.

        protected bool ValidateCSharpIdentifier(string name, string id, bool allowDots)
        {
            if (String.IsNullOrEmpty(id)) {
                LogError(String.Format("The parameter '{0}' is required, but no value was provided.", name));
                return false;
            }

            if (!Util.ValidateCSharpIdentifier(id, allowDots)) {
                LogError(String.Format("The value '{0}' provided to parameter '{1}' is not a valid C# identifier.", id, name));
                return false;
            }

            return true;
        }

        #endregion


    }

    delegate void SimpleMethod();
}
