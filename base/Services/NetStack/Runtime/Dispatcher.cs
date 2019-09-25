// ==++==
//
//   Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ==--==

// #define DEBUG_TCP

using System;
using System.Net.IP;
using System.Threading;

using RJBlack;

using Drivers.Net;

using NetStack.NetDrivers;

namespace NetStack.Runtime
{
    // This provides the basic dispatching of three types of events
    // 1. Internal events.  These are when one piece of code requests
    // that another piece of code is called as soon as it is done, but
    // it cannot be called immediately because of a re-entrancy issue.
    // 2. External events.  These events occur when some component
    // external to the stack (such as a client or a device driver)
    // indicate that some action is pending.
    // 3. Timers.  These events occur as a result of an external
    // activity, but once triggered are handled as internal events
    //
    // Internal events have priority over external events.  The
    // rationale for this may be found in the design documents.

    // XXX This code needs refactoring into platform specific
    // and generic components.
    public class Dispatcher
    {
        // Public interfaces by which we interact with components
        public delegate NetStatus Callback(CallbackArgs ca);
        public interface CallbackArgs  {}

        private uint swapCount = 0;
        private bool stopped = false;

        // Linked list of internal events
        private class Internal
        {
            public Callback fun;
            public CallbackArgs arg;
            public Internal next;
        }

        private Internal internalEventsHead;
        private Internal internalEventsTail;

        // This event is used to wake up the main dispatcher
        // thread, typically because we have changed the
        // list of events or timeouts to be serviced.
        // It lives in the first slot of eHandles.
        private AutoResetEvent dispatcherStrobe;

        // Timers have arguments too
        private Timer.TimerWheel! timers;
        private class Timer : RJBlack.Timer
        {
            public Callback fun;
            public CallbackArgs arg;
            public Timer(Callback fun, CallbackArgs arg, ulong time) : base(time)
            {
                this.fun = fun;
                this.arg = arg;
            }
        }

        // External events. eHandles[0] is special and
        // holds our internal strobe (dispatcherStrobe).
        private Callback [] eFuns;
        private CallbackArgs [] eArgs;
        private WaitHandle []! eHandles;

        // Public Methods
        public void AddCallback(Callback fun, CallbackArgs arg)
        {
            Internal internalEvent = new Internal();
            internalEvent.fun = fun;
            internalEvent.arg = arg;
            if (internalEventsHead == null) {
                internalEventsHead = internalEvent;
            }
            else {
                internalEventsTail.next = internalEvent;
            }
            internalEventsTail = internalEvent;

            // Make sure to wake up and notice this
            dispatcherStrobe.Set();
        }

        internal RJBlack.Timer! AddCallback(Callback fun, CallbackArgs args, ulong time)
        {
            Timer t = new Timer(fun, args, time);

            lock (timers) {
                timers.Add(t);
            }

            // Make sure to wake up and notice this
            dispatcherStrobe.Set();
            return t;
        }

        public void AddCallback(Callback fun, CallbackArgs arg, WaitHandle wh)
        {
            int n = eHandles.Length;
            WaitHandle [] newHandles = new WaitHandle[n + 1];
            Callback [] newFuns = new Callback[n + 1];
            CallbackArgs [] newArgs = new CallbackArgs[n + 1];

            if (n > 0) {
                // Lock to defend against the main loop shuffling the array
                // while we are copying it
                lock (eHandles.SyncRoot) {
                    eHandles.CopyTo(newHandles, 0);
                    eFuns.CopyTo(newFuns, 0);
                    eArgs.CopyTo(newArgs, 0);
                }
            }

            // Add the new callback to the end...
            newHandles[n] = wh;
            newFuns[n] = fun;
            newArgs[n] = arg;

            // Swap in the new arrays
            eHandles = newHandles;
            eFuns = newFuns;
            eArgs = newArgs;

            // Make sure to wake up and notice this
            dispatcherStrobe.Set();
        }

        // CALLER MUST HOLD A LOCK that ensures that
        // the eHandles, eFuns and eArgs array won't
        // change during this function call!
        private void RemoveWaitHandleCallback(int index)
        {
            int newLength = eHandles.Length - 1;

            if (newLength == 0) {
                eHandles = new WaitHandle[0];
                eFuns    = null;
                eArgs    = null;
                return;
            }

            int lhLength = index;
            int rhLength = newLength - index;

            // Allocate the replacement arrays
            WaitHandle []   newHandles = new WaitHandle[newLength];
            Callback []     newFuns    = new Callback[newLength];
            CallbackArgs [] newArgs    = new CallbackArgs[newLength];

            // Copy before the removed item...
            if (lhLength > 0) {
                Array.Copy(eHandles, 0, newHandles, 0, lhLength);
                Array.Copy(eFuns, 0, newFuns, 0, lhLength);
                Array.Copy(eArgs, 0, newArgs, 0, lhLength);
            }

            // Copy after the removed item...
            if (rhLength > 0) {
                Array.Copy(eHandles, index + 1, newHandles, index, rhLength);
                Array.Copy(eFuns, index + 1, newFuns, index, rhLength);
                Array.Copy(eArgs, index + 1, newArgs, index, rhLength);
            }

            // Swap in the replacement array
            eHandles = newHandles;
            eFuns    = newFuns;
            eArgs    = newArgs;

            // Make sure to wake up and notice this
            dispatcherStrobe.Set();
        }

        public void RemoveCallback(WaitHandle wh)
        {
            lock (eHandles.SyncRoot) {
                for (int i = 0; i < eHandles.Length; i++) {
                    if (((!)eHandles[i]).Equals(wh)) {
                        RemoveWaitHandleCallback(i);
                        return;
                    }
                }
            }
        }

        public bool RemoveTimeoutCallback(RJBlack.Timer! fun)
        {
            lock (timers) {
                return timers.Remove(fun);
            }
        }


        public void Stop()
        {
            stopped = true;

            // Make sure to wake up and notice this
            dispatcherStrobe.Set();
        }

        // Execute forever
        public void Execute()
        {
            while (stopped == false) {
                // Internal events first
                if (internalEventsHead != null) {
                    Internal internalEvent = internalEventsHead;
                    internalEventsHead = internalEvent.next;
#if DEBUG_TCP
                    Core.Log("Dispatching Internal Event at " +
                             DateTime.UtcNow.ToString() +
                             " calling '" + internalEvent.fun.ToString() +
                             "'.");
#endif
                    internalEvent.fun(internalEvent.arg);
                    continue;
                }

                // One read of NOW
                ulong now = (ulong)DateTime.UtcNow.Ticks;

                // Deal with timers
                TimeSpan waitTime = TimeSpan.MaxValue;

                lock (timers) {
                    Timer timer = (Timer)timers.Advance(now);

                    if (timer != null) {
                        // This timer has expired; service
                        // it immediately and start over
#if DEBUG_TCP
                        Core.Log("Timer Expiration at " +
                                 (new DateTime((long) now)).ToString() +
                                 " calling '" + timer.fun.ToString() +
                                 "'.");
#endif
                        timer.fun(timer.arg);
                        continue;
                    }

                    timer = (Timer)timers.GetSoonest();

                    if (timer != null) {
                        ulong soonest = timer.time;
                        if (soonest < now) {
                            Core.Log("Negative WaitTime");
                            waitTime = new TimeSpan(0L);
                        }
                        else {
                            waitTime = new TimeSpan((long)(soonest - now));
                        }
                    }
                }

                // Grab a copy of the external-event pointers so
                // we're not affected by changes to them on other
                // threads
                Callback[] funs = eFuns;
                CallbackArgs[] args = eArgs;
                WaitHandle[] handles = eHandles;

                // Shuffle the array values so the same tasks aren't
                // always preferred to others (WaitAny() will unblock
                // against the lowest-index WaitHandle in the array)
                lock (handles.SyncRoot) {
                    int n = handles.Length;

                    for (int i = 0; i < n - 1; ++i) {
                        // Swap the current element of the list with
                        // an entry that follow it. Instead of an
                        // expensive real random-number generator,
                        // generate a pseudo-random number by multiplying
                        // a largish prime with an increasing count
                        uint swapWith = (uint)(i + ((unchecked(53533511 * swapCount++)) % (n - i)));

                        if (swapWith != i) {
                            Callback swapFun = funs[swapWith];
                            CallbackArgs swapArgs = args[swapWith];
                            WaitHandle swapHandle = handles[swapWith];

                            funs[swapWith] = funs[i];
                            args[swapWith] = args[i];
                            handles[swapWith] = handles[i];

                            funs[i] = swapFun;
                            args[i] = swapArgs;
                            handles[i] = swapHandle;
                        }
                    }
                }

                int rc = WaitHandle.WaitAny(handles, waitTime);

                if (rc == WaitHandle.WaitTimeout)
                    continue;

                if (rc < 0 || rc >= handles.Length)
                    throw new ApplicationException("Invalid WaitAny");

                Callback cb = funs[rc];
                if (cb != null) {
                    NetStatus res = cb(args[rc]);

                    if (!NetStatus.SUCCEEDED(res))
                        Core.Panic("Error handling internal event.");
                }
            }

            Core.Log("NetStack dispatcher exiting...\n");
        }

        // Constructor
        public Dispatcher()
        {
            this.timers = new RJBlack.Timer.TimerWheel(10000, 16, (ulong)DateTime.UtcNow.Ticks);

            CallbackArgs[]! eArgs = this.eArgs = new CallbackArgs[1];

            Callback[]! eFuns = this.eFuns = new Callback[1];

            AutoResetEvent! dispatcherStrobe = this.dispatcherStrobe = new AutoResetEvent(false);
            WaitHandle[]! eHandles = this.eHandles = new WaitHandle[1];

            base();

            // The first eHandles element is always our private strobe
            eHandles[0] = dispatcherStrobe;
            eArgs[0] = null;
            eFuns[0] = null;
        }

    } // Dispatcher

} // NetStack
// End
