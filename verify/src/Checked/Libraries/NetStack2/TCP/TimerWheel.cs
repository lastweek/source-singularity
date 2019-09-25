///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:
//
//  Note: Based on "Hashed and Hierarchical Timing Wheels: Efficient
//        Data Structures for Implementing a Timer Facility"
//        George Varghese and Anthony Lauck IEEE TON 1997 (updated '87 SOSP paper)
//
//        Big idea: if your wheel is large enough such that no event in the future
//        will wrap past the current pointer into the wheel then all diciontary events are
//        O(1).  Removal is O(1) by keeping a pointer from the object into the wheel list.

//#define DEBUG_TIMER_WHEEL

using System;
using Drivers.Net;
using System.Net.IP;
using System.Threading;
using System.Diagnostics;

using Microsoft.Singularity;
using SchedulerTime = System.DateTime;

namespace Microsoft.Singularity.NetStack2
{
    public class TimerWheel: IThreadStart
    {
        [Conditional("DEBUG_TIMER_WHEEL")]
        internal static void DebugPrint(string           format,
                                        params object [] arguments)
        {
            DebugStub.Print("TimerWheel: {0}",
                            DebugStub.ArgList(
                                string.Format(format, arguments))
                            );
        }

        [Conditional("DEBUG_TIMER_WHEEL")]
        internal static void DebugPrint(string format)
        {
            DebugStub.Print("TimerWheel: {0}",
                            DebugStub.ArgList(format));
        }

        private const int DefaultWheelSize = 256;

        public abstract class TimerDelegate
        {
            public abstract void Run(TCP tcpSession);
        }

        private LinkedList[] timerEntries;
        private int tickFrequency;
        private int tickIndex;
        private int wheelSize;
        private AutoResetEvent tickEvent;
        private MonitorLock objectLock;

        public class TimerEvent
        {
            public TCP tcpSession;
            public TimerDelegate timerDelegate;

            public TimerEvent(TCP tcpSession, TimerDelegate timerDelegate)
            {
                this.tcpSession = tcpSession;
                this.timerDelegate = timerDelegate;
            }
        }

        private void RunWheel()
        {
            tickEvent = new AutoResetEvent(false);

            SchedulerTime nextTick;
            TCP tcpSession;

            while(true) {
                nextTick = SchedulerTime.Now;
                nextTick = nextTick.AddMilliseconds(tickFrequency);
                bool rc = tickEvent.WaitOne(nextTick);
                VTable.Assert(rc == false);

                bool done = false;
                while(done == false) {
                    TimerEvent timerEvent;
                    using (this.objectLock.Lock()) {
                        LinkedList timersList = timerEntries[tickIndex];
                        VTable.Assert(timersList != null);
                        if (timersList.Count == 0) {
                            tickIndex = (tickIndex + 1) % wheelSize;
                            done = true;
                            break;
                        }

                        LinkedListNode currentNode = timersList.head;
                        VTable.Assert(currentNode != null);
                        timerEvent = currentNode.theObject as TimerEvent;
                        DebugStub.Assert (timerEvent != null);
                        VTable.Assert(timerEvent != null);
                        tcpSession = timerEvent.tcpSession;
                        VTable.Assert(tcpSession != null);
                    }
                    VTable.Assert(timerEvent != null);
                    VTable.Assert(tcpSession != null);
                    timerEvent.timerDelegate.Run(tcpSession);
                }
                tickIndex = (tickIndex + 1) % wheelSize;
            }
        }

        public void AddTimerEvent(int msInTheFuture,
                                  TCP tcpSession,
                                  TimerDelegate timerDelegate,
                                  ref LinkedListNode timerLLNode)
        {
            if (timerLLNode != null) {
                return;
            }
            int numTicks = msInTheFuture / tickFrequency;
            DebugPrint("AddTimerEvent adding {0} = {1} ticks frequency {2}\n",
                       msInTheFuture, numTicks, tickFrequency);
            int index = (tickIndex + numTicks) % wheelSize;
            DebugStub.Assert(numTicks < wheelSize);
            using (this.objectLock.Lock()) {
                LinkedList timersList = timerEntries[index];
                VTable.Assert(timersList != null);
                TimerEvent timerEvent = new TimerEvent(tcpSession, timerDelegate);
                timerLLNode = timersList.InsertHead(timerEvent);
            }
        }

        public bool DeleteTimerEvent(ref LinkedListNode timerLLNode)
        {
            DebugPrint("DeleteTimerEvent\n");
            using (this.objectLock.Lock()) {
                if (timerLLNode != null) {
                    LinkedList linkedList = timerLLNode.parent;
                    TimerEvent timerEvent = linkedList.Remove(timerLLNode) as TimerEvent;
                    VTable.Assert(timerEvent != null);
                    timerEvent.tcpSession = null;
                    timerLLNode = null;

                    return true;
                }
            }
            return false;
        }


        //tick frequency is in ms
        //this timer wheel operates under the invariant tha
        //no event will be so long as to go past the current tickIndex!!!
        //insertion, deletion, tick are all O(1)
        [Microsoft.Contracts.NotDelayed]
        public TimerWheel(int wheelSize, int tickFrequency)
        {
            DebugPrint("New timer wheel wheelSize {0} tickFrequency (ms) {1}\n",
                       wheelSize, tickFrequency);

            timerEntries = new LinkedList[wheelSize];
            for (int i = 0; i < wheelSize; i++) {
                timerEntries[i] = new LinkedList();
            }
            tickIndex = 0;
            this.tickFrequency = tickFrequency;
            this.wheelSize = wheelSize;
            this.objectLock = new MonitorLock();

            Thread newThread = new Thread(this);
            newThread.Start();
        }

        public void Run()
        {
            RunWheel();
        }

        [Microsoft.Contracts.NotDelayed]
        public TimerWheel(int tickFrequency)
        {
            this.wheelSize = DefaultWheelSize;
            DebugPrint("New timer wheel wheelSize {0} tickFrequency (ms) {1}\n",
                       wheelSize, tickFrequency);

            timerEntries = new LinkedList[wheelSize];
            for (int i = 0; i < DefaultWheelSize; i++) {
                timerEntries[i] = new LinkedList();
            }

            tickIndex = 0;
            this.tickFrequency = tickFrequency;
            this.objectLock = new MonitorLock();

            Thread newThread = new Thread(this);
            newThread.Start();
        }
    }
}
