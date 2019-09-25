// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;

namespace NetStack.Runtime
{
    /// <summary>
    /// Static class maintains a pool of Tcp Sessions kept as a FILO (Stack).
    /// </summary>
    public static class TcpSessionPool
    {
        // Session Recycle to GC ratio as a Rational Approximation.
        // BUGBUG: When 992 and 1024 fixed, set to UInt64.Max or remove
        private const long SessionRecycleToGCRANumerator = 1ul;
        private const long SessionRecycleToGCRADenominator = 256ul;
        private static long rationalApproximationCurrentValue =
            TcpSessionPool.SessionRecycleToGCRADenominator / -2;
        
        static TcpModule tcpModule;
        static Stack tcpSessions = new Stack();

        static ulong getCalls = 0;
        static ulong allocations = 0;
        static ulong recycleCalls = 0;

        public static void SetTcpModule(TcpModule tcpModule)
        {
            TcpSessionPool.tcpModule = tcpModule;
        }

        public static TcpSession! Get()
        {
            TcpSession! tcpSession;
            lock (TcpSessionPool.tcpSessions) {
                TcpSessionPool.getCalls++;
                
                if(tcpSessions.Count <= 0) {
                    TcpSessionPool.allocations++;
                    tcpSession = new TcpSession(tcpModule);
                }
                else {
                    tcpSession = (TcpSession!) tcpSessions.Pop();
                    assert(tcpSession.IsClosed);
                    Core.Instance().DeregisterSession(tcpSession.Protocol, tcpSession);
                    tcpSession =
                        TcpSessionPool.tcpModule.ReInitializeSession(tcpSession);
                }
            }
            
            return tcpSession;
        }

        public static void Recycle(TcpSession! tcpSession)
        {
            assert(tcpSession.IsClosed);

            // Under Exclusion, count call and add to (free) list.
            lock (TcpSessionPool.tcpSessions) {
                TcpSessionPool.recycleCalls++;
                tcpSessions.Push(tcpSession);
                // TODO: Occasionally (1/1024 times?) free a session to
                //  lower usage from highwater mark to high average at the
                //  cost of some additional Alloc/Free cycles.
            }

            // Run the CG every N/D session recycles to avoid Bugs 992 and 1024.
            // Can be done after every session if searching for memory leaks.
            TcpSessionPool.rationalApproximationCurrentValue +=
                TcpSessionPool.SessionRecycleToGCRANumerator;
            while (TcpSessionPool.rationalApproximationCurrentValue > 0) {
                TcpSessionPool.rationalApproximationCurrentValue -=
                    TcpSessionPool.SessionRecycleToGCRADenominator;
                GC.Collect();           // Free memory and fill finalizer Q.
                GC.WaitForPendingFinalizers();  // Dispose non-managed stuff
                GC.Collect();           // Free memory release by finalizing
            }
        }
    }
}
