///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   TcpExpManager.sg
//  Author: maiken
//  Note:   Provider-side helper for the IP Channel Contract
//

#if false
using System.Threading;
using System.Net.IP;
using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.NetStack;
using System.Collections;
using System;

namespace Microsoft.Singularity.NetStack2.Channels.Private
{
    public class TcpExpManager : StoppableThread
    {
        private /*TRef*/ServiceProviderContract/*.Exp*/ spRef;

        public TcpExpManager(ServiceProviderContract/*.Exp*/ spRef)
        {
            this.spRef = spRef;
        }

        protected override void Run(StopThreadContract/*.Exp*/ terminator)
        {
            ServiceProviderContract/*.Exp*/ nsExp = spRef.Acquire();

            // Here is the set of client channels we service
            ESet<TcpContract/*.Exp*/ epSet = new ESet<TcpContract/*.Exp*/();

            while (true) {
                switch receive {
                    //
                    // Don't forget that we're selecting TcpContract endpoints
                    // from the epSet endpoint-set. In each case that we
                    // receive a message from one of those endpoints, we
                    // need to remember to put the endpoint back into epSet
                    // if we want to keep listening to it.
                    //
                    case ep.CreateTcpSession(TcpConnectionContract/*.Exp*/:Start newEP) in epSet :
                        {
                            // Transition the endpoint to the ReadyState
                            newEP.SendReady();
                            // Create a dedicated thread to service this connection
                            TcpConnectionExpThread tcpThread = new TcpConnectionExpThread(newEP);
                            tcpThread.Start();
                            ep.SendAck();
                            epSet.Add(ep);
                        }
                        break;

#if false
                    case ep.AddFilterEngine(FilterEngineContract/*.Imp*/:Start newEP) in epSet :
                        {
                            newEP.SendReady();
                            NetStack2.NetDrivers.FilterAdapter.AddFilterEngine(newEP);
                            ep.SendAck();
                            epSet.Add(ep);
                        }
                        break;
#endif

                    case nsExp.Connect(ServiceContract/*.Exp*/:Start newEp) :
                        {
                            // We expect people top give us TcpContract/*.Exp*/ instances
                            //TcpContract/*.Exp*/:Start newTcpEp = newEp as TcpContract/*.Exp*/;
                            TcpContract/*.Exp*/ newTcpEp = newEp as TcpContract/*.Exp*/;

                            if (newTcpEp == null) {
                                // Invalid contract type. Fail.
                                nsExp.SendNackConnect(newEp);
                            }
                            else {
                                // Signal ready and start servicing this contract
                                nsExp.SendAckConnect();
                                newTcpEp.SendReady();
                                epSet.Add(newTcpEp);
                            }
                        }
                        break;

                    case ep.ChannelClosed() in epSet:
                        //delete ep;
                        break;

                    case nsExp.ChannelClosed():
                        // Exit this thread
                        goto quit;

                    case terminator.Terminate():
                        terminator.SendAckTerminate();
                        goto quit;

                    case terminator.ChannelClosed():
                        goto quit;

                }
            }

        quit:
            //delete nsExp;
            epSet.Dispose();
        }
    }
}
#endif
