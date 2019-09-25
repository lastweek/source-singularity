///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   UdpExpManager.sg
//
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
    public class UdpExpManager : StoppableThread
    {
        private /*TRef*/ServiceProviderContract/*.Exp*/ spRef;

        public UdpExpManager(ServiceProviderContract/*.Exp*/ spRef)
        {
            this.spRef = spRef;
        }

        protected override void Run(StopThreadContract/*.Exp*/ terminator)
        {
            ServiceProviderContract/*.Exp*/ nsExp = spRef.Acquire();

            // Here is the set of client channels we service
            ESet<UdpContract/*.Exp*/ epSet = new ESet<UdpContract/*.Exp*/();

            while (true) {
                switch receive {
                    //
                    // Don't forget that we're selecting UdpContract endpoints
                    // from the epSet endpoint-set. In each case that we
                    // receive a message from one of those endpoints, we
                    // need to remember to put the endpoint back into epSet
                    // if we want to keep listening to it.
                    //
                    case ep.CreateUdpSession(UdpConnectionContract/*.Exp*/:Start newEP) in epSet :
                        {
                            // Move the endpoint to the ReadyState
                            newEP.SendReady();
                            // Create a dedicated thread to service this connection
                            UdpConnectionExpThread udpThread = new UdpConnectionExpThread(newEP);
                            udpThread.Start();
                            ep.SendAck();
                            epSet.Add(ep);
                        }
                        break;

                    case nsExp.Connect(ServiceContract/*.Exp*/:Start newEp) :
                        {
                            // We expect people top give us
                            // UdpContract/*.Exp*/ instances
                            // UdpContract/*.Exp*/:Start newUdpEp = newEp
                            // as UdpContract/*.Exp*/;
                            UdpContract/*.Exp*/ newUdpEp = newEp as UdpContract/*.Exp*/;

                            if (newUdpEp == null) {
                                // Invalid contract type. Fail.
                                nsExp.SendNackConnect(newEp);
                            }
                            else {
                                // Signal ready and start
                                // servicing this contract
                                nsExp.SendAckConnect();
                                newUdpEp.SendReady();
                                epSet.Add(newUdpEp);
                            }
                        }
                        break;

                    case ep.ChannelClosed() in epSet :
                        //delete ep;
                        break;

                    case nsExp.ChannelClosed():
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
