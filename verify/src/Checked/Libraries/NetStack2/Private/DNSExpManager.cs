///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   DNSExpManager.gs
//
//  Note:   Provider-side helper for the IP Channel Contract
//

#if false
using System.Threading;
using System.Net.IP;
using System.Collections;
using System;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;

using Microsoft.Singularity.NetStack;

namespace Microsoft.Singularity.NetStack2.Channels.Private
{
    public class DNSExpManager : StoppableThread
    {
        private /*TRef*/ServiceProviderContract/*.Exp*/ spRef;

        public DNSExpManager(ServiceProviderContract/*.Exp*/ spRef)
        {
            this.spRef = spRef;
        }

        override protected void Run(StopThreadContract/*.Exp*/ terminator)
        {
            ServiceProviderContract/*.Exp*/ nsExp = spRef.Acquire();

            bool run = true;
            while (run) {
                switch receive {
                    case nsExp.Connect(ServiceContract/*.Exp*/:Start newEp) :
                        {
                            // We expect people to give us DnsContract/*.Exp*/ instances
                            DnsContract/*.Exp*/ newDnsEp = newEp as DnsContract/*.Exp*/;

                            if (newDnsEp == null) {
                                // Invalid contract type. Fail.
                                nsExp.SendNackConnect(newEp);
                            }
                            else {
                                // Signal ready and start servicing this contract
                                nsExp.SendAckConnect();
                                newDnsEp.SendReady();

                                // Spin up a new servicing thread
                                DNSExpConnection newConn = new DNSExpConnection(newDnsEp);
                                newConn.Start();
                            }
                        }
                        break;

                    case nsExp.ChannelClosed():
                        // Exit this thread
                        run = false;
                        break;

                    case terminator.Terminate():
                        terminator.SendAckTerminate();
                        run = false;
                        break;

                    case terminator.ChannelClosed():
                        run = false;
                        break;
                }
            }

            //delete nsExp;
        }
    }
}
#endif

