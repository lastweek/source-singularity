///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   NetStack.sg
//
//  Note:
//

#if false
using System;
using System.Runtime.InteropServices;
using System.Runtime.CompilerServices;
using System.Threading;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.Security;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Io.Net;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.ServiceManager;
using Microsoft.Singularity.NetStack;
using Microsoft.Singularity.NetStack2.Channels.Nic;

//[assembly: ApplicationPublisherAttribute("singularity.microsoft.com")]
//[assembly: AssertPrivilegeAttribute("$register-privilege.localhost")]

namespace Microsoft.Singularity.NetStack2
{
    using NetStack2.Channels.Private;
    using NetStack2.Channels.Nic;

    //[Category("Service")]
    internal class ServiceParameters
    {
        //[Endpoint(Affinity=1)]
        public readonly /*TRef<NicDeviceContract.Imp>*/ContractRef NicEndpointRef;

        //[EndpointArray(Affinity=1)]
        public readonly /*TRef<NicDeviceContract.Imp>*/ContractRef[] nicRefs;
    }

    /// <summary>
    /// The NetStack Application class is a single instance service running
    /// on a host.  When it runs it attempts to register as /service/netstack;
    /// success indicates no other instances and it then initializes
    /// the various NetStack subsystems.
    /// </summary>
    class NetStackApplication
    {
        NetStackApplication(ServiceParameters parameters)
        {
            routingManager = new RoutingExpManager();
            ipManager = new IPContract();

            this.nicRefs = parameters.nicRefs;
        }

        readonly RoutingExpManager routingManager;
        readonly IPContract ipManager;
        readonly /*TRef*/NicDeviceContract/*.Imp*/[] nicRefs;

        bool Start()
        {
            try {
                ipManager.Start();
                routingManager.Start();

                for (int i = 0; i < nicRefs.Length; i++) {
                    NicDeviceContract/*.Imp*/ imp = (nicRefs[i]).Acquire();
                    Nic.CreateAndRegister(imp, String.Format("/dev/nic{0}", i));
                }

                return true;
            }
            catch (Exception ex) {
                Dbg("An exception occurred during service startup: " + ex.Message);
                return false;
            }
        }

        void Stop()
        {
            // Stop the service provider threads.
            Dbg("Stopping service provider threads");
            routingManager.Stop();
            ipManager.Stop();

            // StaticConfiguration.Stop() walks the list of installed modules and calls
            // the StopModule() method of each.  We do this after stopping the service
            // provider threads.
            Dbg("Stopping protocol modules");
        }

        internal static int AppMain(ServiceParameters parameters)
        {
            NicDeviceContract/*.Imp*/ nicImp  = parameters.NicEndpointRef.Acquire();
            nicImp.RecvSuccess();
            //delete nicImp;
            DebugStub.WriteLine("Closed nic contract via reflection\n");

            ARP arp = new ARP();
            IP.Initialize(arp);
            Ethernet.Initialize(arp);

            NetStackApplication app = new NetStackApplication(parameters);

            try {
                return app.Run();
            }
            finally {
                //delete app;
                Dbg("NetStack is terminating.");
            }
        }

        int Run()
        {
                if (Start()) {
                    svcontrol.SendStartSucceeded();
                    ServiceMain();
                    Stop();
                    return 0;
                }
                else {
                    Dbg("Sending StartFailed to Service Manager.");
                    svcontrol.SendStartFailed(ServiceError.Unknown);
                    Stop();
                    return -1;
                }
        }

        static void Dbg(string line)
        {
            DebugStub.WriteLine(line);
        }

        static void Dbg(string format, params object[] args)
        {
            Dbg(String.Format(format, args));
        }
    }
}
#endif
