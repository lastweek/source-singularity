////////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:   Test utility program
//
using System;
using System.Diagnostics;
using System.Net.IP;

using Microsoft.Singularity;
using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Directory;
using Microsoft.SingSharp;
using NetStack.Contracts;
using NetStack.Channels.Public;

using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
[assembly: Transform(typeof(ApplicationResourceTransform))]

namespace Microsoft.Singularity.Applications
{

    [ConsoleCategory(HelpMessage="Test utility application", DefaultAction=true)]
    internal class DefaultConfig
    {
        [Endpoint]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;

        [Endpoint]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [Endpoint]
        public readonly TRef<IPContract.Imp:Start> ipRef;

        reflective internal DefaultConfig();

        internal int AppMain() {
            return  TestUtil.DefaultMain(this);
        }
    }

    public class TestUtil
    {

        public static void WriteInterfaceLine([Claims] InterfaceInfo ifInfo, string! ifName)
        {
            bool found = false;

            delete ifInfo.driverName;
            delete ifInfo.driverVersion;

            InterfaceIPInfo[] in ExHeap ipConfigs = ifInfo.ipConfigs;

            if (ipConfigs != null) {
                for (int i = 0; i < ipConfigs.Length; i++) {
                    InterfaceIPInfo ipc = ipConfigs[i];
                    IPv4 ipv4 = new IPv4(ipc.address);
                    
                    Console.WriteLine("TESTUTIL:IPAddress: {0,-14}", ipv4);
                    DebugStub.WriteLine("TESTUTIL:IPAddress:{0}:", __arglist(ipv4.ToString()));
                    found |= true;
                }
                delete ipConfigs;
            }

            if (found == false)
                DebugStub.WriteLine("TESTUTIL:IPAddress: Not available.");
        }


        internal static int DefaultMain(DefaultConfig! config)
        {
            IPContract.Imp ipConn = ((!)config.ipRef).Acquire();
            if (ipConn == null) { 
                throw new Exception("Unable to acquire handle to the IP network"); 
            } 
            ipConn.RecvReady(); 


            char[][]! in ExHeap ifNames;
            ipConn.SendGetInterfaces();
            ipConn.RecvInterfaceList(out ifNames);

            for (int i = 0; i < ifNames.Length; ++i) {
                CustomVector.Expose(ifNames, i);
                char[] in ExHeap ifName = ifNames[i];
                if (ifName == null)
                    throw new Exception("ifName is null");
                string! deviceName = Bitter.ToString2(ifName);
                CustomVector.UnExpose(ifNames, i);
                ipConn.SendGetInterfaceState(Bitter.FromString2(deviceName));
                switch receive {
                    case ipConn.InterfaceNotFound() :
                        Console.WriteLine("Unexpected error");
                        break;

                    case ipConn.InterfaceState(InterfaceInfo ifInfo) :
                        WriteInterfaceLine(ifInfo, deviceName);
                        break;

                    case ipConn.ChannelClosed() :
                        throw new Exception("ipConn channel closed");
                }
           }

           delete ifNames;
           delete ipConn;
           return 0; 
        }
    } // end class TestUtil
}
