///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity / Netstack
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

#if false
using System;
using System.Collections;
using System.Diagnostics;
using System.Threading;

using Microsoft.SingSharp;
using Microsoft.Singularity;
using Microsoft.Singularity.Channels;

using Microsoft.Singularity.NetStack2;
using Microsoft.Singularity.NetStack;
using Microsoft.Singularity.NetStack.Common;
using Microsoft.Singularity.NetStack.Runtime;

using Drivers.Net;

namespace Microsoft.Singularity.NetStack2.NetDrivers
{
    public class FilterAdapter : IAdapter
    {
        IAdapter wrappedAdapter;
        private int txDroppedPackets;
        static ArrayList /*of TRef FilterEngineContract.Imp*/ filterEngineImpRefs =
            new ArrayList();

        public FilterAdapter(IAdapter wrappedAdapter)
        {
            this.wrappedAdapter = wrappedAdapter;
            this.txDroppedPackets = 0;
        }

        public static void AddFilterEngine(FilterEngineContract/*.Imp*/ imp)
        {
        filterEngineImpRefs.Add((imp));
        }

        public string DriverName
        {
            get { return wrappedAdapter.DriverName; }
        }

        public string DriverVersion
        {
            get { return wrappedAdapter.DriverVersion; }
        }

        public EthernetAddress HardwareAddress
        {
            get { return wrappedAdapter.HardwareAddress; }
        }

        public uint LinkSpeed
        {
            get { return wrappedAdapter.LinkSpeed; }
        }

        public string NicName
        {
            get { return wrappedAdapter.NicName; }
        }

        public bool ProcessIncomingPacket(Bytes data)
        {
            using (thisLock.Lock()) {

                foreach (FilterEngineContract/*.Imp*/ filterEngineImpRef in filterEngineImpRefs) {
            FilterEngineContract/*.Imp*/ filterEngineImp = filterEngineImpRef.Acquire();
            filterEngineImp.SendReceivedPacket(data);
            switch receive {
            case filterEngineImp.AcceptPacket(returnedHeader, returnedData):
                            data = returnedData;
                            //delete returnedHeader;
                            break; /* Continue and see if another filter will reject it */

            case filterEngineImp.RejectPacket(returnedHeader, returnedData):
                            data = returnedData;
                            //delete returnedHeader;
                            return false;

            case filterEngineImp.ModifyPacket(returnedHeader, returnedData):
                            data = returnedData;
                            //delete returnedHeader;
                break;
            }

                    filterEngineImpRef.Release(filterEngineImp);
                }
            }
            return true;
        }

        public void PopulateTxRing(Bytes header, Bytes data)
        {
            using (thisLock.Lock()) {
                // Process each sent packet and pass on the filtered versions.
                foreach (FilterEngineContract/*.Imp*/ filterEngineImpRef in filterEngineImpRefs) {
            FilterEngineContract/*.Imp*/ filterEngineImp = filterEngineImpRef.Acquire();
            filterEngineImp.SendSendingPacket(header, data);
            switch receive {
            case filterEngineImp.AcceptPacket(returnedHeader, returnedData):
                            header = returnedHeader;
                            data = returnedData;
                wrappedAdapter.PopulateTxRing(header, data);
                break;

            case filterEngineImp.RejectPacket(returnedHeader, returnedData):
                            header = returnedHeader;
                            data = returnedData;
                txDroppedPackets++;
                break;

            case filterEngineImp.ModifyPacket(returnedHeader, returnedData):
                            header = returnedHeader;
                            data = returnedData;
                wrappedAdapter.PopulateTxRing(header, data);
                break;
            }
                    filterEngineImpRef.Release(filterEngineImp);
                }
            }
        }
    }
}
#endif

