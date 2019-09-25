///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

#define DEBUG_INTEL

using Microsoft.SingSharp;

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Io.Net;
using Microsoft.Singularity.Directory;
using Microsoft.Singularity.V1.Services;

using System;
using System.Threading;

namespace Microsoft.Singularity.Drivers.Network.Intel
{
    internal class IntelDeviceChannel: NicDeviceContract
    {
        Intel device;

        public IntelDeviceChannel(
            Intel theDevice
            )
        {
            this.device  = theDevice;
        }

        public PacketFifo GiveTxPacketsToDevice(PacketFifo txFifo)
        {
            device.PopulateTsmtBuffer(txFifo);
            device.DrainTsmtBuffer(txFifo);
            return txFifo;
        }

        public PacketFifo GiveRxPacketsToDevice(PacketFifo rxFifo)
        {
            device.PopulateRecvBuffer(rxFifo);
            device.DrainRecvBuffer(rxFifo);
            return rxFifo;
        }

        public void RegisterForEvents(NicDeviceEventContract eventExp)
        {
            device.SetEventRelay(new IntelEventRelay(eventExp));
        }

        public void SetChecksumProperties(ChecksumSupport checksum)
        {
            if ((checksum & ~Intel.ChecksumSupport) == 0) {
                // TODO: Running with checksumming on anyway...
                // but should be responsive to this request.
            }
            else {
                throw new Exception("SetChecksumProperties: UnsupportedChecksumProperties");
            }
        }

        public void StartIO()
        {
            device.StartIo();
        }

        public void StopIO()
        {
            device.StopIo();
        }

        public NicDeviceProperties GetDeviceProperties()
        {
            NicDeviceProperties dp = new NicDeviceProperties();
            GetDeviceProperties(dp);
            return dp;
        }

        public void ConfigureIO()
        {
        }

        private void GetDeviceProperties(NicDeviceProperties dp)
        {
                //delete dp.DriverName;
                dp.DriverName = device.DriverName;

                //delete dp.DriverVersion;
                dp.DriverVersion = device.DriverVersion;

                dp.MacType    = MacType.Ethernet;
                //delete dp.MacAddress;
                dp.MacAddress = device.getMacAddress;

                dp.ChecksumSupport         = Intel.ChecksumSupport;
                dp.MtuBytes                = (int)Intel.MtuBytes;
                dp.MaxRxFragmentsPerPacket = (int)Intel.MaxRxFragmentsPerPacket;
                dp.MaxTxFragmentsPerPacket = (int)Intel.MaxTxFragmentsPerPacket;
                dp.MaxRxPacketsInDevice    = (int)Intel.MaxRxPackets;
                dp.MaxTxPacketsInDevice    = (int)Intel.MaxTxPackets;
        }
    }
}
