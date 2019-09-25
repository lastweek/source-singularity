///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File: AdapterInfo.cs
//

using NetStack.Common;
using System.Net.IP;
using Drivers.Net;

namespace NetStack.Runtime
{
    public class AdapterInfo
    {
        //
        // Fixed fields
        //
        private IAdapter adapter;
        private string   deviceName;

        //
        // Mutable fields
        //
        private string  description;

        public AdapterInfo(IAdapter adapter,
                           string   deviceName,
                           string   description)
        {
            this.adapter     = adapter;
            this.deviceName  = deviceName;
            this.description = description;
        }

        public AdapterInfo(IAdapter adapter,
                           string   deviceName)
        {
            this.adapter     = adapter;
            this.deviceName  = deviceName;
            this.description = "";
        }

        public IAdapter Adapter
        {
            get { return adapter; }
        }

        public EthernetAddress Address
        {
            get { return adapter.HardwareAddress; }
        }

        public string DeviceName
        {
            get { return this.deviceName; }
        }

        public string DriverName
        {
            get { return adapter.DriverName; }
        }

        public string DriverVersion
        {
            get { return adapter.DriverVersion; }
        }

        public string Description
        {
            get { return description; }
            set { description = value; }
        }
    }
}
