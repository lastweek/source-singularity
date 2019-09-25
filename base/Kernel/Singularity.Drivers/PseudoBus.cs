///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   PseudoBus.cs
//
//  Note:
//

using Microsoft.Singularity.Channels;
using Microsoft.Singularity.Io;

using System;
using System.Collections;

namespace Microsoft.Singularity.Drivers
{
    // create the resource object for CTR to fill in
    [DriverCategory]
    [Signature("/root/pseudobus0")]
    [EnumeratesDevice("pseudo/...")]
    internal class PseudoBusResources : DriverCategoryDeclaration
    {
    }

    /// <summary>
    /// Bus for pseudo-devices.  A pseudo-device is typically a
    /// layer in I/O stack that may or may not be associated
    /// with one or more physical devices.
    /// </summary>
    public class PseudoBus : IBusDevice
    {
        public const string Name = "/pseudo0";

        private static PseudoBus instance = null;

        private SortedList! pseudoDevices;

        internal PseudoBus()
        {
            pseudoDevices = new SortedList();
        }

        void IDevice.Initialize()
        {
            DebugStub.Print("Initializing PseudoBusDevice.\n");

            instance = this;

            RegisterBootPseudoDevices();
        }

        void IDevice.Finalize()
        {
        }

        internal void RegisterPseudoDevice(string! name, IoConfig config)
        {
            pseudoDevices.Add(name, config);
        }

        SortedList IBusDevice.Enumerate()
        {
            return pseudoDevices;
        }

        //
        // Register boot time pseudo devices
        //
        internal void RegisterBootPseudoDevices()
        {
            // Pseudo Devices have no resources (I/O ports, memory, etc.)
            if (instance != null) {
                PseudoConfig config = new PseudoConfig("iotest");
                instance.RegisterPseudoDevice("/test/iotest", config);
            }
        }

        // Allows us to be registered as a root level driver
        public PseudoConfig! ReportConfig()
        {
            PseudoConfig config = new PseudoConfig("root");

            return config;
        }
    }

    public class PseudoConfig : IoConfig
    {
        static private int count = 0;

        public PseudoConfig(string className)
        {
            string[] ids = { String.Format("/pseudo0{0}/{1}", className, count++) };
            this.Ids = ids;
        }

        public override string! ToString()
        {
            assert Ids != null;
            assert Ids.Length > 0;
            string id = Ids[0];
            assert id != null;
            return id;
        }

        public override string ToPrint()
        {
            return ToString();
        }
    }
}

