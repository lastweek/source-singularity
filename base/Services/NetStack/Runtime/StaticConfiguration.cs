///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Netstack / Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   StaticConfiguration.cs
//

using System.Collections;

#if SINGULARITY
using Drivers.Net;
using Microsoft.Singularity.Io;
using Microsoft.Singularity;
#endif

namespace NetStack.Runtime
{
    /// <summary> A class that Initializes, Starts, and Stops the default
    /// set of IP modules.
    /// </summary>
    public class StaticConfiguration
    {
        static ArrayList modules;
        static bool running = false;
        static bool initialized = false;

        public static void Initialize()
        {
            using (ImpatientWatcher watcher = new ImpatientWatcher("NetStack starting", "Starting core", 100)) {
                modules = new ArrayList();
                modules.Add(Core.Instance());
                modules.Add(new IPModule());
                modules.Add(new ArpModule());
                modules.Add(new IcmpModule());
                modules.Add(new TcpModule());
                modules.Add(new UdpModule());

                foreach (INetModule! module in modules) {
                    watcher.NextStep("Starting module " + module.ModuleName, 100);
                    bool success = module.Initialize(null);
                    if (!success)
                        Core.Log("Error: Module '{0}' failed to initialize.", module.ModuleName);
                }
                initialized = true;
            }
        }

        public static void Start()
        {
            if (running) {
                return;
            }
            running = true;

            Core.Instance().Activate();
            Core.Instance().StartModule();
        }

        public static void Stop()
        {
            if (!running) {
                return;
            }
            running = false;

            modules.Reverse();
            foreach (INetModule! module in modules) {
                bool success;
                using (ImpatientWatcher watcher = new ImpatientWatcher("stopping net module " + module.ModuleName, "Calling module.StopModule()", 500)) {
                success = module.StopModule();
                }
                if (!success) {
                    Core.Log("Module '{0}' indicates that it failed to stop.", module.ModuleName);
                }
            }
        }
    }
}
