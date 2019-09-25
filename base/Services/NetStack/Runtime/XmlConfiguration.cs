// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using NetStack.Common;
using System;
using System.Net;
using System.Text;
using System.Reflection;

using System.Net.IP;
using Drivers.Net;
using NetStack.Configuration;
using NetStack.Protocols;
using NetStack.NetDrivers;

namespace NetStack.Runtime
{
    /// <summary>
    /// Parses XML configuration file and instantiates runtime components.
    /// </summary>
    public class XmlConfiguration
    {
        string configFile;

        // the driver's path (for dynamic loading)
        protected string driversPath;

        // the protocols' path (for dynamic loading)
        // where the actual module reside
        protected string protocolsPath;

        public XmlConfiguration(string configFile)
        {
            this.configFile = configFile;
            if (System.IO.File.Exists(configFile) == false) {
                Core.Panic("Can't locate configuration file, Exit!");
            }
        }

        public XmlConfiguration()
        {
            // check if the file exists...
            // 1. check for <appName>.xml
            // 2. then for config.xml locally
            string appFullPath = AppDomain.CurrentDomain.BaseDirectory +
                AppDomain.CurrentDomain.FriendlyName;
            string configFile1 = AppDomain.CurrentDomain.BaseDirectory + @"config.xml";
            string configFile2 = appFullPath.Substring(0,appFullPath.Length-4) + @".xml";
            if (System.IO.File.Exists(configFile1)) {
                configFile = configFile1;
            }
            else if (System.IO.File.Exists(configFile2)) {
                configFile = configFile2;
            }
            else {
                Core.Panic("Can't locate configuration file, Exit!");
            }
        }

        // loads an adapter's driver and add the relevant data structures
        // for managing it.
        protected bool LoadAdapter(ProtocolParams args, string driversPath)
        {
            // the user can ignore an adapter
            // so ignore it...
            string ignore = args["ignore"];
            if (ignore != null && ignore == "true")
                return true;

            string name =
                ProtocolParams.LookupString(args, "name", "unknown");
            string typeName =
                ProtocolParams.LookupString(args, "type", "unknown");
            string id =
                ProtocolParams.LookupString(args, "id", "unknown");

            int mtu     = ProtocolParams.LookupInt32(args, "mtu",
                                                     EthernetFormat.MaxFrameSize);
            int txRing  = ProtocolParams.LookupInt32(args, "txRing", 64);
            int rxRing  = ProtocolParams.LookupInt32(args, "rxRing", 64);
            int fwQueue = ProtocolParams.LookupInt32(args, "fwQueue", 64);

            IAdapterFactory factory = null;
            IAdapter        adapter = null;
            try {
                string factoryTypeName = typeName + "Factory";
                Assembly assembly = Assembly.LoadFrom(driversPath);
                Type[] types      = assembly.GetTypes();
                foreach (Type t in types) {
                    if (t.IsClass && t.Name.Equals(typeName)) {
                        factory = (IAdapterFactory)Activator.CreateInstance(t, null);
                        break;
                    }
                    if (factory == null)
                        throw new Exception("Can't find Adapter's Factory.");

                    adapter = factory.CreateAdapter(name, id, txRing, rxRing);
                    Core.Instance().RegisterAdapter(adapter, fwQueue);
                }
            }
            catch (Exception e) {
                adapter = null;
                Console.Out.WriteLine(e.Message);
                Environment.Exit(1);
            }

            IPModule ipModule = Core.Instance().GetProtocolByName("IP") as IPModule;
            HostConfiguration hostConfig = ipModule.HostConfiguration;
            for (int i = 0;; i++) {
                string ipTag      = String.Format("ip{0}", i);
                string maskTag    = String.Format("mask{0}", i);
                string gatewayTag = String.Format("gateway{0}", i);

                // XXX No point-to-point support here.
                IPv4 address = ProtocolParams.LookupIPv4(args, ipTag,
                                                         IPv4.AllOnes);
                IPv4 netmask = ProtocolParams.LookupIPv4(args, maskTag,
                                                         IPv4.AllOnes);
                IPv4 gateway = ProtocolParams.LookupIPv4(args, gatewayTag,
                                                         IPv4.Zero);
                if (address == IPv4.AllOnes || netmask == IPv4.AllOnes) {
                    break;
                }
                hostConfig.Bindings.Add(adapter,
                    new InterfaceIPConfiguration(address, netmask, gateway, 128)
                    );
            }

#if DEBUG
            System.Console.Out.WriteLine("[Interface {0}]", args["name"]);
            System.Console.Out.WriteLine("-----------------------------");
#endif
            return true;
        }


        // This method dynamically loads a protocol and
        // initializes it.
        protected bool LoadProtocolModule(ProtocolParams args)
        {
            // the user can mark a protocol ignore field so
            // we just ignore it...
            string ignore = args["ignore"];
            if (ignore != null && ignore == "true")
                return true;
#if DEBUG
            System.Console.Out.WriteLine("[Protocol {0}]", args["name"]);
            foreach (string s in args.Keys)
                System.Console.Out.WriteLine("{0}={1}",s,args[s]);
            System.Console.Out.WriteLine("-----------------------------");
#endif
            // dynamic load the protocol
            // by default it is in the Runtime assembly
            string protocolType = args["type"];

            try {
                IProtocol protocol = (IProtocol)Activator.CreateInstance(Type.GetType(protocolType));

                if (protocol == null)
                    throw new Exception("Can't find Protocol's Class.");

                // initialize the protocol
                protocol.Initialize(args);
            }
            catch (Exception e) {
                Console.Out.WriteLine(String.Format("Can't load protocol class: {0}",protocolType));
                Console.Out.WriteLine(e.Message);
                return false;
            }
            return true;
        }

        // parse the configuration file return the root or
        // null if error.
        protected ConfigElement ParseConfiguration(bool toPrint)
        {
            ConfigElement root = null;
            root = ConfigFileParser.parseFile(configFile);
            if (root != null && toPrint) {
                System.Text.StringBuilder tree = new System.Text.StringBuilder();
                ConfigFileParser.printConfigurationTree(root,tree,0);
                System.Console.WriteLine(tree);
            }
            return root;
        }

        //handle host config
        protected void HandleConfiguration()
        {
            Core core = Core.Instance();

            // the path of the driver assembly
            ConfigElement config = ParseConfiguration(false);

            // we start with the configuration tag...
            // we assume that the XML is valid!

            // if we have children, and we have...
            if (config.ChildElements.Count > 0) {
                foreach (ConfigElement element in config.ChildElements) {
                    switch (element.TagName) {
                        case "creator":
                            break;
                        case "date":
                            break;
                        case "hostname":
                            break;
                        case "forwarding":
                            break;
                        case "OutQHandlerTimeout":
                            core.SetOutQueueHandlerInterval(Convert.ToInt32(element.Text,10));
                            break;
                        case "protocol-path":
                            protocolsPath = element.Text;
                            break;
                        case "drivers-path":
                            driversPath = element.Text;
                            break;
                        case "backlog-size":
                            int freeListSize = Convert.ToInt32(element.Text,10);
                            core.ProvisionDemux(
                                freeListSize,
                                EthernetFormat.MaxFrameSize
                                );
                            break;
                        case "protocols":
                            // handle the protocols
                            // use a generic scheme and apply
                            // it to the adapters in the future ;-)

                            // the args include the name and type!
                            ProtocolParams args = new ProtocolParams();;
                            foreach (ConfigElement prot in element.ChildElements) {
                                args.Clear();
                                foreach (string attr in prot.Attributes.Keys)
                                    args.Add(attr,prot.Attribute(attr));
                                foreach (ConfigElement protInfo in prot.ChildElements)
                                    args.Add(protInfo.TagName,protInfo.Text);
                                // done with one...
                                if (!LoadProtocolModule(args))
                                    Core.Panic("Error while loading Protocol");
                            }
                            break;
                        case "adapters":
                            // handle the adapters
                            ProtocolParams adArgs = new ProtocolParams();;
                            foreach (ConfigElement ad in element.ChildElements) {
                                adArgs.Clear();
                                foreach (string attr in ad.Attributes.Keys)
                                    adArgs.Add(attr,ad.Attribute(attr));
                                foreach (ConfigElement adInfo in ad.ChildElements)
                                    adArgs.Add(adInfo.TagName,adInfo.Text);
                                // done with one...
                                if (!LoadAdapter(adArgs,driversPath))
                                    Core.Panic("Error while loading an Adapter");
                            }
                            break;
                    }
                }
            }
        }

        public string ConfigurationFilename { get { return configFile; } }
    }
} // NetStack.Runtime
