// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

///
// Microsoft Research, Cambridge
// 

using System;

namespace NetStack
{
    namespace Runtime
    {
        ///
        // All the networking stack modules must implement
        // this interface. The runtime uses this interface
        // to manage the different modules.
        // 
        public interface INetModule
        {
            // get the module's name
            string ModuleName  { get; }

            // get the modules version
            ushort ModuleVersion { get; }

            // an initializer for new protocols.
            // the protocol receives the parameters
            // from the configuration file (string based)
            // NOTICE: should not rely on a specific initialization
            // order, wait to StartModule invocation for inter-module
            // operations!
            bool Initialize(ProtocolParams parameters);


            // start module activity, module specific.
            // it is called by the runtime after ALL protocols
            // are initialized and the host configuration is valid!
            bool StartModule();

            // stop module activity, module specific.
            // it is called by the runtime
            bool StopModule();

            // destroy module, free unmanaged resources if any.
            // it is called by the runtime
            bool DestroyModule();
        }
    }
}
