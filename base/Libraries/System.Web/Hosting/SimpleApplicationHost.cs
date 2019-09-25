////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Note:
//    This file was ported from the Coriolis codebase to Singularity.
//

namespace System.Web.Hosting
{
    using System;
    using System.Collections;
    using System.Diagnostics;
    using System.Globalization;
    using System.Web;
    using System.Web.Util;
    using System.IO;

    public class SimpleApplicationHost : IApplicationHost {

        private String _appVirtualPath;
        private String _appPhysicalPath;
        private String _installPath;
        private String _clientScriptPath;
        private String _clientScriptVirtualPath;

        public SimpleApplicationHost(string virtualPath, string physicalPath) {
            _appVirtualPath = virtualPath;

            String directorySeparatorString = new String(Path.DirectorySeparatorChar, 1);
            _appPhysicalPath = physicalPath.EndsWith(directorySeparatorString) ? physicalPath : physicalPath + directorySeparatorString;

            // This has been hard-coded for Singularity
            _installPath = "/cassini";
            _clientScriptPath = Path.Combine(_installPath, "asp.netclientfiles");
            _clientScriptVirtualPath = "/aspnet_client/system_web/";
        }

        protected String ClientScriptPath { get { return _clientScriptPath; } }
        protected String ClientScriptVirtualPath { get { return _clientScriptVirtualPath; } }
        protected IntPtr ConfigToken { get { return IntPtr.Zero; } }
        protected String SiteName { get { return "Default Web Site"; } }

        public String PhysicalPath { get { return _appPhysicalPath; } }
        public String InstallPath { get { return _installPath; } }
        public String VirtualPath { get { return _appVirtualPath; } }

        protected void MessageReceived() {
        }

        protected bool IsHostProcessMultiInstance() {
            return false;
        }

        public virtual Object InitializeLifetimeService() {
            return null; // never expire lease
        }

        // IApplicationHost implementation
        String IApplicationHost.GetVirtualPath() {
            return VirtualPath;
        }

        String IApplicationHost.GetPhysicalPath() {
            return PhysicalPath;
        }

        IntPtr IApplicationHost.GetConfigToken() {
            return ConfigToken;
        }

        String IApplicationHost.GetSiteName() {
            return SiteName;
        }

        void IApplicationHost.MessageReceived() {
            MessageReceived();
        }

        bool IApplicationHost.IsHostProcessMultiInstance() {
            return IsHostProcessMultiInstance();
        }
    }
}
