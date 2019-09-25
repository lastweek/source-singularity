//------------------------------------------------------------------------------
//   Copyright (c) Microsoft Corporation. All Rights Reserved.
//------------------------------------------------------------------------------

namespace Microsoft.VisualStudio.WebHost
{
    using System;
    using System.Collections;
    using System.Diagnostics;
    using System.Globalization;
    using System.Net;
    using System.Net.Sockets;
    using System.Text;
    using System.Threading;
    using System.Web.Hosting;

    internal sealed class Host : IRegisteredObject {
        private Server _server;

        private int _port;
        private string _virtualPath;
        private string _lowerCasedVirtualPath;
        private string _lowerCasedVirtualPathWithTrailingSlash;
        private string _physicalPath;
        private string _physicalClientScriptPath;
        private string _lowerCasedClientScriptPathWithTrailingSlash;

        public void Configure(Server server, int port, string virtualPath, string physicalPath, string clientScriptVirtualPath, string clientScriptPath) {
            _server = server;

            _port = port;
            _virtualPath = virtualPath;
            _lowerCasedVirtualPath = _virtualPath.ToLower();
            _lowerCasedVirtualPathWithTrailingSlash = virtualPath.EndsWith("/") ? virtualPath : virtualPath + "/";
            _lowerCasedVirtualPathWithTrailingSlash = _lowerCasedVirtualPathWithTrailingSlash.ToLower();
            _physicalPath = physicalPath;
            _physicalClientScriptPath = clientScriptPath + "\\";
            _lowerCasedClientScriptPathWithTrailingSlash = (clientScriptVirtualPath + "/").ToLower();
        }

        public void ProcessRequest(Connection conn) {
            Request request = new Request(this, conn);
            request.Process();
        }

        public void Shutdown() {
        }


        void IRegisteredObject.Stop(bool immediate) {
            if (_server != null)
                _server.HostStopped();
        }

        public string NormalizedClientScriptPath {
            get {
                return _lowerCasedClientScriptPathWithTrailingSlash;
            }
        }

        public string NormalizedVirtualPath {
            get {
                return _lowerCasedVirtualPathWithTrailingSlash;
            }
        }

        public string PhysicalClientScriptPath {
            get {
                return _physicalClientScriptPath;
            }
        }

        public string PhysicalPath {
            get {
                return _physicalPath;
            }
        }

        public int Port {
            get {
                return _port;
            }
        }

        public string VirtualPath {
            get {
                return _virtualPath;
            }
        }

        public bool IsVirtualPathInApp(String path) {
            bool isClientScriptPath;
            return IsVirtualPathInApp(path, out isClientScriptPath);
        }

        public bool IsVirtualPathInApp(String path, out bool isClientScriptPath) {
            isClientScriptPath = false;

            if (path == null) {
                return false;
            }

            if (_virtualPath == "/" && path.StartsWith("/")) {
                if (path.StartsWith(_lowerCasedClientScriptPathWithTrailingSlash))
                    isClientScriptPath = true;
                return true;
            }

            path = path.ToLower();

            if (path.StartsWith(_lowerCasedVirtualPathWithTrailingSlash)) {
                return true;
            }

            if (path == _lowerCasedVirtualPath) {
                return true;
            }

            if (path.StartsWith(_lowerCasedClientScriptPathWithTrailingSlash)) {
                isClientScriptPath = true;
                return true;
            }

            return false;
        }

        public bool IsVirtualPathAppPath(String path) {
            if (path == null) {
                return false;
            }

            path = path.ToLower();
            return (path == _lowerCasedVirtualPath || path == _lowerCasedVirtualPathWithTrailingSlash);
        }
    }
}
