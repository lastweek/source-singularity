//------------------------------------------------------------------------------
//   Copyright (c) Microsoft Corporation. All Rights Reserved.
//------------------------------------------------------------------------------

namespace Microsoft.VisualStudio.WebHost
{
    using System;
    using System.Collections;
    using System.Diagnostics;
    using System.Net;
    using System.Net.Sockets;
    using System.Security;
    using System.Text;
    using System.Threading;
    using System.Globalization;
    using System.Web;
    using System.Web.Hosting;

    // Singularity
    using Microsoft.SingSharp;
    using Microsoft.Contracts;
    using Microsoft.SingSharp.Runtime;
    using Microsoft.Singularity.Channels;
    using Microsoft.Singularity;
    //

    // Event types local to this provider   
    public enum CassiniEvent : ushort
    {
        ProcessRequest = 1
    }

    internal sealed class Request : SimpleWorkerRequest {
        private const int MaxChunkLength = 64 * 1024;

        private Host! _host;
        private Connection! _connection;

        // raw request data
        private const int maxHeaderBytes = 32*1024;
        private byte[] _headerBytes;
        private int _startHeadersOffset;
        private int _endHeadersOffset;
        private ArrayList _headerByteStrings;

        // parsed request data
        private string _verb;
        private string _url;
        private string _prot;

        private string _path;
        private string _filePath;
        private new string _pathInfo;
        private string _pathTranslated;
        private new string _queryString;
        private byte[] _queryStringBytes;

        private int _contentLength;
        private int _preloadedContentLength;
        private byte[] _preloadedContent;

        private string _allRawHeaders;
        private string[][] _unknownRequestHeaders;
        private string[] _knownRequestHeaders;
        private bool _specialCaseStaticFileHeaders;

        // cached response
        private bool _headersSent;
        private int _responseStatus;
        private StringBuilder _responseHeadersBuilder;
        private ArrayList _responseBodyBytes;

        public Request(Host! host, Connection! connection)
        {
            _host = host;
            _connection = connection;
            base(String.Empty, String.Empty, String.Empty, String.Empty, null);
        }

        public void Process() {
            ReadAllHeaders();

            // Limit to local requests only
            if (!_connection.IsLocal) {
                _connection.WriteErrorAndClose(403);
                return;
            }

            if (_headerBytes == null || _endHeadersOffset < 0 ||
                _headerByteStrings == null || _headerByteStrings.Count == 0) {
                _connection.WriteErrorAndClose(400);
                return;
            }

            if (!ParseRequestLine()) {
                return; // ParseRequestLine() has closed the connection
            }

            Monitoring.Log(Monitoring.Provider.Cassini,
                           (ushort)CassiniEvent.ProcessRequest,
                           this.GetUriPath());

            // Check if the path is not well formed or is not for the current app
            bool isClientScriptPath = false;
            if (!_host.IsVirtualPathInApp(_path, out isClientScriptPath)) {
                _connection.WriteErrorAndClose(404);
                return;
            }

            ParseHeaders();

            ParsePostedContent();

            string expectHeader = GetKnownRequestHeader(HeaderExpect);

            if (_verb == "POST" &&
                _contentLength > 0 &&
                _preloadedContentLength < _contentLength &&
                expectHeader != null &&
                expectHeader.ToLower().IndexOf("100-continue") >= 0) {

                // Client is expecting 100-continue
                _connection.Write100Continue();
            }

            PrepareResponse();

            // Hand over the request to be processed
            Dispatcher.DispatchRequest(this);
        }

        private bool TryReadAllHeaders() {
            // read the first packet (up to 32K)
            byte[] headerBytes = _connection.ReadRequestBytes(maxHeaderBytes);

            if (headerBytes == null || headerBytes.Length == 0)
                return false;

            if (_headerBytes != null) {
                // previous partial read
                int len = headerBytes.Length + _headerBytes.Length;
                if (len > maxHeaderBytes)
                    return false;

                byte[] bytes = new byte[len];
                Buffer.BlockCopy(_headerBytes, 0, bytes, 0, _headerBytes.Length);
                Buffer.BlockCopy(headerBytes, 0, bytes, _headerBytes.Length, headerBytes.Length);
                _headerBytes = bytes;
            }
            else {
                _headerBytes = headerBytes;
            }

            // start parsing
            _startHeadersOffset = -1;
            _endHeadersOffset = -1;
            _headerByteStrings = new ArrayList();

            // find the end of headers
            ByteParser parser = new ByteParser(_headerBytes);

            for (;;) {
                ByteString line = parser.ReadLine();

                if (line == null) {
                    break;
                }

                if (_startHeadersOffset < 0) {
                    _startHeadersOffset = parser.CurrentOffset;
                }

                if (line.IsEmpty) {
                    _endHeadersOffset = parser.CurrentOffset;
                    break;
                }

                _headerByteStrings.Add(line);
            }

            return true;
        }

        private void ReadAllHeaders() {
            _headerBytes = null;

            do {
                if (!TryReadAllHeaders()) {
                    // something bad happened
                    break;
                }
            }
            while (_endHeadersOffset < 0); // found \r\n\r\n
        }

        private bool ParseRequestLine() {
            ByteString requestLine = (ByteString)_headerByteStrings[0];
            ByteString[] elems = requestLine.Split(' ');

            if (elems == null || elems.Length < 2 || elems.Length > 3) {
                _connection.WriteErrorAndClose(400);
                return false;
            }

            _verb = elems[0].GetString();

            ByteString urlBytes = elems[1];
            _url = urlBytes.GetString();

            if (elems.Length == 3) {
                _prot = elems[2].GetString();
            }
            else {
                _prot = "HTTP/1.0";
            }

            // query string

            int iqs = urlBytes.IndexOf('?');
            if (iqs > 0) {
                _queryStringBytes = urlBytes.Substring(iqs+1).GetBytes();
            }
            else {
                _queryStringBytes = new byte[0];
            }

            iqs = _url.IndexOf('?');
            if (iqs > 0) {
                _path = _url.Substring(0, iqs);
                _queryString = _url.Substring(iqs+1);
            }
            else {
                _path = _url;
                _queryStringBytes = new byte[0];
            }

            // url-decode path

            if (_path.IndexOf('%') >= 0) {
                _path = HttpUtility.UrlDecode(_path, Encoding.UTF8);
            }

            // path info

            int lastDot = _path.LastIndexOf('.');
            int lastSlh = _path.LastIndexOf('/');

            if (lastDot >= 0 && lastSlh >= 0 && lastDot < lastSlh && lastSlh < _path.Length - 1) {
                int ipi = _path.IndexOf('/', lastDot);
                _filePath = _path.Substring(0, ipi);
                _pathInfo = _path.Substring(ipi);
            }
            else {
                _filePath = _path;
                _pathInfo = String.Empty;
            }

            _pathTranslated = MapPath(_filePath);

            return true;
        }

        private void ParseHeaders() {
            _knownRequestHeaders = new string[RequestHeaderMaximum];

            // construct unknown headers as array list of name1,value1,...
            ArrayList headers = new ArrayList();

            for (int i = 1; i < _headerByteStrings.Count; i++) {
                string s = ((ByteString)_headerByteStrings[i]).GetString();

                int c = s.IndexOf(':');

                if (c >= 0) {
                    string name = s.Substring(0, c).Trim();
                    string value = s.Substring(c + 1).Trim();

                    // remember
                    int knownIndex = GetKnownRequestHeaderIndex(name);
                    if (knownIndex >= 0) {
                        _knownRequestHeaders[knownIndex] = value;
                    }
                    else {
                        headers.Add(name);
                        headers.Add(value);
                    }
                }
            }

            // copy to array unknown headers

            int n = headers.Count / 2;
            _unknownRequestHeaders = new string[n][];
            int j = 0;

            for (int i = 0; i < n; i++) {
                _unknownRequestHeaders[i] = new string[2];
                _unknownRequestHeaders[i][0] = (string)headers[j++];
                _unknownRequestHeaders[i][1] = (string)headers[j++];
            }

            // remember all raw headers as one string

            if (_headerByteStrings.Count > 1) {
                _allRawHeaders = Encoding.UTF8.GetString(_headerBytes, _startHeadersOffset, _endHeadersOffset-_startHeadersOffset);
            }
            else {
                _allRawHeaders = String.Empty;
            }
        }

        private void ParsePostedContent() {
            _contentLength = 0;
            _preloadedContentLength = 0;

            string contentLengthValue = _knownRequestHeaders[HttpWorkerRequest.HeaderContentLength];
            if (contentLengthValue != null) {
                try {
                    _contentLength = Int32.Parse(contentLengthValue);
                }
                catch {
                }
            }

            if (_headerBytes.Length > _endHeadersOffset) {
                _preloadedContentLength = _headerBytes.Length - _endHeadersOffset;

                if (_preloadedContentLength > _contentLength && _contentLength > 0)
                    _preloadedContentLength = _contentLength; // don't read more than the content-length

                _preloadedContent = new byte[_preloadedContentLength];
                Buffer.BlockCopy(_headerBytes, _endHeadersOffset, _preloadedContent, 0, _preloadedContentLength);
            }
        }

        private void PrepareResponse() {
            _headersSent = false;
            _responseStatus = 200;
            _responseHeadersBuilder = new StringBuilder();
            _responseBodyBytes = new ArrayList();
        }

        ///////////////////////////////////////////////////////////////////////////////////////////////
        // Implementation of HttpWorkerRequest

        public override string GetUriPath() {
            return _path;
        }

        public override string GetQueryString() {
            return _queryString;
        }

        public override byte[] GetQueryStringRawBytes() {
            return _queryStringBytes;
        }

        public override string GetRawUrl() {
            return _url;
        }

        public override string GetHttpVerbName() {
            return _verb;
        }

        public override string GetHttpVersion() {
            return _prot;
        }

        public override string GetRemoteAddress() {
            return _connection.RemoteIP;
        }

        public override int GetRemotePort() {
            return 0;
        }

        public override string GetLocalAddress() {
            return _connection.LocalIP;
        }

        public override string GetServerName() {
            string localAddress = GetLocalAddress();
            if (localAddress.Equals("127.0.0.1")) {
                return "localhost";
            }
            return localAddress;
        }

        public override int GetLocalPort() {
            return _host.Port;
        }

        public override string GetFilePath() {
            return _filePath;
        }

        public override string GetFilePathTranslated() {
            return _pathTranslated;
        }

        public override string GetPathInfo() {
            return _pathInfo;
        }

        public override string GetAppPath() {
            return _host.VirtualPath;
        }

        public override string GetAppPathTranslated() {
            return _host.PhysicalPath;
        }

        public override byte[] GetPreloadedEntityBody() {
            return _preloadedContent;
        }

        [Pure]
        public override bool IsEntireEntityBodyIsPreloaded() {
            return (_contentLength == _preloadedContentLength);
        }

        public override int ReadEntityBody(byte[] buffer, int size)  {
            int bytesRead = 0;
            byte[] bytes = _connection.ReadRequestBytes(size);

            if (bytes != null && bytes.Length > 0) {
                bytesRead = bytes.Length;
                Buffer.BlockCopy(bytes, 0, buffer, 0, bytesRead);
            }

            return bytesRead;
        }

        public override string GetKnownRequestHeader(int index)  {
            return _knownRequestHeaders[index];
        }

        public override string GetUnknownRequestHeader(string name) {
            int n = _unknownRequestHeaders.Length;

            for (int i = 0; i < n; i++) {
                if (string.Compare(name, _unknownRequestHeaders[i][0], true) == 0) {
                    return _unknownRequestHeaders[i][1];
                }
            }

            return null;
        }

        public override string[][] GetUnknownRequestHeaders() {
            return _unknownRequestHeaders;
        }

        public override string GetServerVariable(string name) {
            string s = String.Empty;

            switch (name) {
                case "ALL_RAW":
                    s = _allRawHeaders;
                    break;

                case "SERVER_PROTOCOL":
                    s = _prot;
                    break;

                case "AUTH_TYPE":
                    if (GetUserToken() != IntPtr.Zero)
                        s = "NTLM";
                    break;
            }

            return s;
        }

        public override string MapPath(string path) {
            string mappedPath = String.Empty;
            bool isClientScriptPath = false;

            if (path == null || path.Length == 0 || path.Equals("/")) {
            // asking for the site root
                if (_host.VirtualPath == "/") {
                    // app at the site root
                    mappedPath = _host.PhysicalPath;
                }
                else {
                    // unknown site root - don't point to app root to avoid double config inclusion
                    mappedPath = "c:\\"; //Environment.SystemDirectory;
                }
            }
            else if (_host.IsVirtualPathAppPath(path)) {
                // application path
                mappedPath = _host.PhysicalPath;
            }
            else if (_host.IsVirtualPathInApp(path, out isClientScriptPath)) {
                if (isClientScriptPath) {
                    mappedPath = _host.PhysicalClientScriptPath + path.Substring(_host.NormalizedClientScriptPath.Length);
                }
                else {
                    // inside app but not the app path itself
                    mappedPath = _host.PhysicalPath + path.Substring(_host.NormalizedVirtualPath.Length);
                }
            }
            else {
                // outside of app -- make relative to app path
                if (path.StartsWith("/")) {
                    mappedPath = _host.PhysicalPath + path.Substring(1);
                }
                else {
                    mappedPath = _host.PhysicalPath + path;
                }
            }

            mappedPath = mappedPath.Replace('/', '\\');

            if (mappedPath.EndsWith("\\") && !mappedPath.EndsWith(":\\")) {
                mappedPath = mappedPath.Substring(0, mappedPath.Length-1);
            }

            return mappedPath;
        }

        public override void SendStatus(int statusCode, string statusDescription) {
            _responseStatus = statusCode;
        }

        public override void SendKnownResponseHeader(int index, string value) {
            if (_headersSent) {
                return;
            }

            switch (index) {
                case HttpWorkerRequest.HeaderServer:
                case HttpWorkerRequest.HeaderDate:
                case HttpWorkerRequest.HeaderConnection:
                    // ignore these
                    return;
                case HttpWorkerRequest.HeaderAcceptRanges:
                    if (value == "bytes") {
                        // use this header to detect when we're processing a static file
                        _specialCaseStaticFileHeaders = true;
                        return;
                    }
                    break;
                case HttpWorkerRequest.HeaderExpires:
                case HttpWorkerRequest.HeaderLastModified:
                    if (_specialCaseStaticFileHeaders) {
                        // NOTE: Ignore these for static files. These are generated
                        //       by the StaticFileHandler, but they shouldn't be.
                        return;
                    }
                    break;
            }

            _responseHeadersBuilder.Append(GetKnownResponseHeaderName(index));
            _responseHeadersBuilder.Append(": ");
            _responseHeadersBuilder.Append(value);
            _responseHeadersBuilder.Append("\r\n");
        }

        public override void SendUnknownResponseHeader(string name, string value) {
            if (_headersSent)
                return;

            _responseHeadersBuilder.Append(name);
            _responseHeadersBuilder.Append(": ");
            _responseHeadersBuilder.Append(value);
            _responseHeadersBuilder.Append("\r\n");
        }

        public override void SendCalculatedContentLength(int contentLength) {
            if (!_headersSent) {
                _responseHeadersBuilder.Append("Content-Length: ");
                _responseHeadersBuilder.Append(contentLength);
                _responseHeadersBuilder.Append("\r\n");
            }
        }

        public override bool HeadersSent() {
            return _headersSent;
        }

        public override bool IsClientConnected() {
            return _connection.Connected;
        }

        public override void CloseConnection() {
            _connection.Close();
        }

        public override void SendResponseFromMemory(byte[] data, int length) {
            if (length > 0) {
                byte[] bytes = new byte[length];
                Buffer.BlockCopy(data, 0, bytes, 0, length);
                _responseBodyBytes.Add(bytes);
            }
        }

        public void SendResponseFromMemory([Claims] byte[]! in ExHeap data) {
            VContainer<byte> container = new VContainer<byte>(data);
            _responseBodyBytes.Add(container);
        }

        public override void FlushResponse(bool finalFlush) {
            try {

                if (!_headersSent) {
                    _connection.WriteHeaders(_responseStatus, _responseHeadersBuilder.ToString());
                    _headersSent = true;
                }

                for (int i = 0; i < _responseBodyBytes.Count; i++) {
                    byte[] bytes = _responseBodyBytes[i] as byte[];
                    VContainer<byte> container = _responseBodyBytes[i] as VContainer<byte>;

                    if (bytes != null) {
                        _connection.WriteBody(bytes, 0, bytes.Length);
                    }
                    else if (container != null) {
                        byte[]! in ExHeap exBytes = container.Acquire();
                        _responseBodyBytes[i] = null;
                        _connection.WriteBody(exBytes);
                    }
                    else {
                        Debug.Assert(false);
                    }
                }
            }
            catch (SocketException) {
                // If the socket throws an exception, abort trying to write the
                // rest of the body.
            }
            finally {
                // Clean up in case an exception caused us to abort partway through
                _headersSent = true;

                for (int i = 0; i < _responseBodyBytes.Count; i++) {
                    VContainer<byte> container = _responseBodyBytes[i] as VContainer<byte>;

                    if (container != null) {
                        byte[]! in ExHeap exBytes = container.Acquire();
                        delete exBytes;
                        _responseBodyBytes[i] = null;
                    }
                }
            }

            _responseBodyBytes = new ArrayList();

            if (finalFlush) {
                _connection.Close();
            }
        }

        public override void EndOfRequest() {
            FlushResponse(true);
        }
    }
}
