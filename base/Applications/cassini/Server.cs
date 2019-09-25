//------------------------------------------------------------------------------
//   Copyright (c) Microsoft Corporation. All Rights Reserved.
//------------------------------------------------------------------------------

namespace Microsoft.VisualStudio.WebHost
{
    using System;
    using System.Collections;
    using System.Globalization;
    using System.IO;
    using System.Net;
    using System.Net.Sockets;
    using System.Threading;
    using System.Runtime.InteropServices;
    using System.Web.Hosting;

    public class Server : SimpleApplicationHost {

        // =======================
        // The original version of Cassini uses the .NET thread pool to run
        // certain methods. There is currently no thread pool available on Singularity,
        // so I adapted Cassini to spin up threads on demand instead. These helper
        // objects assist with this; we could go back and remove them when
        // thread pools become available, if we wanted.
        // =======================   

        internal abstract class ThreadObject
        {
            protected abstract void Run();

            public void Start()
            {
                ThreadStart threadStart = new ThreadStart(Run);
                Thread selfThread = new Thread(threadStart);
                selfThread.Start();
            }

#if THREAD_POOL
            public ThreadStart NewThreadStart()
            {
                return new ThreadStart(Run);
            }
#endif
        }

        internal class AcceptThread : ThreadObject {
            private Server _server;
            private Socket _socket;

            public AcceptThread(Server server, Socket socket)
            {
                _server = server;
                _socket = socket;
            }

            protected override void Run()
            {
                _server.OnSocketAccept(_socket);
            }
        }

        internal class StartThread : ThreadObject {
            private Server _server;

            public StartThread(Server server)
            {
                _server = server;
            }

            protected override void Run()
            {
                _server.OnStart();
            }
        }

        // =======================
        // end helper objects
        // =======================   


        private int _port;
        private string _virtualPath;
        private string _physicalPath;
        private string _clientIP;

        //private WaitCallback _onStart;
        //private WaitCallback _onSocketAccept;

        private bool _shutdownInProgress;

        private Socket _socket;
        private Host _host;

        private IntPtr _processToken;
        private String _processUser;

#if THREAD_POOL
        private CassiniThreadPool threadPool;
        private const int workerThreads = 16;
        private const int maxWorkItems = workerThreads * 128;
#endif

        public Server(int port, string virtualPath, string physicalPath, string clientIP)
            : base(virtualPath, physicalPath)
        {
            _port = port;
            _virtualPath = virtualPath;
            _clientIP = clientIP;

            string directorySeparatorString = new string(Path.DirectorySeparatorChar, 1);
            _physicalPath = physicalPath.EndsWith(directorySeparatorString) ? physicalPath : physicalPath + directorySeparatorString;
            //_onSocketAccept = new WaitCallback(OnSocketAccept);
            //_onStart = new WaitCallback(OnStart);
#if THREAD_POOL
            threadPool = new CassiniThreadPool(workerThreads, maxWorkItems);
#endif
        }

        //
        //// MarshalByRefObject override
        //public override object InitializeLifetimeService() {
        //  // never expire the license
        //  return null;
        //}
        //

        public int Port {
            get {
                return _port;
            }
        }

        public string RootUrl {
            get {
                if (_port != 80) {
                    return "http://localhost:" + _port + _virtualPath;
                }
                else {
                    return "http://localhost" + _virtualPath;
                }
            }
        }

        //
        // Process identity
        //

        private const int TOKEN_ALL_ACCESS   = 0x000f01ff;
        private const int TOKEN_EXECUTE      = 0x00020000;
        private const int TOKEN_READ         = 0x00020008;
        private const int TOKEN_IMPERSONATE  = 0x00000004;

        public IntPtr GetProcessToken() {
            return _processToken;
        }

        public String GetProcessUser() {
            return _processUser;
        }

        //
        // Socket listening
        //

        public void Start() {
            _socket = new Socket(AddressFamily.InterNetwork, SocketType.Stream, ProtocolType.Tcp);
            _socket.Bind(new IPEndPoint(IPAddress.Any, _port));
            _socket.Listen((int)SocketOptionName.MaxConnections);

            //ThreadPool.QueueUserWorkItem(_onStart);
            (new StartThread(this)).Start();
        }

        public void Stop() {
            _shutdownInProgress = true;

            try {
                if (_socket != null) {
                    _socket.Shutdown(SocketShutdown.Both);
                    _socket.Close();
                }
            }
            catch {
            }
            finally {
                _socket = null;
            }

            try {
                if (_host != null) {
                    _host.Shutdown();
                }

                while (_host != null) {
                    Thread.Sleep(100);
                }
            }
            catch {
            }
            finally {
                _host = null;
            }
        }

        protected void OnSocketAccept(object acceptedSocket) {
            if (!_shutdownInProgress) {
                Connection conn =  new Connection(this, (Socket)acceptedSocket, _clientIP);
                //Console.WriteLine("- Accept at {0} from {1}", conn.LocalIP, conn.RemoteIP);

                // wait for at least some input
                if (conn.WaitForRequestBytes() == 0) {
                    conn.WriteErrorAndClose(400);
                    return;
                }

                // find or create host
                Host host = GetHost();
                if (host == null) {
                    conn.WriteErrorAndClose(500);
                    return;
                }

#if FEATURE_PAL && DEBUG // ROTORTODO
                Console.WriteLine("Process request at " + conn.LocalIP + " from " + conn.RemoteIP);
#endif

                // process request in worker app domain
                host.ProcessRequest(conn);
            }
        }

        protected void OnStart()
        {
            while (!_shutdownInProgress) {
                try {
                    if (_socket != null) // ROTORTODO
                    {
                        Socket socket = _socket.Accept();
                        //ThreadPool.QueueUserWorkItem(_onSocketAccept, socket);
#if THREAD_POOL
                        //ThreadPool.QueueUserWorkItem(_onSocketAccept, socket);
                        threadPool.QueueUserWorkItem(
                            new AcceptThread(this, socket).NewThreadStart());
#else
                        (new AcceptThread(this, socket)).Start();
#endif
                    }
                }
                catch {
                    Thread.Sleep(100);
                }
            }
        }

        private Host GetHost()
        {
            if (_shutdownInProgress) {
                return null;
            }

            Host host = _host;

            if (host == null) {
                lock (this) {
                    if (_host == null) {
                        _host = new Host();
                        _host.Configure(this, _port, _virtualPath, _physicalPath, ClientScriptVirtualPath, ClientScriptPath);
                    }

                    host = _host;
                }
            }

            return host;
        }

        internal void HostStopped() {
            _host = null;
        }
    }
}
