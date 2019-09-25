using System;
using System.Diagnostics;
using System.IO;
using System.Net;
using System.Net.Sockets;
using System.Text;
using System.Threading;
using Microsoft.Singularity.Smtp;

namespace Microsoft.Singularity.Smtp.Clients
{

    public class FileServer
    {
        private String[] sentDirectories;
        private Mutex    fileServerMutex;
        private int index;

        public FileServer(string path)
        {
            fileServerMutex = new Mutex();
            index = 0;
            Console.WriteLine("FileServer: Received file {0}\n", path);
            try {
                string fullPath = Path.GetFullPath(path);
                sentDirectories = File.ReadAllLines(fullPath);
            }
            catch (Exception e) {
                Console.WriteLine("FileServer: failed to get sent directories." +
                                  "  Exception: {0}\n", e.Message);
            }
        }

        public string GetNextDirectory()
        {
            string dirName = null;
            lock(fileServerMutex) {
                if (index < sentDirectories.Length) {
                    dirName = sentDirectories[index];
                    index++;
                }
            }
            return dirName;
        }

    }

    public class SmtpClient
    {

        public const int _port = 25;
        public static bool verbose = false;
        public static String server = "127.0.0.1";
        public static FileServer fileServer;
        public static int transPerThread = -1;

        //////////////////////////////////////////////////////////////////////////////
        //

        private static void Usage()
        {
            Console.WriteLine("Usage:");
            Console.WriteLine("    cli [operation] [options]");
            Console.WriteLine("Options:");
            Console.WriteLine("    /s:server       Send to server.");
            Console.WriteLine("    /c:conn         Number of simultaneous connections [default 1: max 50].");
            Console.WriteLine("    /t:trans        Number of transcations [default: no limit].");
            Console.WriteLine("    /f:file         File Containing directories of mail to send.");
            Console.WriteLine("    /?              Print this help information.");
        }

        public void Run()
        {
            String client = Dns.GetHostName();
            Console.WriteLine("Self: {0}", client);

            Socket socket = new Socket(AddressFamily.InterNetwork,
                                       SocketType.Stream,
                                       ProtocolType.Tcp);
            try {
                IPAddress addr = IPAddress.Parse(SmtpClient.server);
                socket.Connect(new IPEndPoint(addr, _port));
            } catch (SocketException e) {
                Console.WriteLine("Socket connect failure: {0}", e.Message);
                return;
            }

            Session session = new Session(socket);

            session.Verbose = verbose;

            try {
                // Establish SMPT connection.
                string line;
                line = session.ReadLine7();
                if (session.Result != 220) {
                    Console.WriteLine(":: Aborting due to {0}", session.Result);
                    session.Quit();
                    return;
                }

                session.WriteLine7("EHLO ", client);

                for (;;) {
                    line = session.ReadLine7();
                    if (session.Result != 250) {
                        Console.WriteLine(":: Aborting due to {0}", session.Result);
                        session.Quit();
                        return;
                    }

                    if (line[3] != '-') {
                        break;
                    }
                }
                Stopwatch sw = new Stopwatch();
                long fileCount = 0;
                string sentDir = SmtpClient.fileServer.GetNextDirectory();
                while((sentDir != null) && (fileCount < SmtpClient.transPerThread)) {
                    Console.WriteLine("Sending files in directory {0}\n", sentDir);
                    String[] files = Directory.GetFiles(sentDir);

                    // Send files.
                    foreach (string file in files) {
                        fileCount++;
                        Console.WriteLine(":: {0}", file);
                        String[] lines = File.ReadAllLines(file);
                        //start timing this transaction
                        sw.Start();
                        session.WriteLine7("NOOP ", file);
                        line = session.ReadLine7();
                        if (session.Result != 250) {
                            Console.WriteLine(":: Aborting due to {0}", session.Result);
                            session.Quit();
                            return;
                        }

                        string from = FindFrom(lines).ToLower();
                        session.WriteLine7("MAIL FROM: <", from, ">");
                        line = session.ReadLine7();
                        if (session.Result != 250) {
                            Console.WriteLine(":: Aborting due to {0}", session.Result);
                            session.Quit();
                            return;
                        }

                        string to = FindTo("To: ", lines);
                        string cc = FindTo("Cc: ", lines);
                        string bcc = FindTo("Bcc: ", lines);
                        if (to == null) {
                            to = cc;
                            cc = null;
                        }
                        if (to == null) {
                            to = bcc;
                            bcc = null;
                        }

                        if (cc != null) {
                            to = to + "," + cc;
                        }
                        if (bcc != null) {
                            to = to + "," + bcc;
                        }

                        if (to == null || to.Length == 0) {
                            Console.WriteLine(":: Couldn't find receipients.");
                            session.Quit();
                            return;
                        }

                        string[] rcpts = to.Split(new Char[]{','});
                        for (int i = 0; i < rcpts.Length; i++) {
                            rcpts[i] = rcpts[i].Trim().ToLower();
                            if (rcpts[i].Length == 0) {
                                rcpts[i] = null;
                            }
                        }

                        for (int i = 0; i < rcpts.Length; i++) {
                            for (int j = i + 1; j < rcpts.Length; j++) {
                                if (rcpts[i] == rcpts[j]) {
                                    rcpts[j] = null;
                                }
                            }
                        }

                        foreach (string rcpt in rcpts) {
                            if (rcpt != null) {
                                session.WriteLine7("RCPT TO: <", rcpt, ">");
                                line = session.ReadLine7();
                                if (session.Result != 250) {
                                    Console.WriteLine(":: Aborting due to {0}", session.Result);
                                    session.Quit();
                                    return;
                                }
                            }
                        }

                        session.WriteLine7("DATA");
                        line = session.ReadLine7();
                        if (session.Result != 354) {
                            Console.WriteLine(":: Aborting due to {0}", session.Result);
                            session.Quit();
                            return;
                        }

                        foreach (string data in lines) {
                            if (data.Length > 0 && data[0] == '.') {
                                session.WritePrefix((byte)'.');
                            }
                            session.WriteLine7(data);
                        }
                        session.WriteLine7(".");
                        line = session.ReadLine7();
                        if (session.Result != 250) {
                            Console.WriteLine(":: Aborting due to {0}", session.Result);
                            session.Quit();
                            return;
                        }
                        //stop timing this transaction
                        sw.Stop();
                        if (fileCount > SmtpClient.transPerThread) {
                            Console.WriteLine("Thread reached max transactions...done\n");
                            break;
                        }
                    }
                    sentDir = SmtpClient.fileServer.GetNextDirectory();
                }
                session.Quit();
                double seconds = sw.ElapsedTicks / Stopwatch.Frequency;
                double transPerSecond = fileCount / seconds;
                Console.WriteLine("Thread complete: total transactions {0} total time {1}" +
                                  " transactions per second {2}\n", fileCount, seconds,
                                  transPerSecond);
            }
            catch (SocketException e) {
                Console.WriteLine("Caught socket exception: {0}", e.Message);
            }
        }

        public static int Main(string[] args)
        {
            bool needHelp = false;
            int numConnections = 1;
            int totalTransactions = 10000;

            if (args.Length == 0) {
                needHelp = true;
            }
            fileServer = null;
            for (int a = 0; a < args.Length  && !needHelp; a++) {
                String arg = args[a];

                if (arg[0] == '/') {
                    int colon = arg.IndexOf(':');
                    String option;
                    String values;

                    if (colon > 1) {
                        option = arg.Substring(1, colon - 1).ToLower();
                        values = arg.Substring(colon + 1);
                    }
                    else {
                        option = arg.Substring(1).ToLower();
                        values = null;
                    }

                    switch (option[0]) {
                        // Commands:
                        case '?':   // Help
                            needHelp = true;
                            break;

                        case 's':   // Server
                        case 'S':
                            server = values;
                            break;

                        case 'c':
                        case 'C':
                            numConnections = Convert.ToInt32(values);
                            if (numConnections < 1 || numConnections > 50) {
                                needHelp = true;
                            }
                            break;

                        case 'v':   // Verbose
                            verbose = true;
                            break;

                        case 't':
                        case 'T':
                            totalTransactions = Convert.ToInt32(values);
                            if( (totalTransactions < 1) || (totalTransactions > 10000)) {
                                needHelp = true;
                                Console.WriteLine("transactions must be between 1 and 10,000\n");
                            }
                            break;

                        case 'f':  //file of directories
                            String file = Path.GetFileName(values);
                            if (file == String.Empty) {
                                Console.WriteLine("File name given is not a file\n");
                                needHelp = true;
                                break;
                            }
                            fileServer = new FileServer(values);
                            break;
                        default:
                            Console.WriteLine("Unknown option: {0}", arg);
                            needHelp = true;
                            break;
                    }
                }
                else {
                    needHelp = true;
                }

            }

            if (fileServer == null) {
                needHelp = true;
            }

            if (needHelp) {
                Usage();
                return 1;
            }

            bool highRes = Stopwatch.IsHighResolution;
            Console.WriteLine("About to spawn {0} threads StopWatch.IsHighResolution {1}\n",
                              numConnections, highRes);


            Thread[] workers;
            workers = new Thread[numConnections];
            int i;
            transPerThread = totalTransactions / numConnections;
            Console.WriteLine("Executing total transactions {0} per thread {1}\n",
                              totalTransactions, transPerThread);
            for (i = 0; i < numConnections; i++) {
                SmtpClient client = new SmtpClient();
                workers[i] = new Thread(
                    new ThreadStart(client.Run));
                workers[i].Start();
            }

            for (i = 0; i< numConnections; i++) {
                workers[i].Join();
            }

            return 0;
        }

        //////////////////////////////////////////////////////////////////////////////

        public static String FindFrom(String[] lines)
        {
            foreach (string line in lines) {
                if (line.Length == 0) {
                    return null; // Header ended.
                }
                if (line.StartsWith("From: ")) {
                    return line.Substring(6);
                }
            }
            return null;
        }

        public static string FindTo(String prefix, String[] lines)
        {
            for (int i = 0; i < lines.Length; i++) {
                if (lines[i].Length == 0) {
                    return null; // Header ended.
                }
                if (lines[i].StartsWith(prefix)) {
                    string to = lines[i++].Substring(prefix.Length);
                    while (lines[i].Length > 0 && (lines[i][0] == ' ' || lines[i][0] == '\t')) {
                        to = to + lines[i++];
                    }
                    return to;
                }
            }
            return null;
        }

    }
}


