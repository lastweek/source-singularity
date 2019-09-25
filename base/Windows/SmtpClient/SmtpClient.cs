using System;
using System.IO;
using System.Net;
using System.Net.Sockets;
using System.Text;
using Microsoft.Singularity.Smtp;

namespace Microsoft.Singularity.Smtp.Clients
{
    public class SmtpClient
    {
        public const int _port = 25;
        public static bool verbose = false;

        //////////////////////////////////////////////////////////////////////////////
        //

        private static void Usage()
        {
            Console.WriteLine("Usage:");
            Console.WriteLine("    cli [operation] [options]");
            Console.WriteLine("Options:");
            Console.WriteLine("    /s:server       Send to server.");
            Console.WriteLine("    /?              Print this help information.");
        }

        public static int Main(string[] args)
        {
            bool needHelp = false;
            String client = Dns.GetHostName();
            String server = "127.0.0.1";
            String[] files = null;

            if (args.Length == 0) {
                needHelp = true;
            }

            Console.WriteLine("Self: {0}", client);

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

                        case 'v':   // Verbose
                            verbose = true;
                            break;

                        default:
                            Console.WriteLine("Unknown option: {0}", arg);
                            needHelp = true;
                            break;
                    }
                }
                else {
                    String file = Path.GetFileName(arg);
                    String dir = Path.GetDirectoryName(arg);
                    String path = (dir == String.Empty) ?
                        Directory.GetCurrentDirectory() :
                        Path.GetFullPath(dir);
                    files = Directory.GetFiles(path, file);
                }
            }

            if (files == null) {
                needHelp = true;
            }

            if (needHelp) {
                Usage();
                return 1;
            }

            // Send the file.

            String line;
            Socket socket = new Socket(AddressFamily.InterNetwork,
                                       SocketType.Stream,
                                       ProtocolType.Tcp);
            try {
                IPAddress addr = IPAddress.Parse(server);
                socket.Connect(new IPEndPoint(addr, _port));
            } catch (SocketException e) {
                Console.WriteLine("Socket connect failure: {0}", e.Message);
                return 2;
            }

            Session session = new Session(socket);

            session.Verbose = verbose;

            try {
                // Establish SMPT connection.
                line = session.ReadLine7();
                if (session.Result != 220) {
                    Console.WriteLine(":: Aborting due to {0}", session.Result);
                    return session.Quit();
                }

                session.WriteLine7("EHLO ", client);

                for (;;) {
                    line = session.ReadLine7();
                    if (session.Result != 250) {
                        Console.WriteLine(":: Aborting due to {0}", session.Result);
                        return session.Quit();
                    }

                    if (line[3] != '-') {
                        break;
                    }
                }

                // Send files.

                foreach (string file in files) {
                    Console.WriteLine(":: {0}", file);
                    String[] lines = File.ReadAllLines(file);

#if false
                    // Sanitize the data.
                    for (int i = 0; i < lines.Length; i++) {
                        String data = lines[i];

                        if (data.Length >= 2 &&
                            data[data.Length - 2] == '\r' &&
                            data[data.Length - 1] == '\n') {

                            lines[i] = data.Substring(0, data.Length - 2);
                        }
                        else if (data.Length >= 1 &&
                                 data[data.Length - 1] == '\n') {

                            lines[i] = data.Substring(0, data.Length - 1);
                        }
                        else if (data.Length >= 1 &&
                                 data[data.Length - 1] == '\r') {

                            lines[i] = data.Substring(0, data.Length - 1);
                        }
                    }
#endif

                    session.WriteLine7("NOOP ", file);
                    line = session.ReadLine7();
                    if (session.Result != 250) {
                        Console.WriteLine(":: Aborting due to {0}", session.Result);
                        return session.Quit();
                    }

                    string from = FindFrom(lines).ToLower();
                    session.WriteLine7("MAIL FROM: <", from, ">");
                    line = session.ReadLine7();
                    if (session.Result != 250) {
                        Console.WriteLine(":: Aborting due to {0}", session.Result);
                        return session.Quit();
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
                        return session.Quit();
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
                                return session.Quit();
                            }
                        }
                    }

                    session.WriteLine7("DATA");
                    line = session.ReadLine7();
                    if (session.Result != 354) {
                        Console.WriteLine(":: Aborting due to {0}", session.Result);
                        return session.Quit();
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
                        return session.Quit();
                    }
                }
                session.Quit();
            }
            catch (SocketException e) {
                Console.WriteLine("Caught socket exception: {0}", e.Message);
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


