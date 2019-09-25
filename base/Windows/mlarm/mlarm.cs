///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   mlarm.cs
//
//  Note:   Parse ML style arguments and invoked ARMASM.
//

using System;
using System.Collections;
using System.Diagnostics;
using System.Runtime.InteropServices;
using System.IO;
using System.Text;

namespace Microsoft.Singularity.Applications
{
    public class ArmAsmWrapper
    {
        // Print the correct command line args for the program
        static void Usage()
        {
            Console.WriteLine(
                "Usage:\n"+
                "    MLARM [ /options ] filelist [ /link linkoptions ]\n"+
                "\n"+
                "Options:\n"+
                "    /c               Assemble without linking\n"+
                "    /Cp              Preserve case of user identifiers [ignored]\n"+
                "    /Cx              Preserve case in publics, externs [ignored]\n"+
                "    /D<name>[=text]  Define text macro\n"+
                "    /Fl[file]        Generate listing\n"+
                "    /Fo<file>        Name object file\n"+
                "    /I<name>         Add include path\n"+
                "    /nologo          Suppress copyright message [ignored]\n"+
                "    /QRarch4         ARM4 Architecture\n"+
                "    /QRarch4T        ARM4T Architecture\n"+
                "    /QRarch5         ARM5 Architecture\n"+
                "    /QRarch5T        ARM5T Architecture\n"+
                "    /QRarch6         ARM6 Architecture\n"+
                "    /QRxscale        XSCALE Architecture\n"+
                "    /Sa              Maximize source listing\n"+
                "    /Sl<width>       Set line width\n"+
                "    /Sp<length>      Set page length\n"+
                "    /Sx              List false conditionals\n"+
                "    /W<number>       Set warning level\n"+
                "    /Zi              Add symbolic debug info [ignored]\n"+
                "\n"+
                "Summary:\n"+
                "    Converts command arguments formats and calls armasm.");
        }

        static bool IsQuote(char c)
        {
            return (c == '"' || c == '\'');
        }

        static string RemoveQuotes(string text)
        {
            int start = 0;
            int length = text.Length;

            if (length > 0 && IsQuote(text[start + length - 1])) {
                length--;
            }
            if (length > 0 && IsQuote(text[start])) {
                start++;
                length--;
            }

            if (start != 0 || length != text.Length) {
                return text.Substring(start, length);
            }
            else {
                return text;
            }
        }

        static bool StringIsNullOrEmpty(string str)
        {
            return (str == null || str.Length == 0);
        }

        static bool ArgIsPrefix(string arg, string prefix)
        {
            return (arg == prefix);
        }

        static bool ArgIsPrefix(string arg, string prefix, string alt)
        {
            return (arg == prefix || arg == alt);
        }

        static string ArgHasPrefix(string arg, string prefix)
        {
            if (arg.StartsWith(prefix)) {
                return arg.Substring(prefix.Length);
            }
            return null;
        }

        static string ArgHasPrefix(string arg, string prefix, string alt)
        {
            string ret = ArgHasPrefix(arg, prefix);
            return (ret != null) ? ret : ArgHasPrefix(arg, alt);
        }

        static int Main(string[] args)
        {
            ArrayList outargs = new ArrayList();

            // Temporaries for command-line parsing
            bool needHelp = (args.Length == 0);
            bool linkOnly = false;
            bool nologo = false;

            for (int i = 0; i < args.Length && !needHelp; i++) {
                string arg = (string) args[i];
                string val = null;

                if (ArgIsPrefix(arg, "/c", "-c")) {
                    // Assemble without linking
                    linkOnly = true;
                }
                else if (ArgIsPrefix(arg, "/Cp", "-Cp")) {
                    // Preserve case of user identifiers.
                }
                else if (ArgIsPrefix(arg, "/Cx", "-Cx")) {
                    // Preserve case in publics, externs.
                }
                else if (ArgIsPrefix(arg, "/Cx", "-Cx")) {
                }
                else if ((val = ArgHasPrefix(arg, "/D", "-D")) != null) {
                    // <name>[=text] Define text macro
                    int index = val.IndexOf('=');
                    if (index > 0) {
                        outargs.Add(String.Format("-PreDefine \"{0} SETA {1}\"",
                                                  val.Substring(0, index),
                                                  val.Substring(index + 1)));
                    }
                    else {
                        outargs.Add(String.Format("-PreDefine \"{0} SETA {1}\"",
                                                  val, 1));
                    }
                }
                else if ((val = ArgHasPrefix(arg, "/Fl", "-Fl")) != null) {
                    // [file] Generate listing
                    outargs.Add("-list " + val);
                }
                else if ((val = ArgHasPrefix(arg, "/Fo", "-Fo")) != null) {
                    // <file> Name object file
                    outargs.Add("-o " + val);
                }
                else if ((val = ArgHasPrefix(arg, "/I", "-I")) != null) {
                    // <name> Add include path
                    outargs.Add("-I " + val);
                }
                else if (ArgIsPrefix(arg, "/nologo", "-nologo")) {
                    // Suppress copyright message
                    if (!nologo) {
                        outargs.Add("-nologo");
                        nologo = true;
                    }
                }
                else if (ArgIsPrefix(arg, "/QRarch4", "-QRarch4")) {
                    // ARM4 Architecture
                    outargs.Add("-ARCH 4");
                }
                else if (ArgIsPrefix(arg, "/QRarch4T", "-QRarch4T")) {
                    // ARM4T Architecture
                    outargs.Add("-ARCH 4T");
                }
                else if (ArgIsPrefix(arg, "/QRarch5", "-QRarch5")) {
                    // ARM5 Architecture
                    outargs.Add("-ARCH 5");
                }
                else if (ArgIsPrefix(arg, "/QRarch5T", "-QRarch5T")) {
                    // ARM5T Architecture
                    outargs.Add("-ARCH 5T");
                }
                else if (ArgIsPrefix(arg, "/QRarch6", "-QRarch6")) {
                    // ARM6 Architecture
                    outargs.Add("-ARCH 6");
                }
                else if (ArgIsPrefix(arg, "/QRxscale", "-QRxscale")) {
                    // XScale
                    outargs.Add("-CPU XSCALE");
                }
                else if (ArgIsPrefix(arg, "/Sa", "-Sa")) {
                    // Maximize source listing
                }
                else if ((val = ArgHasPrefix(arg, "/Sl", "-Sl")) != null) {
                    // <width> Set line width
                    outargs.Add("-Width " + val);
                }
                else if ((val = ArgHasPrefix(arg, "/Sp", "-Sp")) != null) {
                    // <length> Set page length
                    outargs.Add("-Length " + val);
                }
                else if (ArgIsPrefix(arg, "/Sx", "-Sx")) {
                    // <length> Set page length
                    outargs.Add("-NOTerse");
                }
                else if (ArgIsPrefix(arg, "/W0", "-W0")) {
                    // <number> Set warning level
                    outargs.Add("-NOWarn");
                }
                else if (ArgIsPrefix(arg, "/W1", "-W1")) {
                    // <number> Set warning level
                }
                else if (ArgIsPrefix(arg, "/W2", "-W2")) {
                    // <number> Set warning level
                }
                else if (ArgIsPrefix(arg, "/W3", "-W3")) {
                    // <number> Set warning level
                }
                else if (ArgIsPrefix(arg, "/Zi", "-Zi")) {
                    // Add symbolic debug info
                }
                else if (ArgIsPrefix(arg, "/?", "-?")) {
                    needHelp = true;

                }
                else if (ArgHasPrefix(arg, "/", "-") != null) {
                    Console.Error.WriteLine("mlarm: Invalid argument: {0}", arg);
                    break;
                }
                else {
                    outargs.Add(arg);
                }
            }

            if (!linkOnly) {
                Console.Error.WriteLine("mlarm: Missing without linking option (/c)");
                needHelp = true;
            }

            if (needHelp) {
                Usage();
                return 1;
            }

            string arguments = null;
            foreach (string s in outargs) {
                if (arguments != null) {
                    arguments = arguments + " " + s;
                }
                else {
                    arguments = s;
                }
            }

            Process p = new Process();
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.RedirectStandardOutput = false;
            p.StartInfo.FileName = "armasm.exe";
            p.StartInfo.Arguments = arguments;
            int exit = -1;

            Console.WriteLine("    {0} {1}", p.StartInfo.FileName, p.StartInfo.Arguments);
            try {
                p.Start();
                p.WaitForExit();
                exit = p.ExitCode;
            }
            catch (Exception e) {
                Console.WriteLine("mlarm: Exception: {0}", e);
            }
            return exit;
        }
    }
}
