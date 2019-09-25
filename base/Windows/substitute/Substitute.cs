///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   Substitute.cs
//
//  Note:
//

using System;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Singularity.Tools
{
    class Substitute
    {
        static bool unescape = false;

        private static void Apply(TextReader input,
                                  TextWriter output,
                                  string     inPattern,
                                  string     outPattern)
        {
            if (unescape)
                outPattern = Regex.Unescape(outPattern);

            string line;
            while (null != (line = input.ReadLine())) {
                line = Regex.Replace(line, inPattern, outPattern);
                output.WriteLine(line);
            }
        }

        public static int Main(string[] args)
        {
            int start = 0;

            int length = args.Length;
            if (length > 0 && String.Equals(args[0], "-e")) {
                unescape = true;
                start = 1;
            }

            switch (args.Length-start) {
                case 2:
                    Apply(Console.In, Console.Out, args[start+0], args[start+1]);
                    return 0;

                case 3:
                    using (StreamReader sr = new StreamReader(args[start+2])) {
                        Apply(sr, Console.Out, args[start+0], args[start+1]);
                    }
                    return 0;

                case 4:
                    using (StreamReader sr = new StreamReader(args[start+2])) {
                        if (sr.Peek() >= 0) {
                            using (StreamWriter sw = new StreamWriter(args[start+3], 
                                                                      false, sr.CurrentEncoding)) {
                                Apply(sr, sw, args[start+0], args[start+1]);
                            }
                        }
                    }
                    return 0;

                default:
                    Console.WriteLine("Usage: substitute [-e] <string1> <string2> [<Input file> [<OutputFile>]]");
                    return -1;
            }
        }
    }
}
