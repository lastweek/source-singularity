///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   cmp.cs
//
//  Note:
//

using System;
using System.IO;

namespace Microsoft.Singularity.Applications
{
    public class Cmp
    {
        public enum ExitCode :int {
            FilesEquivalent  = 0,
            FilesDiffer      = 1,
            Usage            = 2,
            Error            = 3
        }

        public static void Exit(ExitCode e)
        {
            Environment.Exit((int)e);
        }

        public static void Usage()
        {
            Console.WriteLine("Cmp <fileA> <fileB>");
            Exit(ExitCode.Usage);
        }

        public static FileInfo GetFileInfo(string filepath)
        {
            try {
                return new FileInfo(filepath);
            }
            catch (Exception e) {
                Console.Error.WriteLine("Exception when accessing {0} : {1}",
                                        filepath, e);
            }
            return null;
        }

        public static void Main(string [] args)
        {
            if (args.Length != 2) {
                Usage();
            }

            FileInfo a = GetFileInfo(args[0]);
            if (a == null) {
                Exit(ExitCode.Error);
            }

            FileInfo b = GetFileInfo(args[1]);
            if (b == null) {
                Exit(ExitCode.Error);
            }

            if (a.Length != b.Length) {
                Exit(ExitCode.FilesDiffer);
            }

            ExitCode ec = ExitCode.FilesDiffer;
            try {
                using (Stream sa = a.OpenRead()) {
                    using (Stream sb = b.OpenRead()) {
                        int ba, bb;
                        do {
                            ba = sa.ReadByte();
                            bb = sb.ReadByte();
                        } while ((ba == bb) && (ba != -1));

                        ec = (ba == bb) ? ExitCode.FilesEquivalent : ExitCode.FilesDiffer;
                    }
                }
                Exit(ec);
            } catch (Exception e) {
                Console.Error.WriteLine(
                    "Exception during attempted comparison: {0}",
                    e
                    );
                Exit(ExitCode.Error);
            }
        }
    }
}
