////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   mktests.cs
//
//  Examine assembly metadata to compile a manifest of test code in a Singularity
//  distribution.
//
using System;
using System.Collections;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Runtime.InteropServices;
using System.Text;
using System.Xml;

using Bartok.MSIL;

public class mktests
{
    const string ATTRIBUTE_PREFIX = "Microsoft.Singularity.UnitTest.";

    private static void Usage()
    {
        Console.WriteLine("Usage:\n" +
                          "    mktests /out:<test_manifest_file> [assemblies]\n");
    }

    public static int Main(string[] args)
    {
        if (args.Length == 0) {
            Usage();
            return 0;
        }
        DateTime timeBegin = DateTime.Now;
        ArrayList infiles = new ArrayList();
        string outfile = null;
        for (int i = 0; i < args.Length; i++) {
            string arg = args[i];
            if (arg.StartsWith("-") || arg.StartsWith("/")) {
                if (arg.StartsWith("-out:") || arg.StartsWith("/out:")) {
                    outfile = arg.Substring(arg.IndexOf(":") + 1);
                }
                else  {
                    Console.WriteLine("Malformed argument: \"" + arg + "\"");
                    Usage();
                    return 1;
                }
            }
            else {
                // This is just an assembly name
                infiles.Add(arg);
            }
        }
        if (outfile == null) {
            Console.WriteLine("You must specify the output file.");
            Usage();
            return 1;
        }
        if (infiles.Count == 0) {
            Console.WriteLine("You must specify at least one input file.");
            Usage();
            return 1;
        }
        XmlTextWriter oo = new XmlTextWriter(outfile, null);
        oo.Formatting = Formatting.Indented;
        oo.Indentation = 4;
        try {
            oo.WriteStartDocument();
            if (infiles.Count == 1) {
                oo.WriteComment("Export of tests from: " + infiles[0]);
            }
            else {
                oo.WriteComment("Export of tests from:");
                foreach (string f in infiles) {
                    oo.WriteComment("     " + f);
                }
            }
            oo.WriteStartElement("Profile");
            oo.WriteAttributeString("Name", outfile);
            ProcessAssemblies(oo, infiles);
            oo.WriteEndElement();
            oo.WriteEndDocument();
        }
        finally {
            oo.Close();
        }

        TimeSpan elapsed = DateTime.Now - timeBegin;
        Console.WriteLine("mktests: {0} seconds elapsed.", elapsed.TotalSeconds);
        return 0;
    }

    private static void ProcessAssemblies(XmlTextWriter oo, ArrayList infiles)
    {
        MetaDataResolver resolver =
                new MetaDataResolver(infiles, new ArrayList(), new DateTime(), false, false);

        MetaDataResolver.ResolveCustomAttributes(new MetaDataResolver[] { resolver });
        foreach (MetaData md in resolver.MetaDataList) {
            // Assume that if we are processing an assembly, it will contain tests
            string name = md.Name;
            string pkg;
            string assembly = Tail(name, '\\', out pkg);   // extract filename
            string module = assembly.Substring(0, assembly.IndexOf('.'));       // trim extension
            oo.WriteStartElement("Module");
            oo.WriteAttributeString("Name", module);
            ProcessAssembly(oo, md);
            oo.WriteEndElement();
        }
    }

    private static void ProcessAssembly(XmlTextWriter oo, MetaData md)
    {
        IDictionary<string, MetaDataObject> tests = new SortedDictionary<string, MetaDataObject>();
        IDictionary<string, MetaDataObject> suites = new SortedDictionary<string, MetaDataObject>();
        // Look for the annotation that tells us that this assembly is a stand-alone
        // test app.
        MetaDataAssembly mda = (MetaDataAssembly) md.Assemblies[0];
        foreach (MetaDataCustomAttribute attrib in md.CustomAttributes) {
            MetaDataObject parent = attrib.Parent;
            //Console.WriteLine("Found: {0} in {1} {2}", attrib.Name, parent.FullName, parent.FullNameWithContext);
            if (!attrib.Name.StartsWith(ATTRIBUTE_PREFIX)) {
                continue;
            }
            string attribName = attrib.Name.Substring(ATTRIBUTE_PREFIX.Length);
            switch (attribName) {
                case "TestAppAttribute":
                    break;
                case "TestClassAttribute":
                    suites.Add(attrib.Parent.FullName, attrib);
                    break;
                case "TestMethodAttribute":
                    MetaDataObject m = attrib.Parent;
                    tests.Add(attrib.Parent.FullName, attrib);
                    break;
            }
        }
        string prevSuite = "";
        foreach (KeyValuePair<string, MetaDataObject> kvp in tests) {
            string k = kvp.Key;
            string className;
            string testname = Tail(k, '.', out className);
            if (!suites.ContainsKey(className)) {
                Console.WriteLine("TestMethod declared outside of a TestClass: {0}", k);
                continue;
            }
            if (!prevSuite.Equals(className)) {
                if (! prevSuite.Equals("")) {
                    oo.WriteEndElement();
                }
                oo.WriteStartElement("Suite");
                string ignored;
                oo.WriteAttributeString("Name", Tail(className, '.', out ignored));
                prevSuite = className;
            }
            oo.WriteStartElement("Test");
            oo.WriteAttributeString("Name", testname);
#if EXTRACT_TIMEOUT
            object timeout = psItem.Fields["Test Timeout"].Value;
            if (timeout != null) {
                oo.WriteAttributeString("Timeout", timeout.ToString());
            }
            object knownFailure = psItem.Fields["Test Known Failure"].Value;
            if (knownFailure != null) {
                oo.WriteAttributeString("KnownFailure", knownFailure.ToString());
            }
#endif
            oo.WriteEndElement();
        }
        if (! prevSuite.Equals("")) {
            oo.WriteEndElement();
        }
    }

    // Split a string at the last occcurence of a character, returning both
    // the before and after.  If the character is not present, then the tail
    // is empty and before is the entire string.
    private static string Tail(string it, char pattern, out string before)
    {
        int i = it.LastIndexOf(pattern);
        if (i < 0) {
            before = it;
            return "";
        }
        else {
            before = it.Substring(0, i);
            return it.Substring(i + 1);
        }
    }

    private static void Assert(bool cond, string trueText)
    {
        if (!cond) {
            throw new Exception("Expected: " + trueText);
        }
    }
}
