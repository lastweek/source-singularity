////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Examine assembly metadata to generate test jig code.
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


internal class SuiteDesc
{
    public readonly List<string> tests = new List<string>();
    public string init = null;
    public string cleanup = null;
    public string testInit = null;
    public string testCleanup = null;
}

internal class ModuleDesc
{
    public readonly IDictionary<string, SuiteDesc> suites = new SortedDictionary<string, SuiteDesc>();
    public string init = null;  
    public string cleanup = null;
    public SuiteDesc ProvideSuite(string className)
    {
        SuiteDesc res;
        if (!suites.TryGetValue(className, out res)) {
            res = new SuiteDesc();
            suites.Add(className, res);
        }
        return res;
    }
    public SuiteDesc ProvideSuite(MetaDataObject m, out string child)
    {
        string className;
        child = mktests.Tail(m.FullName, '.', out className);
        return ProvideSuite(className);
    }
}

public class mktests
{
    const string ATTRIBUTE_PREFIX = "Microsoft.Singularity.UnitTest.";

    private string m_outpath;
    private ModuleDesc m_module;
    private IDictionary<string, MetaDataObject> m_suites = new SortedDictionary<string, MetaDataObject>();
 
    // TEMPLATE STRINGS DEFINE AT BOTTOM OF FILE

    private mktests(string path)
    {
        m_outpath = path;
        m_module = new ModuleDesc();
    }

    public static int Main(string[] args)
    {
        if (args.Length != 2) {
            Usage();
            return -1;
        }
        DateTime timeBegin = DateTime.Now;
        string outfile = args[0];
        string infile = args[1];
        ArrayList infiles = new ArrayList();
        infiles.Add(infile);

        mktests it = new mktests(outfile);
        it.ProcessAssembly(infiles);
        //FileStream oo = new FileStream(outfile, FileMode.Create, FileAccess.Write);
//        try {
//        }
//        finally {
//            oo.Close();
//        }

        TimeSpan elapsed = DateTime.Now - timeBegin;
        Console.WriteLine("mkjig: {0} seconds elapsed.", elapsed.TotalSeconds);
        return 0;
    }

    private static void Usage()
    {
        Console.WriteLine("Usage:\n    mkjig <test_jig_source> <assembly> \n");
    }

    private void ProcessAssembly(ArrayList infiles)
    {
        MetaDataResolver resolver =
                new MetaDataResolver(infiles, new ArrayList(), new DateTime(), false, false);

        MetaDataResolver.ResolveCustomAttributes(new MetaDataResolver[] { resolver });
        foreach (MetaData md in resolver.MetaDataList) {
            // Assume that if we are processing an assembly, it will contain tests
            string name = md.Name;
            string prefix = name.Substring(0, name.LastIndexOf('.')); // trim extension
            string module = prefix.Substring(prefix.LastIndexOf('\\')+1);  // extract filename
            ProcessAssembly(md);
        }
    }

    private void ProcessAssembly(MetaData md)
    {
        // Look for the annotation that tells us that this assembly is a stand-alone
        // test app.
        MetaDataAssembly mda = (MetaDataAssembly) md.Assemblies[0];
        foreach (MetaDataCustomAttribute attrib in md.CustomAttributes) {
            MetaDataObject parent = attrib.Parent;
            //Console.WriteLine("Found: {0} in {1} {2}", attrib.Name, parent.FullName, parent.FullNameWithContext);
            if (!attrib.Name.StartsWith(ATTRIBUTE_PREFIX)) {
                continue;
            }
            Console.WriteLine("Found: {0} in {1} {2}", attrib.Name, parent.FullName, parent.FullNameWithContext);
            string attribName = attrib.Name.Substring(ATTRIBUTE_PREFIX.Length);
            string className;
            string item = Tail(attrib.Parent, out className);
            if (attribName == "TestClassAttribute") {
                m_suites.Add(attrib.Parent.FullName, attrib);
            }
            else if (attribName == "TestMethodAttribute") {
                m_module.ProvideSuite(className).tests.Add(item);
            }
            else if (attribName == "ClassInitializeAttribute") {
                m_module.ProvideSuite(className).init = item;
            }
            else if (attribName == "ClassCleanupAttribute") {
                m_module.ProvideSuite(className).cleanup = item;
            }
            else if (attribName == "TestInitializeAttribute") {
                m_module.ProvideSuite(className).testInit = item;
            }
            else if (attribName == "TestCleanupAttribute") {
                m_module.ProvideSuite(className).testCleanup = item;
            }
            else if (attribName == "AssemblyInitializeAttribute") {
                m_module.init = item;
            }
            else if (attribName == "TestCleanupAttribute") {
                m_module.cleanup = item;
            }
            else {
                // IGNORE
            }
        }
        StringBuilder suiteStr = new StringBuilder();
        StringBuilder jigsStr = new StringBuilder();
        foreach (KeyValuePair<string, SuiteDesc> kvp in m_module.suites) {
            string fullname = kvp.Key;
            if (!m_suites.ContainsKey(fullname)) {
                Console.WriteLine("TestMethod declared outside of a TestClass: {0}", fullname);
                continue;
            }
            string pkg;
            string className = Tail(fullname, '.', out pkg);
            SuiteDesc desc = kvp.Value;
            GenTests(className, pkg, desc, suiteStr);
            jigsStr.AppendFormat(SUITE_CASE_TEMPLATE, className, pkg);
        }
        string modulename = "Foo";
        StringBuilder otherStr = new StringBuilder();
        //AppendOpt(MODULE_INIT_TEMPLATE, m_module.init, otherStr);
        //AppendOpt(MODULE_INIT_TEMPLATE, m_module.cleanup, otherStr);
        string content = string.Format(FILE_TEMPLATE, modulename, jigsStr, otherStr, suiteStr);
        File.WriteAllText(m_outpath, content);
    }

    private void GenTests(string className, string pkg, SuiteDesc desc, StringBuilder suiteStr)
    {
        StringBuilder caseStr = new StringBuilder();
        desc.tests.Sort();
        foreach (string t in desc.tests) {
            caseStr.AppendFormat(TEST_CASE_TEMPLATE, t);
        }
        StringBuilder otherStr = new StringBuilder();
        AppendOpt(INIT_TEMPLATE, desc.init, otherStr);
        AppendOpt(CLEANUP_TEMPLATE, desc.cleanup, otherStr);
        // TODO test init
        suiteStr.AppendFormat(SUITE_TEMPLATE, className, pkg, caseStr, otherStr);
    }

    private static void AppendOpt(string format, string optS, StringBuilder otherStr)
    {
        if (optS != null) {
            otherStr.AppendFormat(format, optS);
        }
    }

    // Split a string at the last occcurence of a character, returning both
    // the before and after.  If the character is not present, then the tail
    // is empty and before is the entire string.
    public static string Tail(string it, char pattern, out string before)
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

    public static string Tail(MetaDataObject m, out string before)
    {
        return Tail(m.FullName, '.', out before);
    }

    //Assert(m != null, "TestMethod attribute is on a method");
    //                        oo.WriteStartElement("Suite");
    //                        oo.WriteAttributeString("Name", );
    //                        inSuite = true;
    //                    object timeout = psItem.Fields["Test Timeout"].Value;
    //                    if (timeout != null) {
    //                        oo.WriteAttributeString("Timeout", timeout.ToString());
    //                    }
    //                    object knownFailure = psItem.Fields["Test Known Failure"].Value;
    //                    if (knownFailure != null) {
    //                        oo.WriteAttributeString("KnownFailure", knownFailure.ToString());
    //                    }
    private static void Assert(bool cond, string trueText)
    {
        if (!cond) {
            throw new Exception("Expected: " + trueText);
        }
    }

    private const string TEST_INIT_TEMPLATE = @"
        override public void TestInitialize()
        {{
            m_test.{0}();
        }}
";

    private const string TEST_CLEANUP_TEMPLATE = @"
        override public void TestCleanup()
        {{
            m_test.{0}();
        }}
";

    private const string INIT_TEMPLATE = @"
        override public void Initialize()
        {{
            m_test.{0}();
        }}
";

    private const string CLEANUP_TEMPLATE = @"
        override public void Cleanup()
        {{
            m_test.{0}();
        }}
";

    private const string TEST_CASE_TEMPLATE = @"
                case ""{0}"": 
                    m_test.{0}(); 
                    break;
";

    private const string SUITE_CASE_TEMPLATE = @"
                case ""{0}"": 
                    return new {1}.{0}_Jig(log);
";

    // suite name, suite namespace, suite cases, suite other
    private const string SUITE_TEMPLATE = @"
namespace {1} {{
    internal class {0}_Jig : SuiteJig
    {{
        private {0}! m_test;

        public {0}_Jig(TestLog! log)
        {{
            {0} t = new {0}();
            t.SetLog(log);
            m_test = t;
        }}

        override public void DoTest(string! test)
        {{
            switch (test) {{
{2}
                default:
                    base.DoTest(test);
                    break;
            }}
        }}
{3}
     }}
}}
";

    // module name, module cases, module other, suite jigs
    private const string FILE_TEMPLATE = @"
///////////////////////////////////////////////////////////////////////////////
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  Generated test jig code

using System;
using System.Threading;

using Microsoft.Singularity.UnitTest;

using Microsoft.Singularity.Channels;
using Microsoft.Contracts;
using Microsoft.SingSharp.Reflection;
using Microsoft.Singularity.Applications;
using Microsoft.Singularity.Io;
using Microsoft.Singularity.Configuration;
using Microsoft.Singularity.Test.Contracts;
using Microsoft.Singularity.Configuration;

[assembly: Transform(typeof(ApplicationResourceTransform))]

// GENERATED SUITE JIGS
{3}

namespace Microsoft.Singularity.Applications {{

    // GENERATED MODULE JIG
    public class {0}_ModuleJig : ModuleJig
    {{
        override public SuiteJig GetSuite(string! name, TestLog! log)
        {{
            switch (name) {{
{1}
                default:
                    return base.GetSuite(name, log);
            }}
        }}
{2}
    }}

    [ConsoleCategory(HelpMessage=""ModuleTester"", Action=""test"")]
    internal class ModuleTest_Category {{
        [InputEndpoint(""data"")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;
        [OutputEndpoint(""data"")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        [CustomEndpoint]
        public readonly TRef<ModuleTesterContract.Exp:START> testerRef;

        reflective internal ModuleTest_Category();

        internal int AppMain() {{
            if (testerRef == null) {{
                DebugStub.WriteLine(""TEST endpoint not setup"");
                throw new Exception(""TEST endpoint not setup "");
            }}
            ModuleTesterContract.Exp tester = testerRef.Acquire();
            if (tester == null) {{
                DebugStub.WriteLine(""TEST unable to acquite handle to test driver"");
                throw new Exception(""Unable to acquire handle to the test driver"");
            }}
            ModuleJig jig = new {0}_ModuleJig();
            ModuleTester.RunTests(tester, jig);
            return 0;
        }}
    }}

    // Currently required to get process launch code generated.
    [ConsoleCategory(HelpMessage=""Run using the test framework"", DefaultAction=true)]
    internal class ModuleConsole_Category {{
        [InputEndpoint(""data"")]
        public readonly TRef<UnicodePipeContract.Exp:READY> Stdin;
        [OutputEndpoint(""data"")]
        public readonly TRef<UnicodePipeContract.Imp:READY> Stdout;

        reflective internal ModuleConsole_Category();

        internal int AppMain() {{
            Console.WriteLine(""This is a test application and can only be run from the tester."");
            return -1;
        }}
    }}
}}
";
}
