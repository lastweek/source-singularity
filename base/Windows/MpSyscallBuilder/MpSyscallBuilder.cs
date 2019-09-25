// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

////////////////////////////////////////////////////////////
//
// File: MpSyscallBuilder.cs
//
//

using System;
using System.Collections;
using System.IO;


public class MpSyscallBuilder
{
    public class AbiDef
    {
        public AbiDef() {}

        public int abiNum; // this number if important
        public string decl;
        public string longReturnType;
        public string shortReturnType;
        public string longMethodName;
        public string longClassName;
        public string namespaceName;
        public string shortClassName;
        public string shortMethodName;
        public string shortMethodNameWithG;
        public string [] longParamArray;
        public string [] shortParamArray;
    }

    const string s4 = "    ";
    const string s8 = s4 + s4;
    const string s12 = s8 + s4;
    const string s16 = s12 + s4;


    static Hashtable globalClassTable = new Hashtable();
    static Hashtable structTable = new Hashtable();
    static Hashtable paramTable = new Hashtable();
    static Hashtable linkStackTable = new Hashtable();

    static Hashtable namespaceTable = new Hashtable();

    static Hashtable typeConverter = new Hashtable();

    // we allow 1000 abi defs
    const int MAX_ABI_DEF = 1000;
    static AbiDef [] sequentialAbiDef = new AbiDef [MAX_ABI_DEF];

    static int curAbiNum = -1;
    static int lineNumber = 0;
    static int printCount = 0;

    static bool genSingStubV1Def = false;
    static bool genApAbiStub = false;
    static bool genBspAbiStub = false;
    static bool genMpSyscallsHeader = false;
    static bool genMpSyscallsImpl = false;

    static void AddType(string t)
    {
        if (t.StartsWith("struct ")) {
            int end = t.IndexOf(" ", 7);
            if (end == -1) {
                end = t.Length;
            }
            string structName = t.Substring(7, end - 7);

            //if (!structTable.ContainsKey(structName)) {
            //Console.WriteLine("// Adding " + structName);
            //}

            if (end < t.Length) {
                structTable[structName] = "";
            }
            else {
                int ssize;
                if (structName.EndsWith("Handle")) {
                    ssize = 4;
                }
                else {
                    if (!paramTable.ContainsKey("struct " + structName)) {
                        throw new Exception("unknown struct type: " + t);
                    }
                    ssize = (int) paramTable["struct " + structName];
                }
                structTable[structName] = "char data[" + ssize + "];";
            }
        }
    }

    static void AddTypeToStructTable(string t)
    {
        if (t.StartsWith("struct ")) {
            int end = t.IndexOf(" ", 7);
            if (end == -1) {
                end = t.Length;
            }
            string structName = t.Substring(7, end - 7);

            //if (!structTable.ContainsKey(structName)) {
            //Console.WriteLine("// Adding " + structName);
            //}

            if (end < t.Length) {
                structTable[structName] = "";
            }
            else {
                int ssize;
                if (structName.EndsWith("Handle")) {
                    ssize = 4;
                }
                else {
                    if (!paramTable.ContainsKey("struct " + structName)) {
                        throw new Exception("unknown struct type: " + t);
                    }
                    ssize = (int) paramTable["struct " + structName];
                }
                structTable[structName] = "char data[" + ssize + "];";
            }
        }
    }

    static int GetTypeSize(string type)
    {
        int size;
        if (type.EndsWith("*") || type.EndsWith("Handle")) {
            size = 4;
        }
        else {
            if (!paramTable.ContainsKey(type)) {
                throw new Exception ("unknown parameter type: " + type);
            }
            size = (int) paramTable[type];
        }
        return size;
    }


    ////////////////////////////////////////////////////////////////
    //
    public static void PrintNamespaceTable()
    {
        AbiDef abiDef;
        Hashtable nsClassTable, methodTable;
        printCount = 0;

        Console.WriteLine("\n");
        Console.WriteLine("/////////////////////////////////////");
        Console.WriteLine("//");
        Console.WriteLine("// This is the namespace hashtable : ");
        Console.WriteLine("//");
        Console.WriteLine("/////////////////////////////////////\n");

        foreach (string namespaceName in namespaceTable.Keys) {

            Console.WriteLine("\n" + namespaceName);
            Console.WriteLine("###################################################");

            nsClassTable = (Hashtable)namespaceTable[namespaceName];

            foreach (string className in nsClassTable.Keys) {

                Console.WriteLine("\n" + "  " + className);
                Console.WriteLine("  =================================");

                methodTable = (Hashtable)nsClassTable[className];

                foreach (string decl in methodTable.Keys) {

                    abiDef = (AbiDef)methodTable[decl];
                    PrintAbiDef(abiDef, "    ");
                }
            }
        }
    }


    ////////////////////////////////////////////////////////////////
    // Print Abi Def
    public static void PrintAbiDef(AbiDef ad, string pre)
    {
        Console.WriteLine(pre + "\n[" + printCount++ + "]");
        Console.WriteLine(pre + ad.decl);
        Console.WriteLine(pre + "---------------------------------------------------");
        Console.WriteLine(pre + "    ABI number      : <{0,3}>", ad.abiNum);
        Console.WriteLine(pre + "    longReturnType  : <" + ad.longReturnType + ">");
        Console.WriteLine(pre + "    shortReturnType : <" + ad.shortReturnType + ">" +
                          "  sz: " + GetTypeSize(ad.longReturnType));

        Console.WriteLine(pre + "    longMethodName  : <" + ad.longMethodName + ">");
        Console.WriteLine(pre + "    longClassName   : <" + ad.longClassName + ">");
        Console.WriteLine(pre + "    namespaceName   : <" + ad.namespaceName + ">");
        Console.WriteLine(pre + "    shortClassName  : <" + ad.shortClassName + ">");
        Console.WriteLine(pre + "    shortMethodName : <" + ad.shortMethodName + ">");
        Console.WriteLine(pre + "    shortMethodName2: <" + ad.shortMethodNameWithG + ">");

        // test param
        for (int v = 0; v < ad.longParamArray.Length; v++) {
            string p = "        ";
            if (ad.longParamArray[v] != "") {
                Console.WriteLine(pre + "    param " + v + " : ");
                Console.WriteLine(pre + p + "longParam     : <" +
                                  ad.longParamArray[v] + ">");
                Console.WriteLine(pre + p + "shortParam    : <" +
                                  ad.shortParamArray[v] + ">" +
                                  "  sz: " + GetTypeSize(ad.longParamArray[v]));
            }
        }
        Console.WriteLine();
    }



    ////////////////////////////////////////////////////////////////
    // Option      : genSingStubV1Def
    // Input file  : $(OBJ)/Singularity.V1.def
    // Output file : $(OBJ)/SingularityStub.V1.def
    // Note        : This generates SingularityStub.V1.def which is
    //               basically Singularity.V1.def plus the stubs
    //               definition
    // Example     : Given a line like this
    //               ?g_Abi@Struct_Micr_Sing_V1_Services_ProcessService@@SIHH@Z
    //               It adds the new stub function in the new stub struct:
    //               ?g_StubAbi@Struct_Micr_Sing_V1_Services_ProcessService@@SIHH@Z
    public static void GenerateSingularityStubV1Def()
    {
        // String Indexes:
        // ?g_Break@Struct_Microsoft_Singularity_V1_Services_DebugService@@SIXXZ
        // a       b                                        c            d
        //  method             namespaceName                  structName   suffix
        int a, b, c, d, tmp;
        string methodName = "";
        string structName = "";
        string namespaceName = "";
        string suffix = "";

        lineNumber = 0;

        while (true) {

            // read line
            string s = Console.ReadLine();
            lineNumber++;
            if (s == null) {
                break;
            }

            // print the line first
            Console.WriteLine(s);

            // is this abi definition
            a = s.IndexOf('?');
            if (a == -1) {
                continue;
            }

            // At this point, we currently does not support some files
            // For example: EndpointCore.cs is not located in
            // Singularity/V1/Services/EndpointCore.cs
            // instead in Singularity/Channels/EndpointCore
            // So we're not creating the stubs for here for now.
            // Need to think some solutions later.
            if (s.IndexOf("_EndpointCore@") != -1) {
                continue;
            }


            b = s.IndexOf('@');
            d = s.IndexOf('@', b+1);
            tmp = b;
            c = b;
            while (true) {
                tmp = s.IndexOf('_', tmp+1);
                if (tmp == -1 || tmp > d) {
                    break;
                }
                c = tmp;
            }

            methodName = s.Substring(a, b-a); // include '?'
            namespaceName = s.Substring(b+1, c-(b+1));
            structName = s.Substring(c+1, d-(c+1));
            suffix = s.Substring(d, s.Length-d);

            // add "Stub" to methodName
            if (methodName.IndexOf("?g_") != -1) {
                methodName = methodName.Replace("?g_", "?g_Stub");
            }
            else if (methodName.IndexOf("?m_") != -1) {
                methodName = methodName.Replace("?m_", "?m_Stub");
            }

            // add "Stub" to structName
            // Nope not necessary ....
            // structName = "Stub" + structName;

            // Console.WriteLine("  namespace : <" + namespaceName + ">");
            // Console.WriteLine("  struct    : <" + structName + ">");
            // Console.WriteLine("  method    : <" + methodName + ">");
            // Console.WriteLine("  suffix    : <" + suffix + ">");

            Console.WriteLine("    " + methodName + "@" + namespaceName + "_" +
                              structName + suffix);
        }
    }




    ////////////////////////////////////////////////////////////////
    // Array string for storing parameter
    // We allow maximum of 20 parameters. If not enough, change
    // the constant.
    public static string [] GetParamArray() {
        string [] paramArray = new string [20];
        for (int i = 0; i < paramArray.Length; i++) {
            paramArray[i] = "";
        }
        return paramArray;
    }

    ////////////////////////////////////////////////////////////////
    // The function separates a long struct name into two parts
    // divided by the last underscore mark "_"
    // Example:
    //   longName  : struct Struct_Micr_Sing_V1_Services_SharedHeapService_Allocation *
    //   firstPart : struct Struct_Micr_Sing_V1_Services_SharedHeapService_
    //   secondPart: Allocation *
    // WARNING:
    //   However we must careful with types that have "_". So we need to check if it
    //   is a struct or not, if not, we just set secondPart = longName
    public static void SeparateLongStructName(string longName, out string firstPart,
                                              out string secondPart)
    {
        int tmp, i=0;
        if (longName.IndexOf("_") == -1) {
            firstPart = "ERROR IGNORE";
            secondPart = longName;
            return;
        }

        // this is not a struct
        if (longName.IndexOf("Struct_") == -1) {
            firstPart = "";
            secondPart = longName;
            return;
        }

        tmp = 0;
        while (true) {
            tmp = longName.IndexOf('_', tmp+1);
            if (tmp == -1) {
                break;
            }
            i = tmp;
        }
        firstPart = longName.Substring(0, i);
        secondPart = longName.Substring(i+1, longName.Length-(i+1));
    }


    public static void SeparateNamespaceAndClass(string longName,
                                                 out string nsName,
                                                 out string className)
    {
        int tmp = 0;
        int i = 0;
        tmp = 0;
        while (true) {
            tmp = longName.IndexOf('.', tmp+1);
            if (tmp == -1) {
                break;
            }
            i = tmp;
        }
        nsName = longName.Substring(0, i);
        className = longName.Substring(i+1, longName.Length-(i+1));
    }

    // increase abi number number
    static void IncrementAbiNumber(string s)
    {
        if (s.IndexOf("?g_") != -1 || s.IndexOf("?m_") != -1) {
            curAbiNum++;
        }
    }



    ////////////////////////////////////////////////////////////////
    // Option      : genApAbiStub
    // Input file  : $(OBJ)/SingularityStub.V1.dumpbin
    // Output file : StubXXX.cs (Find all Stub*.cs files
    // Note        : This create the Stub files which contains the stub functions
    //               that will perform the marshaling and IPI
    // Example:
    //
    //
    public static void GenerateApAbiStub()
    {
        printCount = 0;
        string s;
        AbiDef abiDef;
        while (true) {
            s = Console.ReadLine();
            lineNumber++;

            // end of file
            if (s == null) {
                break;
            }

            // We only create stub files and functions for abi definition that has
            // g_Stub or m_Stub
            if (s.IndexOf("?g_Stub") == -1 && s.IndexOf("?m_Stub") == -1) {
                continue;
            }

            IncrementAbiNumber(s);

            abiDef = new AbiDef();

            ParseLineToAbiDef(s, abiDef);
            // PrintAbiDef(abiDef, "");

            // Now we add abiDef to hashtable
            AddAbiDefToHashTable(abiDef);
        }

        // test
        PrintNamespaceTable();
        BeginCreatingApAbiStubFromNamespaceTable();

    }


    ////////////////////////////////////////////////////////////////
    //
    // namespaceTable[Struct_Microsoft_Singularity_V1_Services] --> nsClassTable
    // nsClassTable[ProcessService] --> methodTable
    // methodTable[decl] -> abiDef
    //
    public static void AddAbiDefToHashTable(AbiDef abiDef)
    {
        //
        Hashtable nsClassTable = (Hashtable)namespaceTable[abiDef.namespaceName];
        if (nsClassTable == null) {
            nsClassTable = new Hashtable();
            namespaceTable[abiDef.namespaceName] = nsClassTable;
        }

        Hashtable methodTable = (Hashtable)nsClassTable[abiDef.shortClassName];
        if (methodTable == null) {
            methodTable = new Hashtable();
            nsClassTable[abiDef.shortClassName] = methodTable;
        }

        methodTable[abiDef.decl] = abiDef;
    }


    ////////////////////////////////////////////////////////////////
    //
    // We need to create the fullFileName = dirName + fileName
    //
    public static void BeginCreatingApAbiStubFromNamespaceTable()
    {
        AbiDef abiDef;
        Hashtable nsClassTable, methodTable;
        string abiFileName, stubFileName, dirName, fileName;

        foreach (string namespaceName in namespaceTable.Keys) {

            nsClassTable = (Hashtable)namespaceTable[namespaceName];

            dirName = namespaceName.Replace("Struct_Microsoft_", "");
            dirName = dirName.Replace("_","/");


            foreach (string className in nsClassTable.Keys) {

                methodTable = (Hashtable)nsClassTable[className];

                fileName = className + ".cs";
                abiFileName = dirName + "/" + fileName;

                // Now we get the abiFileName at this point. e.g.
                // Singularity/V1/Services/ProcessService.cs
                // Next we want to copy the file to
                // Singularity/V1/Services/StubProcessService.cs with
                // exception the last bracket "}" because we want to
                // add the stub functions to the file
                stubFileName = GetStubFileName(abiFileName);

                Console.WriteLine("Copy " + abiFileName);
                Console.WriteLine("     " + stubFileName);

                if (File.Exists(stubFileName)) {
                    File.Delete(stubFileName);
                }

                FileStream fsOutput =
                    new FileStream(stubFileName, FileMode.Create, FileAccess.Write);
                StreamWriter stubOut = new StreamWriter(fsOutput);

                FileStream fsInput =
                    new FileStream(abiFileName, FileMode.Open, FileAccess.Read);
                StreamReader abiIn = new StreamReader(fsInput);

                CopyAbiFileToStubFile(abiIn, stubOut, abiFileName, stubFileName, className);


                foreach (string decl in methodTable.Keys) {

                    abiDef = (AbiDef)methodTable[decl];
                    WriteApAbiStubClassMethod(stubOut, abiDef);

                }

                WriteApAbiStubClassFooter(stubOut);

                abiIn.Close();
                stubOut.Close();
            }
        }
    }

    // Given abiFileName a/b/c/d/ProcessService.cs
    // this function returns a/b/c/d/StubProcessService.cs
    public static string GetStubFileName(string abiFileName)
    {
        string dirName, fileName;
        int tmp = 0;
        int i = 0;
        tmp = 0;
        while (true) {
            tmp = abiFileName.IndexOf('/', tmp+1);
            if (tmp == -1) {
                break;
            }
            i = tmp;
        }
        dirName = abiFileName.Substring(0, i);
        fileName = abiFileName.Substring(i+1, abiFileName.Length-(i+1));

        return (dirName + "/Stub" + fileName);

    }

    // Copy abi file to stub file, except the last bracket
    // This is a copy line per line ... maybe in future we should
    // write a quick script?
    public static void CopyAbiFileToStubFile(StreamReader abiIn, StreamWriter stubOut,
                                             string abiFileName, string stubFileName,
                                             string className)
    {
        stubOut.WriteLine("///////////////////////////////////////////////////////");
        stubOut.WriteLine("// ");
        stubOut.WriteLine("// THIS IS AUTOMATICALLY GENERATED FILE, DO NOT MODIFY ");
        stubOut.WriteLine("// ");
        stubOut.WriteLine("// Generated by: Windows/MpSyscall/MpSyscallBuilder.exe");
        stubOut.WriteLine("// ");
        stubOut.WriteLine("// Abi  File " + abiFileName);
        stubOut.WriteLine("// Stub File " + stubFileName);
        stubOut.WriteLine("// ");
        stubOut.WriteLine("");

        bool isClassDeclared = false;

        string s = abiIn.ReadLine();
        while (s != null) {

            if (s.IndexOf("public struct " + className) != -1) {
                isClassDeclared = true;
            }

            // find the last bracket after class declaration
            if (isClassDeclared && s.IndexOf("    }") == 0) {
                stubOut.WriteLine("");
                break;
            }
            stubOut.WriteLine(s);
            s = abiIn.ReadLine();
        }
    }


    public static void WriteApAbiStubClassFooter(StreamWriter sw)
    {
        sw.WriteLine("    }");
        sw.WriteLine("}");
    }

    public static void WriteApAbiStubClassMethod(StreamWriter sw, AbiDef ad)
    {
        string csType;

        sw.WriteLine(s8 + "[ExternalEntryPoint]");

        // Right now we just treat all stub functions as non CLS compliant
        // For 100% correctness, this is not true
        sw.WriteLine(s8 + "[CLSCompliant(false)]");

        // function declare
        sw.Write(s8 + "public static unsafe " +
                 GetCsType(ad.shortReturnType, ad.longReturnType) + " " +
                     ad.shortMethodName + "(");

        for (int i = 0; i < ad.shortParamArray.Length; i++) {
            if (ad.shortParamArray[i] != "") {
                if (ad.shortParamArray[i] != "void") {
                    csType = GetCsType(ad.shortParamArray[i], ad.longParamArray[i]);
                    if (i == 0) {
                        sw.Write(csType + " p" + i) ;
                    }
                    else {
                        sw.Write(", " + csType + " p" + i);
                    }
                }
            }
        }
        sw.WriteLine(")");
        sw.WriteLine(s8 + "{");

        // write function body now
        bool  allApAbiStub  = true;
        if (allApAbiStub) {
            WriteApAbiStubClassMethodBodyGeneric(sw, ad);
        }
        else if (ad.shortMethodName ==  "StubHelloProcessABI" ||
            ad.shortMethodName ==  "StubTestAbiCallOne" ||
            ad.shortMethodName ==  "StubTestAbiCallTwo" ||
            ad.shortMethodName ==  "StubTestAbiCallThree" ||
            false) {
            WriteApAbiStubClassMethodBodyGeneric(sw, ad);
            // WriteApAbiStubClassMethodBodySample(sw, ad);
        }
        else {
            WriteApAbiStubClassMethodBodyBlank(sw, ad);
        }

        sw.WriteLine(s8 + "}");
        sw.WriteLine();
    }

    public static string stubHelloProcessABICode =
"\n            int ap  = Processor.GetCurrentProcessorId();" +
"\n            int bsp = 0;" +
"\n" +
"\n            DebugStub.WriteLine" +
"\n                (\"\\n\\nHSG: ** cpu.{0} StubHelloProcessABI({1})\"," +
"\n                 __arglist(ap, p0));" +
"\n            DebugStub.WriteLine(\"HSG: ** -------------------------\");" +
"\n" +
"\n            bool iflag = Processor.DisableInterrupts();" +
"\n" +
"\n            MpExecution.AbiCall abiCall = new MpExecution.AbiCall();" +
"\n" +
"\n            // 1) set up all the parameters" +
"\n            abiCall.argVal = p0;" +
"\n" +
"\n            // prepare IPI" +
"\n            DebugStub.Print" +
"\n                (\"HSG: ** cpu.{0} PutAbiCall(cpu.{1}, arg.{2}) --> \"," +
"\n                 __arglist(ap, bsp, abiCall.argVal));" +
"\n" +
"\n            // 2) register the abiCall," +
"\n            //    after this, we get the position" +
"\n            int pos = MpExecution.PutAbiCall(bsp, abiCall);" +
"\n" +
"\n            DebugStub.WriteLine(\"pos.{0}\", __arglist(pos));" +
"\n" +
"\n            DebugStub.WriteLine" +
"\n                (\"HSG: ** cpu.{0} SendAbiCall(cpu.{1}, cpu.{2})\"," +
"\n                 __arglist(ap, ap, bsp));" +
"\n" +
"\n            // 3) send" +
"\n            MpExecution.SendAbiCall(ap, bsp);" +
"\n" +
"\n            DebugStub.WriteLine" +
"\n                (\"HSG: ** cpu.{0} WaitAbiCall(cpu.{1}, pos.{2}) ... zzz \", " +
"\n                 __arglist(ap, bsp, pos));" +
"\n" +
"\n            // 4) spin until done" +
"\n            MpExecution.WaitAbiCall(bsp, pos, out abiCall);" +
"\n" +
"\n            // 5) we have the return value" +
"\n            int retval = abiCall.retVal;" +
"\n" +
"\n            DebugStub.WriteLine" +
"\n                (\"HSG: ** cpu.{0} is waken up and receives retval.{1}\"," +
"\n                 __arglist(ap, retval));" +
"\n" +
"\n            DebugStub.WriteLine" +
"\n                (\"HSG: ** cpu.{0} ReleaseAbiCall(cpu.{1}, pos.{2})\"," +
"\n                 __arglist(ap, bsp, pos));" +
"\n" +
"\n            // 6) release abiCall" +
"\n            MpExecution.ReleaseAbiCall(bsp, pos);" +
"\n" +
"\n            Processor.RestoreInterrupts(iflag);" +
"\n" +
"\n            return retval;" +
"\n";


    public static void WriteApAbiStubClassMethodBodySample(StreamWriter sw, AbiDef ad)
    {
        string type = GetCsType(ad.shortReturnType, ad.longReturnType);

        sw.WriteLine(s12 + "DebugStub.WriteLine(\"HSG: ** In " +
                     ad.shortMethodName  + "{0}\", __arglist(p0));");

        sw.WriteLine(stubHelloProcessABICode);

    }

    public static void WriteApAbiStubClassMethodBodyGeneric(StreamWriter sw, AbiDef ad)
    {
        int curOffset, size;

        // some variables, ap, bsp, iflag, retval
        sw.WriteLine(s12 + "DebugStub.WriteLine(\"HSG: ** " + ad.shortMethodName + "()\");");
        sw.WriteLine(s12 + "int ap  = Processor.GetCurrentProcessorId();");
        sw.WriteLine(s12 + "int bsp = 0;");
        sw.WriteLine(s12 + "bool iflag;");
        sw.WriteLine(s12 + "");



        // declare return value
        if (ad.shortReturnType != "void") {
            sw.WriteLine(s12 +
                         GetCsType(ad.shortReturnType, ad.longReturnType) +
                         " retval;");
            sw.WriteLine(s12 + "");
        }


        // get the mpCall
        sw.WriteLine(s12 + "iflag = Processor.DisableInterrupts();");
        sw.WriteLine(s12 + "MpExecution.MpCall mpCall = MpExecution.ReserveMpCall(bsp);");
        sw.WriteLine(s12 + "Processor.RestoreInterrupts(iflag);");

        sw.WriteLine(s12 + "");
        sw.WriteLine(s12 + "if (mpCall == null) {");
        sw.WriteLine(s12 + "    DebugStub.WriteLine(\"MpCall buffer full\");");
        sw.WriteLine(s12 + "    DebugStub.Break();");
        sw.WriteLine(s12 + "}");
        sw.WriteLine(s12 + "");

        // set mpCall number
        sw.WriteLine(s12 + "mpCall.abiNum = " + ad.abiNum + "; // abi number");
        sw.WriteLine(s12 + "");

        // start marshal arguments
        sw.WriteLine(s12 + "// future: need check not to overrun buffer");
        sw.WriteLine(s12 + "// marshall arguments");
        sw.WriteLine(s12 + "fixed (byte *baseArg = & mpCall.argBuffer[0] ) {");

        curOffset = 0;
        for (int v = 0; v < ad.shortParamArray.Length; v++) {
            if (ad.shortParamArray[v] != "" && ad.shortParamArray[v] != "void") {
                size = GetTypeSize(ad.longParamArray[v]);
                sw.WriteLine(s12 + "    Buffer.MoveMemory(baseArg+" + curOffset +
                             " , (byte*) & p" + v + " , " + size + ");");
                curOffset += size;
            }
        }
        sw.WriteLine(s12 + "}");
        sw.WriteLine(s12 + "");

        // send mp call and wait
        sw.WriteLine(s12 + "iflag = Processor.DisableInterrupts();");
        sw.WriteLine(s12 + "MpExecution.SendMpCall(ap, bsp);");
        sw.WriteLine(s12 + "Processor.RestoreInterrupts(iflag);");

        sw.WriteLine(s12 + "");
        sw.WriteLine(s12 + "MpExecution.WaitMpCall(bsp, mpCall.position);");
        sw.WriteLine(s12 + "");

        // return value is available
        if (ad.shortReturnType != "void") {
            sw.WriteLine(s12 + "// get return value");
            sw.WriteLine(s12 + "fixed (byte *baseRet = & mpCall.retBuffer[0] ) {");
            sw.WriteLine(s12 + "    Buffer.MoveMemory( (byte*) & retval , baseRet, " +
                         GetTypeSize(ad.longReturnType) + ");");
            sw.WriteLine(s12 + "}   ");
            sw.WriteLine(s12 + "");
        }

        // copy back out parameter
        sw.WriteLine(s12 + "// also in case we have 'out param', copy back parameters");
        sw.WriteLine(s12 + "fixed (byte *baseArg = & mpCall.argBuffer[0] ) {");

        curOffset = 0;
        for (int v = 0; v < ad.shortParamArray.Length; v++) {
            if (ad.shortParamArray[v] != "" && ad.shortParamArray[v] != "void") {
                size = GetTypeSize(ad.longParamArray[v]);
                sw.WriteLine(s12 + "    Buffer.MoveMemory((byte*) & p" + v +
                             " , baseArg+" + curOffset + " , " + size + ");");
                curOffset += size;
            }
        }
        sw.WriteLine(s12 + "}");
        sw.WriteLine(s12 + "");

        // release and return value
        sw.WriteLine(s12 + "iflag = Processor.DisableInterrupts();");
        sw.WriteLine(s12 + "MpExecution.ReleaseMpCall(bsp, mpCall.position);");
        sw.WriteLine(s12 + "Processor.RestoreInterrupts(iflag);");
        sw.WriteLine(s12 + "");

        if (ad.shortReturnType != "void") {
            sw.WriteLine(s12 + "return retval;");
        }
        else {
            sw.WriteLine(s12 + "return;");
        }

    }

    public static void WriteApAbiStubClassMethodBodyBlank(StreamWriter sw, AbiDef ad)
    {
        string type = GetCsType(ad.shortReturnType, ad.longReturnType);

        // print debug
        sw.WriteLine(s12 + "DebugStub.WriteLine(\"HSG: ** In " +
                     ad.shortMethodName  + "\");");

        // if it's a void, do nothing
        if (type == "void") {
            sw.WriteLine("");
        }
        // it's a pointer
        else if (type.IndexOf("*") != -1) {
            // sw.WriteLine(s12 + GetCsType(ad.shortReturnType, ad.longReturnType) + " x;");
            sw.WriteLine(s12 + "return null;");
        }
        // it's a class
        else if (ad.shortReturnType != ad.longReturnType) {
            sw.WriteLine(s12 + type + " x = new " + type + "();");
            sw.WriteLine(s12 + "return x;");
        }
        // else
        else if (type.IndexOf("bool") != -1) {
            sw.WriteLine(s12 + "return false;");
        }
        else {
             sw.WriteLine(s12 + "return (" +
                          GetCsType(ad.shortReturnType, ad.longReturnType) +
                          ") 0;");
        }
    }



    // Convert C/C++ type into C# type
    // For example convert wchar_t to char
    // This function consults the typeConverter hash table
    public static string GetCsType(string cType, string longVersionType) {

        // first before we convert we check some ambiguities
        string unambiguousType = "";
        CheckAmbiguities(cType, longVersionType, out unambiguousType);
        if (unambiguousType != "") {
            return unambiguousType;
        }

        // Other than that, we will convert the C/C++ type into
        // C# type.
        if (typeConverter[cType] == null) {
            return cType;
        }
        else {
            return (string)typeConverter[cType];
        }
    }

    // This checks ambiguity for BspAbiStub
    // Here is the ambiguity error:
    //   Singularity\BspAbiStub.cs(2202,13): error CS0104:
    //   'ProcessState' is an ambiguous reference
    //   Singularity\BspAbiStub.cs(2249,13): error CS0104:
    //   'ThreadState' is an ambiguous reference
    public static string GetCsTypeForBspAbiStub(string cType, string longVersionType)
    {
        string tmp = GetCsType(cType, longVersionType);
        if (tmp == "ThreadState") {
            return "Microsoft.Singularity.V1.Threads.ThreadState";
        }
        else if (tmp == "ProcessState") {
            return "Microsoft.Singularity.V1.Processes.ProcessState";
        }
        else {
            return tmp;
        }
    }

    // This is all hacks to resolve "ambiguity"
    public static void CheckAmbiguities(string cType, string longVersionType,
                                       out string unambiguousType)
    {

        // Now this is a hack .. for now ..  The problem is when we
        // get the short version of the type we always get the last
        // word after the last "_" For example in:
        // Struct_Microsoft_Singularity_V1_Services_SharedHeapService_Allocation
        // We set the shortType to be "Allocation". But that is not
        // correct because the correct type is actually
        // "SharedHeapService.Allocation"
        if (cType.IndexOf("Allocation") == 0) {
            string str1, str2;
            SeparateLongStructName(longVersionType, out str1, out str2);
            SeparateLongStructName(str1, out str1, out str2);
            unambiguousType = (str2 + "." + cType);
            return;
        }
        unambiguousType = "";
        return;
    }






    ////////////////////////////////////////////////////////////////
    //
    public static void ParseLineToAbiDef(string s, AbiDef abiDef)
    {
        abiDef.abiNum = curAbiNum;
        ParseLine(s,
                  out abiDef.decl,
                  out abiDef.longReturnType,
                  out abiDef.shortReturnType,
                  out abiDef.longMethodName,
                  out abiDef.longClassName,
                  out abiDef.namespaceName,
                  out abiDef.shortClassName,
                  out abiDef.shortMethodName,
                  out abiDef.shortMethodNameWithG,
                  out abiDef.longParamArray,
                  out abiDef.shortParamArray);
    }

    public static void ParseLine(string s,
                                 out string decl,
                                 out string longReturnType,
                                 out string shortReturnType,
                                 out string longMethodName,
                                 out string longClassName,
                                 out string namespaceName,
                                 out string shortClassName,
                                 out string shortMethodName,
                                 out string shortMethodNameWithG,
                                 out string [] longParamArray,
                                 out string [] shortParamArray)
    {
        int i, j, k, pnum;
        string tmpStr, param;

        i = s.IndexOf("static");
        if (i == -1) {
            throw new Exception("line " + lineNumber + " not static");
        }
        i += 7;

        // the whole declaration
        // e.g. "int __fastcall
        //       Struct_Microsoft_Singularity_V1_Services_ProcessService
        //       ::g_HelloProcessABI(int)"
        j = s.IndexOf(')', i);
        decl = s.Substring(i, j + 1 - i);

        // right now we're just working with "decl"
        i = decl.IndexOf("__fastcall");
        if (i == -1) {
            throw new Exception("line " + lineNumber + " not __fastcall");
        }

        // Get the return type
        longReturnType = decl.Substring(0, i-1);

        // Add long return type to structTable
        AddTypeToStructTable(longReturnType);

        // Check if longReturnType is struct type, if so we make
        // the simple type
        // Example:
        //   longReturnType : struct Struct_Micr_Sing_V1_Services_ShrHpServ_Allocation *
        //   shortReturnType: Allocation *
        SeparateLongStructName(longReturnType, out tmpStr, out shortReturnType);

        // now shortReturnType (or any return type) could contain "Stub"
        // The reason for this is when we generate Singularity.V1.lib from
        // Singularity.V1.def, a method M in class StubC could have return type StubC.
        // But that's not what we want, we want a return type of C instead of StubC
        // Here is for example:
        // StubSystemType::StubRootSystemType returns SubSystemType
        // It should actually return SystemType
        // The same thing applies for "param"
        if (shortReturnType.IndexOf("Stub") == 0) {
            shortReturnType = shortReturnType.Substring(4,shortReturnType.Length-4);
        }

        // Right now the string left at index i is:
        // e.g. " Struct_Microsoft_Singularity_V1_Services_ProcessService
        //       ::g_HelloProcessABI(int)"

        // Get the long class name
        i = decl.IndexOf(' ', i) + 1;
        j = decl.IndexOf("::", i);
        k = decl.IndexOf("(", j);

        longClassName = decl.Substring(i, j - i);

        // we have the long class name, add this to the globalClassTable
        globalClassTable[longClassName] = true;


        longMethodName = decl.Substring(i, k - i);
        shortMethodNameWithG = decl.Substring(j + 2, k - (j + 2));

        if (shortMethodNameWithG.IndexOf("g_") != -1) {
            shortMethodName = shortMethodNameWithG.Replace("g_","");
        }
        else if (shortMethodNameWithG.IndexOf("m_") != -1) {
            shortMethodName = shortMethodNameWithG.Replace("m_","");
        }
        else {
            throw new Exception("line " + lineNumber + " method not have g_/m_");
        }

        // Now given the longClassName we want to get the
        // namespaceName and shortClassName
        // Example:
        //   longClassName  : Struct_Microsoft_Singularity_V1_Services_StubProcessService
        //   namespaceName  : Struct_Microsoft_Singularity_V1_Service
        //   shortClassName : StubProcessService
        SeparateLongStructName(longClassName, out namespaceName, out shortClassName);

        // Now we're starting to get the arguments
        longParamArray = GetParamArray();
        shortParamArray = GetParamArray();


        i = decl.IndexOf('(') + 1;
        pnum = 0;
        while (decl[i] != ')') {
            j = decl.IndexOf(',', i);
            if (j == -1) {
                j = decl.IndexOf(')', i);

                param = decl.Substring(i, j - i);
                longParamArray[pnum] = param;
                pnum++;
                break;
            }

            param = decl.Substring(i, j - i);

            longParamArray[pnum] = param;
            pnum++;
            i = j + 1;
        }

        // Add long param array to struct table
        for (int v = 0; v < longParamArray.Length; v++) {
            if (longParamArray[v] != "") {
                AddTypeToStructTable(longParamArray[v]);
            }
        }


        // The params are ready we make shorter param now
        for (int v = 0; v < longParamArray.Length; v++) {
            if (longParamArray[v] != "") {
                SeparateLongStructName(longParamArray[v], out tmpStr, out shortParamArray[v]);

                // fix short param (the same case as in shortReturnType above)
                // this might not be necessary anymore
                //
                //if (shortParamArray[v].IndexOf("Stub") == 0) {
                //  shortParamArray[v] = shortParamArray[v].Substring(4,shortParamArray[v].Length-4);
                //  }  
            }
        }
    }



    ////////////////////////////////////////////////////////////////
    // Option      :
    // Input file  : $(OBJ)/SingularityStub.V1.dumpbin
    // Output file :
    // Note        :
    //
    // Example:
    //
    //
    public static void GenerateMpSyscallsHeader()
    {
        printCount = 0;
        string s;
        AbiDef abiDef;
        while (true) {
            s = Console.ReadLine();
            lineNumber++;

            // end of file
            if (s == null) {
                break;
            }

            // g_ or m_
            if (s.IndexOf("?g_") == -1 && s.IndexOf("?m_") == -1) {
                continue;
            }

            abiDef = new AbiDef();

            ParseLineToAbiDef(s, abiDef);
            // PrintAbiDef(abiDef, "");

            // Now we add abiDef to hashtable
            AddAbiDefToHashTable(abiDef);
        }

        // test
        // PrintNamespaceTable();


        BeginCreatingMpSyscallsHeader();

    }


    public static void BeginCreatingMpSyscallsHeader()
    {
        // go through all the namespace

        AbiDef ad;
        Hashtable nsClassTable, methodTable;

        // header
        Console.WriteLine("////////////////////////////////////////////////////////////");
        Console.WriteLine("// Automatically generated files by MpSyscallsBuilder.exe");
        Console.WriteLine("// ");

        // First of all create external undefined structs
        foreach (string s in structTable.Keys) {
            if (!globalClassTable.ContainsKey(s)) {
                Console.WriteLine("struct " + s + " {" + structTable[s] + "};");
            }
        }
        Console.WriteLine();

        // Next, create struct declarations
        foreach (string namespaceName in namespaceTable.Keys) {

            nsClassTable = (Hashtable)namespaceTable[namespaceName];

            foreach (string className in nsClassTable.Keys) {

                Console.WriteLine("struct " + namespaceName + "_" + className);
                Console.WriteLine("{");

                methodTable = (Hashtable)nsClassTable[className];

                foreach (string decl in methodTable.Keys) {

                    ad = (AbiDef)methodTable[decl];

                    // A stub, export
                    if (ad.shortMethodName.IndexOf("Stub") == 0) {
                        Console.Write("    static " + ad.longReturnType +
                                      " " + ad.shortMethodNameWithG + "(");
                    }
                    else {
                        Console.Write("    __declspec(dllexport) static " +
                                      ad.longReturnType +
                                      " __fastcall " +
                                      ad.shortMethodNameWithG + "(");
                    }

                    // parameters
                    for (int v = 0; v < ad.longParamArray.Length; v++) {
                        if (ad.longParamArray[v] != "") {

                            if (ad.longParamArray[v] != "void") {
                                if (v == 0) {
                                    Console.Write(ad.longParamArray[v]) ;
                                }
                                else {
                                    Console.Write(", " + ad.longParamArray[v]);
                                }
                            }
                        }
                    }


                    Console.WriteLine(");");


                }


                Console.WriteLine("};");
                Console.WriteLine("");
            }
        }
    }


    ////////////////////////////////////////////////////////////////
    // Option      :
    // Input file  : $(OBJ)/SingularityStub.V1.dumpbin
    // Output file :
    // Note        :
    //
    // Example:
    //
    //
    public static void GenerateMpSyscallsImpl()
    {
        printCount = 0;
        string s;
        AbiDef abiDef;
        while (true) {
            s = Console.ReadLine();
            lineNumber++;

            // end of file
            if (s == null) {
                break;
            }

            // g_ or m_
            if (s.IndexOf("?g_") == -1 && s.IndexOf("?m_") == -1) {
                continue;
            }

            abiDef = new AbiDef();

            ParseLineToAbiDef(s, abiDef);
            // PrintAbiDef(abiDef, "");

            // Now we add abiDef to hashtable
            AddAbiDefToHashTable(abiDef);
        }

        // test
        // PrintNamespaceTable();


        BeginCreatingMpSyscallsImpl();

    }

    // Whenever MpSyscalls.x86 has bigger .rdata area, the kernel is
    // crashing (e.g. got different kind of exceptions during boot) no matter
    // where we allocate MpSyscalls.x86 (either in 0x00500000 or 0x10500000)
    // So we're not generating all implementations. Right now we are just
    // generating GetUtcTime and HelloProcessABI
    // Here is an example of the crash:
    // This is fine:
    //   add 00500000..00500400 pe       .\obj\Prototype.ApicMP.Min.MarkSweep\MpSyscalls.x86
    //   add 00501000..00501200 .text    .\obj\Prototype.ApicMP.Min.MarkSweep\MpSyscalls.x86
    //   add 00502000..00502c00 .rdata   .\obj\Prototype.ApicMP.Min.MarkSweep\MpSyscalls.x86
    // This causes a crash:
    //   add 00500000..00500400 pe       .\obj\Prototype.ApicMP.Min.MarkSweep\MpSyscalls.x86
    //   add 00501000..00501400 .text    .\obj\Prototype.ApicMP.Min.MarkSweep\MpSyscalls.x86
    //   add 00502000..00504200 .rdata   .\obj\Prototype.ApicMP.Min.MarkSweep\MpSyscalls.x86
    public static bool DoesNotCauseKernelCrash(string namespaceName, string className,
                                               string methodName)
    {
        // to test more functions/class/namespace, just add the
        // corresponding conditions
        if (methodName.IndexOf("HelloProcessABI")  != -1 ||
            methodName.IndexOf("TestAbiCallOne")   != -1 ||
            methodName.IndexOf("TestAbiCallTwo")   != -1 ||
            methodName.IndexOf("TestAbiCallThree") != -1 ||
            // methodName.IndexOf("GetUtcTime") != -1 ||
            false)
        {
            return true;
        }
        return false;
    }


    public static void BeginCreatingMpSyscallsImpl()
    {
        // go through all the namespace

        AbiDef ad;
        Hashtable nsClassTable, methodTable;

        // header
        Console.WriteLine("////////////////////////////////////////////////////////////");
        Console.WriteLine("// Automatically generated files by MpSyscallsBuilder.exe");
        Console.WriteLine("// ");

        Console.WriteLine("#include \"MpSyscalls.h\"");
        Console.WriteLine("");
        Console.WriteLine("int entry() { return 0; }");
        Console.WriteLine("");


        // Next, create struct declarations
        foreach (string namespaceName in namespaceTable.Keys) {

            nsClassTable = (Hashtable)namespaceTable[namespaceName];

            foreach (string className in nsClassTable.Keys) {

                methodTable = (Hashtable)nsClassTable[className];

                foreach (string decl in methodTable.Keys) {

                    ad = (AbiDef)methodTable[decl];

                    // we only generate methods that have no "Stub"
                    if (ad.shortMethodName.IndexOf("Stub") != 0) {

                        WriteMpSyscallsImplMethod(ad);
                    }
                }
            }
        }
    }


    public static void WriteMpSyscallsImplMethod(AbiDef ad)
    {
        string cm;
        int ptotal;

        // if cause kernel crash, we just add comment code
        cm = "// ";
        if (DoesNotCauseKernelCrash(ad.namespaceName, ad.shortClassName, ad.shortMethodName)) {
            cm = "";
        }

        // function
        Console.Write(cm + "__declspec(dllexport) " +
                      ad.longReturnType +
                      " __fastcall " +
                      ad.longClassName + "::" +
                      ad.shortMethodNameWithG + "(");

        // parameters
        ptotal = 0;
        for (int v = 0; v < ad.longParamArray.Length; v++) {
            if (ad.longParamArray[v] != "") {

                if (ad.longParamArray[v] != "void") {
                    if (v == 0) {
                        Console.Write(ad.longParamArray[v] + " p" + v) ;
                    }
                    else {
                        Console.Write(", " + ad.longParamArray[v] + " p" + v);
                    }
                    ptotal++;
                }
            }
        }

        Console.WriteLine(")");
        Console.WriteLine(cm + "{");

        // function body
        // We are not supporting EndpointCore right now ..
        if (ad.shortClassName.IndexOf("EndpointCore") != -1) {
            Console.WriteLine(cm + "    __asm { int 3 }");
        }
        else {
            WriteMpSyscallsImplMethodBody(cm, ad, ptotal);
        }

        Console.WriteLine(cm + "}");
        Console.WriteLine("");

    }

    public static void WriteMpSyscallsImplMethodBody(string cm,
                                                     AbiDef ad,
                                                     int ptotal)
    {
        Console.Write(cm + "    ");
        if (ad.longReturnType != "void") {
            Console.Write("return ");
        }
        Console.Write(ad.longClassName + "::" +
                          GetStubMethodName(ad.shortMethodNameWithG) + "(");
        for (int v = 0; v < ptotal; v++) {
            if (v != 0) {
                Console.Write(", ");
            }
            Console.Write("p" + v);
        }

        Console.WriteLine(");");
    }


    // Given g_Method, or m_Method it returns g_StubMethod or m_StubMethod
    public static string GetStubMethodName(string methodNameWithG)
    {
        string tmp1, tmp2;
        int i;
        i = methodNameWithG.IndexOf("_");
        tmp1 = methodNameWithG.Substring(0, i);
        tmp2 = methodNameWithG.Substring(i+1, methodNameWithG.Length-(i+1));

        return (tmp1 + "_Stub" + tmp2);

    }


    ////////////////////////////////////////////////////////////////
    // Option      : genBspAbiStub
    // Input file  : $(OBJ)/SingularityStub.V1.dumpbin
    // Output file : Singularity\BspAbiStub.cs (Find all Stub*.cs files
    // Note        : This create the Stub files which contains the stub functions
    //               that will perform the marshaling and IPI
    // Example:
    //
    //
    public static void GenerateBspAbiStub()
    {
        printCount = 0;
        string s;
        AbiDef abiDef;
        while (true) {
            s = Console.ReadLine();
            lineNumber++;

            // end of file
            if (s == null) {
                break;
            }

            // We only create stub files and functions for abi definition that has
            // g_Stub or m_Stub
            if (s.IndexOf("?g_Stub") == -1 && s.IndexOf("?m_Stub") == -1) {
                continue;
            }

            IncrementAbiNumber(s);

            abiDef = new AbiDef();

            ParseLineToAbiDef(s, abiDef);
            // PrintAbiDef(abiDef, "");

            InsertToSequentialAbiDef(abiDef);


            // Now we add abiDef to hashtable
            AddAbiDefToHashTable(abiDef);
        }

        BeginCreatingBspAbiStubFromNamespaceTable();
    }


    public static void InsertToSequentialAbiDef(AbiDef abiDef)
    {
        sequentialAbiDef[curAbiNum] = abiDef;
    }

    public static void BeginCreatingBspAbiStubFromNamespaceTable()
    {
        WriteBspAbiStubFileHeader();

        WriteBspAbiStubEntry();
        WriteBspAbiStubMethods();
        WriteBspAbiStubFileFooter();
    }

    public static void WriteBspAbiStubFileHeader()
    {
        Console.WriteLine("///////////////////////////////////////////////////////");
        Console.WriteLine("// ");
        Console.WriteLine("// THIS IS AUTOMATICALLY GENERATED FILE, DO NOT MODIFY ");
        Console.WriteLine("// ");
        Console.WriteLine("// Generated by: Windows/MpSyscall/MpSyscallBuilder.exe");
        Console.WriteLine("// ");
        Console.WriteLine("// ");
        Console.WriteLine("");

        Console.WriteLine("using System;");
        Console.WriteLine("using System.Runtime.InteropServices;");
        Console.WriteLine("using System.Runtime.CompilerServices;");
        Console.WriteLine("using System.Threading;");
        Console.WriteLine("using Microsoft.Singularity.Hal;");
        Console.WriteLine("using Microsoft.Singularity.Io;");
        Console.WriteLine("using Microsoft.Singularity.Memory;");
        Console.WriteLine("using Microsoft.Singularity.Scheduling;");
        Console.WriteLine("using Microsoft.Singularity.IX;");
        Console.WriteLine("using Microsoft.Singularity.V1.Processes;");
        Console.WriteLine("using Microsoft.Singularity.V1.Security;");
        Console.WriteLine("using Microsoft.Singularity.V1.Services;");
        Console.WriteLine("using Microsoft.Singularity.V1.Stress;");
        Console.WriteLine("using Microsoft.Singularity.V1.Threads;");
        Console.WriteLine("using Microsoft.Singularity.V1.Types;");
        Console.WriteLine("");
        Console.WriteLine("namespace Microsoft.Singularity");
        Console.WriteLine("{");
        Console.WriteLine("    [CLSCompliant(false)]");
        Console.WriteLine("    public class BspAbiStub");
        Console.WriteLine("    {");
    }

    public static void WriteBspAbiStubFileFooter()
    {
        Console.WriteLine("    }");
        Console.WriteLine("}");
    }

    public static void WriteBspAbiStubEntry()
    {
        AbiDef ad;
        // Console.WriteLine(s8 + "[NoHeapAllocation]");
        Console.WriteLine(s8 + "public static unsafe void ProcessMpCall(int cpu, MpExecution.MpCall mpCall)");
        Console.WriteLine(s8 + "{");
        Console.WriteLine(s12 + "switch (mpCall.abiNum) {");

        for (int i = 0; i < MAX_ABI_DEF; i++) {
            if (sequentialAbiDef[i] != null) {
                ad = sequentialAbiDef[i];
                Console.Write(s12 + "case {0,3}: ", ad.abiNum);
                Console.Write("BspAbiStub" + ad.abiNum + "(cpu, mpCall); ");
                Console.WriteLine("break;");
            }
        }

        Console.WriteLine(s12 + "default:");
        Console.WriteLine(s16 + "DebugStub.WriteLine(\"HSG: **** Unknown abi call number {0}\",");
        Console.WriteLine(s16 + "__arglist(mpCall.abiNum));");
        Console.WriteLine(s16 + "break;");

        Console.WriteLine(s12 + "}");
        Console.WriteLine(s8 + "}");
        Console.WriteLine("");
    }

    public static void WriteBspAbiStubMethods()
    {
        AbiDef ad;
        for (int i = 0; i < MAX_ABI_DEF; i++) {
            if (sequentialAbiDef[i] != null) {
                ad = sequentialAbiDef[i];
                WriteBspAbiStubMethod(ad);
            }
        }
    }

    // Right now, the actual abi is called from Processor.DSI(), hence
    // all the subsequent calls must have "NoHeapAllocate". But when
    // the scheduler comes into play, this requirement is no longer holds.
    // Right now, only Mp ABI functions that have been annotated
    // with NoHeapAllocate
    public static bool MethodIsNoHeapAllocation(string methodName)
    {
        return true;

        // this has been fixed since we have ApThread
        //
        //if (methodName == "HelloProcessABI" ||
        //  methodName == "TestAbiCallOne" ||
        //  methodName == "TestAbiCallTwo" ||
        //  methodName == "TestAbiCallThree" ||
        //  false) {
        //  return true;
        //}
        //return false;  
    }


    public static void WriteBspAbiStubMethod(AbiDef ad)
    {
        int curOffset, size;

        // Console.WriteLine(s8 + "[NoHeapAllocation]");
        Console.WriteLine(s8 + "private static unsafe void BspAbiStub" + ad.abiNum +
                          "(int cpu, MpExecution.MpCall mpCall)");
        Console.WriteLine(s8 + "{");

        Console.WriteLine(s12 + "bool iflag;");

        // parameter declaration
        for (int v = 0; v < ad.shortParamArray.Length; v++) {
            if (ad.shortParamArray[v] != "" && ad.shortParamArray[v] != "void") {
                Console.WriteLine(s12 +
                                  GetCsType(ad.shortParamArray[v], ad.longParamArray[v]) +
                                  " p" + v + ";");
            }
        }

        if (ad.shortReturnType != "void") {
            Console.WriteLine(s12 +
                              GetCsTypeForBspAbiStub(ad.shortReturnType, ad.longReturnType) +
                              " retval;");
        }
        Console.WriteLine("");

        // get args
        Console.WriteLine(s12 + "// get args");
        Console.WriteLine(s12 + "fixed (byte *baseArg = & mpCall.argBuffer[0] ) {");
        curOffset = 0;
        for (int v = 0; v < ad.shortParamArray.Length; v++) {
            if (ad.shortParamArray[v] != "" && ad.shortParamArray[v] != "void") {
                size = GetTypeSize(ad.longParamArray[v]);
                Console.WriteLine(s16 + "    Buffer.MoveMemory((byte*) & p" + v +
                             " , baseArg+" + curOffset + " , " + size + ");");
                curOffset += size;
            }
        }
        Console.WriteLine(s12 + "}");
        Console.WriteLine(s12 + "");


        // Call the actual abi
        Console.WriteLine(s12 + "// call actual abi");

        string actualAbiMethodName =
            ad.shortMethodName.Substring(4, ad.shortMethodName.Length - 4);
        string cm = "// ";
        if (MethodIsNoHeapAllocation(actualAbiMethodName)) {
            cm = "";
        }
        Console.Write(s12 + cm);

        if (ad.shortReturnType != "void") {
            Console.Write("retval = ");
        }

        Console.Write(ad.shortClassName + "." + actualAbiMethodName + "(");
        for (int v = 0; v < ad.shortParamArray.Length; v++) {
            if (ad.shortParamArray[v] != "" && ad.shortParamArray[v] != "void") {
                if (v != 0) {
                    Console.Write(", ");
                }
                Console.Write("p" + v);
            }
        }
        Console.WriteLine(");");
        Console.WriteLine("");

        // copy return value
        if (ad.shortReturnType != "void") {
            Console.WriteLine(s12 + "// copy return value");
            Console.WriteLine(s12 + "fixed (byte *baseRet = & mpCall.retBuffer[0] ) {");
            Console.WriteLine(s16 + "    Buffer.MoveMemory( baseRet , (byte*) & retval , " +
                         GetTypeSize(ad.longReturnType) + ");");
            Console.WriteLine(s12 + "}   ");
            Console.WriteLine(s12 + "");
        }

        // copy arguments back
        Console.WriteLine(s12 + "// copy arguments back");
        Console.WriteLine(s12 + "fixed (byte *baseArg = & mpCall.argBuffer[0] ) {");
        curOffset = 0;
        for (int v = 0; v < ad.shortParamArray.Length; v++) {
            if (ad.shortParamArray[v] != "" && ad.shortParamArray[v] != "void") {
                size = GetTypeSize(ad.longParamArray[v]);
                Console.WriteLine(s16 + "    Buffer.MoveMemory(baseArg+" + curOffset +
                             " , (byte*) & p" + v + " , " + size + ");");
                curOffset += size;
            }
        }
        Console.WriteLine(s12 + "}");
        Console.WriteLine(s12 + "");

        // return
        Console.WriteLine(s12 + "iflag = Processor.DisableInterrupts();");
        Console.WriteLine(s12 + "MpExecution.ReturnMpCall(cpu, mpCall.position);");
        Console.WriteLine(s12 + "Processor.RestoreInterrupts(iflag);");


        Console.WriteLine(s8 + "}");
        Console.WriteLine("");
    }


    ////////////////////////////////////////////////////////////////
    //
    public static void Generate(string[] args)
    {
        genSingStubV1Def = args[0] == "/genSingStubV1Def";
        genApAbiStub = args[0] == "/genApAbiStub";
        genBspAbiStub = args[0] == "/genBspAbiStub";
        genMpSyscallsHeader = args[0] == "/genMpSyscallsHeader";
        genMpSyscallsImpl = args[0] == "/genMpSyscallsImpl";

        bool genlib = args[0] == "/genlib";
        bool deflib = args[0] == "/deflib";
        bool defentry = args[0] == "/defentry";

        if (!genSingStubV1Def && !genApAbiStub &&
            !genMpSyscallsHeader && !genMpSyscallsImpl &&
            !genBspAbiStub) {
            throw new Exception("Invalid args ..");
        }

        if (genSingStubV1Def) {
            GenerateSingularityStubV1Def();
            return;
        }
        if (genApAbiStub) {
            GenerateApAbiStub();
            return;
        }
        if (genMpSyscallsHeader) {
            GenerateMpSyscallsHeader();
            return;
        }
        if (genMpSyscallsImpl) {
            GenerateMpSyscallsImpl();
            return;
        }
        if (genBspAbiStub) {
            GenerateBspAbiStub();
            return;
        }
    }



    // Initialize some tables
    public static void Initialize()
    {
        InitializeTypeConverter();
        InitializeParamTable();

        //
        //if (genBspAbiStub) {
        //  for (int i = 0; i < MAX_ABI_DEF; i++) {
        //      sequentialAbiDef[i] = null;
        //  }
        //  }  
    }

    // Sizes are manually configured
    // In the future this should come from Bartok
    public static void InitializeParamTable()
    {
        paramTable["void"] = 0;
        paramTable["int"] = 4;
        paramTable["unsigned int"] = 4;
        paramTable["unsigned short"] = 4;
        paramTable["unsigned char"] = 4;
        paramTable["wchar_t"] = 4;
        paramTable["bool"] = 4;
        paramTable["__int64"] = 8;
        paramTable["unsigned __int64"] = 8;
        paramTable["struct Struct_System_TimeSpan"] = 8;
        paramTable["struct Struct_System_DateTime"] = 8;
        paramTable["struct Struct_Microsoft_Singularity_V1_Types_SystemType"] = 4;
        paramTable["struct Struct_Microsoft_Singularity_V1_Threads_ThreadState"] = 4;
        paramTable["struct Struct_Microsoft_Singularity_V1_Processes_ProcessState"] = 4;
        paramTable["struct Struct_Microsoft_Singularity_V1_Services_ParameterCode"] = 4;
    }

    // We need this because for example "unsigned int should become uint"
    // Right now we just convert types directly, but there could be some automation
    // e.g. int * means out int
    public static void InitializeTypeConverter()
    {
        typeConverter["__int64"] = "long";
        typeConverter["__int64 *"] = "long*";
        typeConverter["__int64 * *"] = "long**";
        typeConverter["unsigned __int64"] = "ulong";
        typeConverter["unsigned __int64 *"] = "ulong*";
        typeConverter["unsigned __int64 * *"] = "ulong**";
        typeConverter["unsigned int"] = "uint";
        typeConverter["unsigned int *"] = "uint*";
        typeConverter["unsigned int * *"] = "uint**";
        typeConverter["wchar_t"] = "char";
        typeConverter["wchar_t *"] = "char*";
        typeConverter["wchar_t * *"] = "char**";
        typeConverter["unsigned char"] = "byte";
        typeConverter["unsigned char *"] = "byte*";
        typeConverter["unsigned char * *"] = "byte **";
        typeConverter["unsigned char * * *"] = "byte ***";
        typeConverter["unsigned short"] = "ushort";
        typeConverter["unsigned short *"] = "ushort *";
        typeConverter["unsigned short * *"] = "ushort * *";
        typeConverter["struct uintPtr *"] = "UIntPtr";
        typeConverter["struct uintPtr * *"] = "UIntPtr*";
    }

    public static int Main(string[] args)
    {
        try {
            Initialize();
            Generate(args);
        }
        catch (Exception e) {
            Console.Write(e);
            return -1;
        }
        return 0;
    }
}

