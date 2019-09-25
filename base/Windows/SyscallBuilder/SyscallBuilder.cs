// ----------------------------------------------------------------------------
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
// ----------------------------------------------------------------------------

using System;
using System.Collections;

public class SyscallBuilder
{
    static Hashtable classTable = new Hashtable();
    static Hashtable structTable = new Hashtable();
    static Hashtable paramTable = new Hashtable();

    static int lineNumber = 0;

    static void AddType(string t)
    {
        if (t.StartsWith("struct ")) {
            int end = t.IndexOf(" ", 7);
            if (end == -1) {
                end = t.Length;
            }
            string structName = t.Substring(7, end - 7);
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

    public static void Generate(string[] args)
    {
        bool genHdr = args[0] == "/genhdr";
        bool genLib = args[0] == "/genlib";
        bool genEntry = args[0] == "/genentry";
        if (genLib) {
            Console.WriteLine("#include \"syscalls.h\"");
            Console.WriteLine();
        }
        if (genEntry) {
            Console.WriteLine("#include \"syscalls.h\"");
        }
        int n = 1;
        paramTable["void"] = 0;
        paramTable["int"] = 4;
        paramTable["unsigned int"] = 4;
        paramTable["unsigned char"] = 4;
        paramTable["unsigned short"] = 4;
        paramTable["wchar_t"] = 4;
        paramTable["bool"] = 4;
        paramTable["__int64"] = 8;
        paramTable["unsigned __int64"] = 8;
        paramTable["struct Struct_System_TimeSpan"] = 8;
        paramTable["struct Struct_System_DateTime"] = 8;
        paramTable["struct Struct_System_SchedulerTime"] = 8;
        paramTable["struct Struct_Microsoft_Singularity_V1_Types_SystemType"] = 4;
        paramTable["struct Struct_Microsoft_Singularity_V1_Threads_ThreadState"] = 4;
        paramTable["struct Struct_Microsoft_Singularity_V1_Processes_ProcessState"] = 4;
        paramTable["struct Struct_Microsoft_Singularity_V1_Services_ParameterCode"] = 4;

        while (true) {
            string s = Console.ReadLine();
            lineNumber++;
            if (s == null) {
                break;
            }
            if (s.IndexOf('?') == -1) {
                continue;
            }
            if (   s.IndexOf("Struct_Microsoft_Singularity_V1_Services_SharedHeapService::g_GetData") != -1
                || s.IndexOf("Struct_Microsoft_Singularity_V1_Services_SharedHeapService::g_GetSize") != -1
                || s.IndexOf("Struct_Microsoft_Singularity_V1_Types_SystemType::g_IsNull") != -1) {
                continue;
            }

            if (s.IndexOf("(public: ") == -1) {     // Skip non attributed exports
                continue;
            }
            
            s = s.Replace("struct void", "void");
            int i = s.IndexOf("static");
            if (i == -1) {
                throw new Exception("not static");
            }
            i += 7;
            string decl = s.Substring(i, s.IndexOf(')', i) + 1 - i);
            i = s.IndexOf("__fastcall", i);
            if (i == -1) {
                throw new Exception("not fastcall");
            }
            string ret = decl.Substring(0, decl.IndexOf(" __fastcall"));

            try {
                AddType(ret);
            }
            catch {
                Console.WriteLine("Failed at input line {0}\n", lineNumber);
                throw;
            }

            i = s.IndexOf(' ', i) + 1;
            bool isAbi;

            {
                int j = s.IndexOf("::", i);
                int k = s.IndexOf("(", j);
                string className = s.Substring(i, j - i);
                string methodName = s.Substring(i, k - i);
                string methodLocalName = s.Substring(j + 2, k - (j + 2));

                // These two symbols are special and shouldn't have ring3
                // stubs
                isAbi =
                    (!methodLocalName.StartsWith("g_LinkStack")) &&
                    (!methodLocalName.StartsWith("g_UnlinkStack"));

                Hashtable methods = (Hashtable)classTable[className];
                if (methods == null) {
                    methods = new Hashtable();
                    classTable[className] = methods;
                }
                methods[decl] = true;
                string typ = ret + "(*)" + s.Substring(k, s.IndexOf(')', k) + 1 - k);
                if (genEntry && isAbi) {
                    Console.WriteLine("static int f" + n + " = int((" + typ + ")" + methodName + ");");
                }
            }

            i = s.IndexOf('(', i) + 1;
            int smallWords = 0;
            int largeWords = 0;
            while (s[i] != ')') {
                int j = s.IndexOf(',', i);
                if (j == -1) {
                    j = s.IndexOf(')', i);
                }
                string param = s.Substring(i, j - i);
                int size;
                if (param.EndsWith("*") || param.EndsWith("Handle")) {
                    size = 4;
                }
                else {
                    if (!paramTable.ContainsKey(param)) {
                        throw new Exception("unknown parameter type: " + param);
                    }
                    size = (int) paramTable[param];
                }
                //Console.WriteLine(size + ":" + param);
                try {
                    AddType(param);
                }
                catch {
                    Console.WriteLine("Failed at input line {0}\n", lineNumber);
                    throw;
                }
                i = j + 1;
                if (size <= 4) {
                    smallWords++;
                }
                else {
                    largeWords += size / 4;
                }
            }

            int paramRegs = (smallWords < 2) ? (smallWords) : 2;
            int paramSlots = smallWords + largeWords - paramRegs;

            if (genLib && isAbi) {
                Console.WriteLine("__declspec(naked dllexport) " + decl);
                Console.WriteLine("{__asm {");
                Console.WriteLine("    push edx");
                Console.WriteLine("    push ecx");

                Console.WriteLine("    mov ecx, " + n);
                Console.WriteLine("    mov edx, esp");
                Console.WriteLine("    push done");

                Console.WriteLine("    _emit   0x0f;");
                Console.WriteLine("    _emit   0x34;  //sysenter");
                Console.WriteLine("  done:");

                Console.WriteLine("    ret " + 4 * paramSlots);
                Console.WriteLine("}}");
                Console.WriteLine();
            }

            if (genEntry && isAbi) {
                Console.WriteLine("__declspec(naked) static void abi" + n + "() {__asm {");
                for (int j = paramSlots - 1; j >= 0; j--) {
                    Console.WriteLine("    push [eax + " + (12 + j * 4) + "]");
                }
                Console.WriteLine("    mov edx, [eax + 4]");
                Console.WriteLine("    mov ecx, [eax + 0]");
                Console.WriteLine("    call f" + n);
                Console.WriteLine("    ret");
                Console.WriteLine("}}");
            }
            if (isAbi) {
                n++;
            }
        }
        if (genHdr) {
            foreach (string s in structTable.Keys) {
                if (!classTable.ContainsKey(s)) {
                    Console.WriteLine("struct " + s + " {" + structTable[s] + "};");
                }
            }
            Console.WriteLine();
            foreach (string c in classTable.Keys) {
                Console.WriteLine("struct " + c);
                Console.WriteLine("{");
                if (structTable.ContainsKey(c)) {
                    string s = (string) structTable[c];
                    if (s != "") {
                        Console.WriteLine("    " + s);
                    }
                }
                foreach (string m in ((Hashtable)classTable[c]).Keys) {
                    Console.WriteLine("    __declspec(dllexport) static " + m + ";");
                }
                Console.WriteLine("};");
                Console.WriteLine();
            }
        }
        if (genEntry) {
            Console.WriteLine();
            Console.WriteLine("void EnterRing0();");
            Console.WriteLine("int syscallEntryTable[] =");
            Console.WriteLine("{");
            Console.WriteLine("int(EnterRing0)");
            for (int i = 1; i < n; i++) {
                if (i > 0) {
                    Console.WriteLine(",");
                }
                Console.Write("    int(abi" + i + ")");
            }
            Console.WriteLine();
            Console.WriteLine("};");
        }
    }

    public static int Main(string[] args)
    {
        try {
            Generate(args);
        }
        catch (Exception e) {
            Console.Write(e);
            return -1;
        }
        return 0;
    }
}
