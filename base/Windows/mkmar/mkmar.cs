////////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  File:   mkmar.cs
//
//  Make static marshaller.
//
using System;
using System.Collections;
using System.Diagnostics;
using System.IO;
using System.Runtime.InteropServices;
using System.Text;
using System.Xml;

using Bartok.MSIL;
using System.Reflection;

public class mkmar
{
    private static void Usage()
    {
        Console.WriteLine("Usage:\n" +
                          "    mkmar /in:file.cs /out:file.cs [assemblies]\n");
    }

    public static int Main(string[] args)
    {
        ArrayList infiles = new ArrayList();
        StreamWriter outfile = null;
        StreamReader infile = null;

        if (args.Length == 0) {
            Usage();
            return 0;
        }

        for (int i = 0; i < args.Length; i++) {
            string arg = args[i];

            if (arg.Length >= 2 && (arg[0] == '-' || arg[0] == '/')) {
                string name = null;
                string value = null;

                int n = arg.IndexOf(':');

                if (n > -1) {
                    name = arg.Substring(1, n - 1).ToLower();

                    if (n < arg.Length + 1) {
                        value = arg.Substring(n + 1);
                    }
                }
                else {
                    name = arg.Substring(1).ToLower();
                }

                bool badArg = false;

                switch (name) {
                    case "out" :
                        if (value != null) {
                            outfile = new StreamWriter(value);
                        }
                        else {
                            badArg = true;
                        }
                        break;
                    case "in" :
                        if (value != null) {
                            infile = new StreamReader(value);
                        }
                        else {
                            badArg = true;
                        }
                        break;

                    default :
                        badArg = true;
                        break;
                }

                if (badArg) {
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
        if (infile == null) {
            Console.WriteLine("You must specify the input file.");
            Usage();
            return 1;
        }

        if (infiles.Count == 0) {
            Console.WriteLine("You must specify at least one input file.");
            Usage();
            return 1;
        }

        ProcessAssemblies(infiles, infile, outfile);

        return 0;
    }

    private static SortedList used;
    private static MetaDataResolver resolver;
    private static TypeInfo tiObject;
    private static TypeInfo tiString;

    private static void ProcessAssemblies(ArrayList infiles, TextReader tr, TextWriter tw)
    {
        resolver = new MetaDataResolver(infiles,
                                        new ArrayList(),
                                        new DateTime(),
                                        false,
                                        false);

        MetaDataResolver.ResolveCustomAttributes(
            new MetaDataResolver[]{resolver});

        TypeInfo.Add("bool");
        TypeInfo.Add("char");
        TypeInfo.Add("byte");
        TypeInfo.Add("sbyte");
        TypeInfo.Add("ushort");
        TypeInfo.Add("short");
        TypeInfo.Add("uint");
        TypeInfo.Add("int");
        TypeInfo.Add("ulong");
        TypeInfo.Add("long");
        tiObject = TypeInfo.Add("object");
        tiObject.isParent = true;
        tiString = TypeInfo.Add("string");
        tiObject.isRefType = true;

        // We must always support null.
        SortedList spaces = new SortedList();
        tw.WriteLine("#define TRACE_CHEAP_STATE");
        tw.WriteLine("#if !USE_CLR_REMOTING");
        tw.WriteLine("using System;");
        tw.WriteLine("using System.Runtime.Serialization;");
        tw.WriteLine("using Bartok.Marshal;");
        foreach (MetaData metadata in resolver.MetaDataList) {
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                if (IsMarshalType(type) &&
                    type.Namespace != "" &&
                    !spaces.Contains(type.Namespace)) {

                    spaces.Add(type.Namespace, null);
                }
            }
        }
        for (int id = 0; id < spaces.Count; id++) {
            tw.WriteLine("using {0};", spaces.GetKey(id));
        }
        tw.WriteLine();

#if false
        foreach (MetaData metadata in resolver.MetaDataList) {
            Console.WriteLine("{0}", metadata.Name);
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                Console.WriteLine("    {0,4} {1}", type.GetHashCode(), type.FullName);
            }
        }
#endif

        // We first try to get all of the types from serialized fields
        // so we have a Signature.Type.
        foreach (MetaData metadata in resolver.MetaDataList) {
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                if (!IsMarshalType(type)) {
                    continue;
                }
                foreach (MetaDataField field in type.Fields) {
                    if (!IsMarshalField(field)) {
                        continue;
                    }
                    TypeInfo.Add(field.Signature.FieldType, "field");
                }
            }
        }

        // Then we pick up any [Serializable] classes.
        foreach (MetaData metadata in resolver.MetaDataList) {
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                if (IsMarshalType(type)) {
                    TypeInfo.Add(type, "serial");
                }
            }
        }

        // Last we pick up any enclosing classes.
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null) {
                continue;
            }

            if (ti.type != null) {
                MetaDataTypeDefinition md = ti.type;
                if (md.EnclosingClass != null) {
                    MetaDataTypeDefinition type = md.EnclosingClass;
                    TypeInfo.Add(type, "enclose");
                }
            }
        }

        CompleteTypeInfoFields();

        tw.WriteLine("// {0} types.", used.Count);
        tw.WriteLine("//  {0:x8}: null", 0);
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;

            if (ti == null) {
                continue;
            }

            string attrs = "";
            attrs += (ti.type != null) ? "d" : "-";
            attrs += (ti.isUsedInField) ? "f" : "-";
            attrs += (ti.isParent) ? "p" : "-";
            attrs += (ti.isAbstract) ? "a" : "-";
            attrs += (ti.isSealed) ? "s" : "-";
            attrs += (ti.isOverload) ? "o" : "-";
            attrs += (ti.isRefType) ? "r" : "-";
            attrs += (ti.isInterface) ? "i" : "-";
            attrs += (ti.isEnum) ? "e" : "-";
            attrs += (ti.isStruct) ? "s" : "-";
            attrs += (ti.isBuiltIn) ? "b" : "-";
            attrs += (ti.hasArray != null) ? "v" : "-";

            tw.WriteLine("//  {0:x8}: {1,-7} {2} {3,4} {4} {5}",
                         id,
                         ti.reason,
                         attrs,
                         ((ti.type != null) ? ti.type.GetHashCode() : 0),
                         ti.kind,
                         ti.isArray ? ":" + ti.arrayOf.kind : "");
        }
        tw.WriteLine("#endif // !USE_CLR_REMOTING");
        tw.WriteLine();

        string ns = "";
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null) {
                // ignore null.
                continue;
            }

            if (ti.type == null) {
                continue;
            }
            if (ti.isEnclosed) {
                // We pick up the enclosed types with their outer class.
                continue;
            }

            // need to handle nested classes...

            if (ns != ti.type.Namespace) {
                if (ns != "") {
                    tw.WriteLine("}");  //
                    tw.WriteLine();
                }
                ns = ti.type.Namespace;
                tw.WriteLine("namespace {0} {{", ns);
            }

            DoClass(ti, tw);
        }

        if (ns != "") {
            tw.WriteLine("}");  //
            tw.WriteLine();
        }

        tw.WriteLine(new String('/', 78));
        tw.WriteLine("//");
        tw.WriteLine("namespace Bartok.Marshal {");
        tw.WriteLine("#if !USE_CLR_REMOTING");
        tw.WriteLine("    public delegate void CheapWriteDelegate(CheapState __cs, Object __ob);");
        tw.WriteLine("    public delegate object CheapReadDelegate(uint __id, CheapState __cs);");
        tw.WriteLine("#endif // !USE_CLR_REMOTING");
        tw.WriteLine();
        tw.WriteLine("    public class CheapState {");
        tw.WriteLine("#if !USE_CLR_REMOTING");
        tw.WriteLine("        public enum Types {");
        tw.WriteLine("            {0,-23} = 0x{1:x8},", "Null", 0);
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null) {
                continue;
            }
            if (ti.isBuiltIn) {
                if (ti.isArray) {
                    tw.WriteLine("            {0,-23} = 0x{1:x8},",
                                 ToEnumName(ti.arrayOf.kind + "Array"),
                                 id);
                }
                else {
                    tw.WriteLine("            {0,-23} = 0x{1:x8},",
                                 ToEnumName(ti.kind),
                                 id);
                }
            }
        }
        tw.WriteLine("        };");
        tw.WriteLine();
        for (string line; (line = tr.ReadLine()) != null;) {
            tw.WriteLine(line);
        }
        tw.WriteLine("#endif //!USE_CLR_REMOTING");
        tw.WriteLine("    }");
        tw.WriteLine("}");
        tw.WriteLine();

        tw.WriteLine("namespace Bartok.Marshal {");
        tw.WriteLine("    public class CheapMarshal {");
        tw.WriteLine("        public static int Main()");
        tw.WriteLine("        {");
        tw.WriteLine("            Console.WriteLine(\"Testing\");");
        tw.WriteLine("            CheapState cs = new CheapState(0);");
        tw.WriteLine("            Test(cs);");
        tw.WriteLine("            return 0;");
        tw.WriteLine("        }");
        tw.WriteLine();

        tw.WriteLine("        static CheapMarshal() {");
        tw.WriteLine("#if !USE_CLR_REMOTING");
        tw.WriteLine("            System.Collections.Hashtable writeHash = new System.Collections.Hashtable({0});",
                     used.Count + 1);
        tw.WriteLine("            System.Collections.Hashtable readHash = new System.Collections.Hashtable({0});",
                     used.Count + 1);
        tw.WriteLine();
        tw.WriteLine("            CheapState.writeHash = writeHash;");
        tw.WriteLine("            CheapState.readHash = readHash;");
        tw.WriteLine();

        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null) {
                continue;
            }

            if (ti.kind == "object" || ti.isInterface) {
                tw.WriteLine("            // dropping {0} as interface.", ti.kind);
                continue;
            }
            if (ti.isArray) {
                tw.WriteLine("            // dropping {0} as array.", ti.kind);
                continue;
            }
            if (ti.isEnum) {
                tw.WriteLine("            // dropping {0} as enum.", ti.kind);
                continue;
            }
            if (ti.isAbstract && ti.children == null) {
                tw.WriteLine("            // dropping {0} as abstract without children.",
                             ti.kind);
                continue;
            }
            if (ti.isBuiltIn) {
                // for now we just drop theses.
                tw.WriteLine("            // dropping {0} as builtin.", ti.kind);
                continue;
            }

            tw.WriteLine("            writeHash.Add(typeof({0}),", ti.kind);
            tw.WriteLine("                          new CheapWriteDelegate({1}.CheapWriteItem));",
                         ti.kind, ti.kind);
            if (!ti.isAbstract) {
                tw.WriteLine("            readHash.Add((uint)0x{0:x8},", ti.id);
                tw.WriteLine("                          new CheapReadDelegate({1}.CheapReadItem));",
                             ti.kind, ti.kind);
            }
            else {
                tw.WriteLine("            // dropping read.{0} as abstract.", ti.kind);
            }

            if (ti.hasArray != null) {
                tw.WriteLine("            writeHash.Add(typeof({0}),", ti.hasArray.kind);
                tw.WriteLine("                          new CheapWriteDelegate({1}.CheapWriteArray));",
                             ti.hasArray.kind, ti.kind);
                tw.WriteLine("            readHash.Add((uint)0x{0:x8},", ti.hasArray.id);
                tw.WriteLine("                          new CheapReadDelegate({1}.CheapReadArray));",
                             ti.hasArray.kind, ti.kind);
            }
        }
        tw.WriteLine("#endif // !USE_CLR_REMOTING");
        tw.WriteLine("        }");

        //////////////////////////////////////////////////////////////////////
        //
        tw.WriteLine("        public static void Test(CheapState __cw) {");
        tw.WriteLine("            CheapState __cr = new CheapState(__cw);");
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;

            if (ti == null) {
                // We ignore null here.
                continue;
            }

            if (!ti.isBuiltIn || ti.isRefType) {
                continue;
            }

            if (ti.kind == "bool" || ti.kind == "char") {
                continue;
            }
            tw.WriteLine("            {");
            tw.WriteLine("                __cw.Trace(\"Testing {0}\");", ti.kind);
            tw.WriteLine("                {0} value = 0x77;", ti.kind);
            tw.WriteLine("                __cw.WriteOpen();");
            tw.WriteLine("                __cw.Write(value);");
            tw.WriteLine("                __cw.WriteClose();");
            tw.WriteLine("                __cw.Trace();");
            tw.WriteLine("                __cr.ReadOpen();");
            tw.WriteLine("                __cr.Read(out value);");
            tw.WriteLine("                __cr.ReadClose();");
            tw.WriteLine("                __cr.Trace();");
            tw.WriteLine("                Console.WriteLine(\"Testing {0}\");", ti.kind);
            tw.WriteLine("            }");
            continue;
        }

        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;

            if (ti == null) {
                // We ignore null here.
                continue;
            }

            if (ti.isInterface || ti.isAbstract) {
                continue;
            }

            if (ti.isBuiltIn || ti.isArray || !ti.isRefType) {
                // Base types are handled manually.
                continue;
            }

            tw.WriteLine("            {");
            tw.WriteLine("                __cw.Trace(\"Testing {0}\");", ti.kind);
            tw.WriteLine("                {0} value = new {0}();", ti.kind);
            tw.WriteLine("                __cw.WriteOpen();");
            tw.WriteLine("                {0}.CheapWrite(__cw, value);", ti.kind);
            tw.WriteLine("                __cw.WriteClose();");
            tw.WriteLine("                __cw.Trace();");
            tw.WriteLine("                __cr.ReadOpen();");
            tw.WriteLine("                {0}.CheapRead(__cr, out value);", ti.kind);
            tw.WriteLine("                __cr.ReadClose();");
            tw.WriteLine("                __cr.Trace();");
            tw.WriteLine("                Console.WriteLine(\"Testing {0}\");", ti.kind);
            tw.WriteLine("            }");
        }

        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;

            if (ti == null) {
                // We ignore null here.
                continue;
            }

            if (ti.isInterface || ti.isAbstract) {
                continue;
            }

            if (ti.isBuiltIn || ti.isArray || !ti.isRefType) {
                // Base types are handled manually.
                continue;
            }

            tw.WriteLine("            {");
            tw.WriteLine("                __cw.Trace(\"Testing {0}\");", ti.kind);
            tw.WriteLine("                {0} value = new {0}();", ti.kind);
            if (ti.fields != null) {
                foreach (FieldInfo fi in ti.fields) {
                    fi.WriteTestInit(tw);

                }
            }
            tw.WriteLine("                __cw.WriteOpen();");
            tw.WriteLine("                {0}.CheapWrite(__cw, value);", ti.kind);
            tw.WriteLine("                __cw.WriteClose();");
            tw.WriteLine("                __cw.Trace();");
            tw.WriteLine("                __cr.ReadOpen();");
            tw.WriteLine("                {0}.CheapRead(__cr, out value);", ti.kind);
            tw.WriteLine("                __cr.ReadClose();");
            tw.WriteLine("                __cr.Trace();");
            tw.WriteLine("                Console.WriteLine(\"Testing {0}\");", ti.kind);
            tw.WriteLine("            }");
        }

        tw.WriteLine("            {");
        tw.WriteLine("                __cw.Trace(\"Testing Linked List\");");
        tw.WriteLine("                NullType[] nt = new NullType[4];");
        tw.WriteLine("                for (int i = 0; i < nt.Length; i++) {");
        tw.WriteLine("                    nt[i] = new NullType();");
        tw.WriteLine("                    nt[i].name = \"nt[\" + i.ToString() + \"]\";");
        tw.WriteLine("                    nt[i].hashCode = i;");
        tw.WriteLine("                }");
        tw.WriteLine("                for (int i = 0; i < nt.Length - 1; i++) {");
        tw.WriteLine("                    nt[i].backEndRep = nt[i+1];");
        tw.WriteLine("                }");
        tw.WriteLine("                for (int i = 1; i < nt.Length; i++) {");
        tw.WriteLine("                    nt[i].backEndMangledName = nt[i-1];");
        tw.WriteLine("                }");
        tw.WriteLine("                ");
        tw.WriteLine("                __cw.WriteOpen();");
        tw.WriteLine("                NullType.CheapWrite(__cw, nt[0]);");
        tw.WriteLine("                __cw.WriteClose();");
        tw.WriteLine("                __cw.Trace();");
        tw.WriteLine("                NullType value = null;");
        tw.WriteLine("                __cr.ReadOpen();");
        tw.WriteLine("                NullType.CheapRead(__cr, out value);");
        tw.WriteLine("                __cr.ReadClose();");
        tw.WriteLine("                __cr.Trace();");
        tw.WriteLine("                for (int i = 0; value != null; i++) {");
        tw.WriteLine("                    __cr.Trace(\"{0,2}: {1,-10} : {2,2} : {3} {4}\",");
        tw.WriteLine("                        i, value.name, value.hashCode,");
        tw.WriteLine("                        value.backEndRep != null ? ((NullType)value.backEndRep).name : \"<null>\",");
        tw.WriteLine("                        value.backEndMangledName != null ? ((NullType)value.backEndMangledName).name : \"<null>\");");
        tw.WriteLine("                    value = (NullType)value.backEndRep;");
        tw.WriteLine("                }");
        tw.WriteLine("                __cr.Trace();");
        tw.WriteLine("                Console.WriteLine(\"Testing Linked List\");");
        tw.WriteLine("            }");

        tw.WriteLine("        }");  // end of Test() method.
        tw.WriteLine("    }");      // end of CheapMarshal class.
        tw.WriteLine("}");          // end of Bartok.Marshal namespace.
        tw.Flush();
    }

    private static string ToEnumName(string name)
    {
        int pos = name.LastIndexOf('.');
        if (pos >= 0) {
            return Char.ToUpper(name[pos + 1]) + name.Substring(pos + 2);
        }
        return Char.ToUpper(name[0]) + name.Substring(1);
    }

    private static void DoClass(TypeInfo ti, TextWriter tw)
    {
        int id = ti.id;
        MetaDataTypeDefinition type = ti.type;

        if (ti.isEnum) {
            tw.WriteLine("    public enum {0} {{ // {1}",
                         type.Name,
                         type.FullName);
            tw.WriteLine("        VALUE = 0,");
            tw.WriteLine("    }");
            return;
        }

        if (ti.isOverload) {
            tw.WriteLine("    // is child class");
        }
        if (ti.isParent) {
            tw.WriteLine("    // is parent class");
            foreach (TypeInfo ci in ti.children) {
                tw.WriteLine("    //      child {0}", ci.kind);
            }
            foreach (TypeInfo ci in ti.descendants) {
                tw.WriteLine("    //      des   {0}", ci.kind);
            }
        }

        if (ti.isStruct) {
            tw.WriteLine("    public struct {0} {{ // {1}",
                         type.Name,
                         type.FullName);
        }
        else if (ti.isInterface) {
            if (ti.isOverload) {
                // else if (type.Extends != null && type.Extends.FullName != "System.Object")
                tw.WriteLine("    public interface {0} : {1} {{ // {2}",
                             type.Name,
                             type.Extends.FullName,
                             type.FullName);
            }
            else {
                tw.WriteLine("    public interface {0} {{ // {1}",
                             type.Name,
                             type.FullName);
            }
            tw.WriteLine("    }");
            tw.WriteLine();
            return;
        }
        else {
            if (ti.isOverload) {
                // else if (type.Extends != null && type.Extends.FullName != "System.Object")
                tw.WriteLine("    public {0}class {1} : {2} {{ // {3}",
                             ti.isAbstract ? "abstract " : "",
                             type.Name,
                             type.Extends.FullName,
                             type.FullName);
            }
            else {
                tw.WriteLine("    public {0}class {1} : Object {{ // {2}",
                             ti.isAbstract ? "abstract " : "",
                             type.Name,
                             type.FullName);
            }
        }

        string vlabel = "";
        if (ti.isOverload) {
            vlabel = "override ";
        }
        else if (ti.isParent) {
            vlabel = "virtual ";
        }

        FieldInfo[] fields = ti.fields;

        //////////////////////////////////////// Null Constructor for Testing.
        //
        if (!ti.isStruct && !ti.isAbstract) {
            tw.WriteLine("        // For Testing.");
            tw.WriteLine("        public {0}() {{", type.Name);
            tw.WriteLine("        }");
        }
        tw.WriteLine("        // For Testing.");
        for (int i = 0; i < fields.Length; i++) {
            tw.WriteLine("        public {0} {1};",
                         fields[i].Type.kind, fields[i].Name);
        }
        tw.WriteLine();

        //////////////////////////////////////////////////////////// Core Constructor.
        //
        if (ti.isAbstract && ti.children == null) {
            // Abort early since class exists only to hold inner types...
            if (ti.inner != null) {
                tw.WriteLine();
                foreach (TypeInfo inner in ti.inner) {
                    DoClass(inner, tw);
                }
            }
            tw.WriteLine("    }");
            tw.WriteLine();
            return;
        }

        tw.WriteLine("#if !USE_CLR_REMOTING");
        if (ti.isAbstract) {
            tw.WriteLine("        public {0}() {{", type.Name);
            tw.WriteLine("        }");
            tw.WriteLine();
        }

        if (ti.isOverload) {
            tw.WriteLine("        private {0}(uint __id, CheapState __cs)",
                         type.Name);
            tw.WriteLine("            : base(__cs) {");
        }
        else {
            tw.WriteLine("        private {0}(uint __id, CheapState __cs) {{", type.Name);
        }
        tw.WriteLine("            if (__id != 0x{0:x8}) {{", ti.id);
        tw.WriteLine("                throw new Exception(\"__id != Type(0x{0:x8}) for {1}\");", ti.id, type.FullName);
        tw.WriteLine("            }");
        if (!ti.isOverload && !ti.isStruct) {
            tw.WriteLine("            __cs.AddPtr(this, 0x{0:x8});", ti.id);
        }

        bool hadEv = false;
        bool hadOb = false;
        for (int i = 0; i < fields.Length; i++) {
            TypeInfo fi = fields[i].Type;
            if (fi.isInterface) {
                if (!hadOb) {
                    tw.WriteLine("            object __ob;");
                    hadOb = true;
                }
                tw.WriteLine("            __cs.Read(out __ob);");
                tw.WriteLine("            {0} = ({1})__ob;",
                             fields[i].Name, fi.kind);
            }
            else if (fi.isArray) {
                if (fi.arrayOf.type != null) {
                    tw.WriteLine("            {0}.CheapRead(__cs, out {1}); // {2}",
                                 fi.arrayOf.kind,
                                 fields[i].Name,
                                 fi.kind);
                }
                else {
                    tw.WriteLine("            __cs.Read(out {0}); // {1}",
                                 fields[i].Name, fi.kind);
                }
            }
            else if (fi.isEnum) {
                if (!hadEv) {
                    tw.WriteLine("            uint __ev;");
                    hadEv = true;
                }
                tw.WriteLine("            __cs.Read(out __ev); // {0}", fi.kind);
                tw.WriteLine("            {0} = unchecked(({1})__ev);",
                             fields[i].Name, fi.kind);
            }
            else if (fi.type != null) {
                tw.WriteLine("            {0}.CheapRead(__cs, out {1});",
                             fi.kind,
                             fields[i].Name);
            }
            else {
                // It is a builtin.
                tw.WriteLine("            __cs.Read(out {0}); // {1}",
                             fields[i].Name, fi.kind);
            }
        }
        tw.WriteLine("            __cs.ReadTypeEnd(0x{0:x8});", ti.id);
        tw.WriteLine("        }");
        tw.WriteLine();

        //////////////////////////////////////////////////////////////////////
        //
        if (!ti.isStruct) {
            tw.WriteLine("        {0}{1}(CheapState __cs)",
                         ti.isSealed ? "private " : "protected ",
                         type.Name);
            tw.WriteLine("            : this(__cs.ReadType(0x{0:x8}), __cs) {{", ti.id);
            tw.WriteLine("        }");
            tw.WriteLine();
        }

        if (ti.isStruct) {
            tw.WriteLine("        private void CheapWrite(CheapState __cs) {");
        }
        else {
            tw.WriteLine("        {0}{1}void CheapWrite(CheapState __cs) {{",
                         (ti.isSealed && !ti.isOverload) ? "private " : "protected ",
                         vlabel);
        }
        tw.WriteLine("            __cs.WriteType(0x{0:x8}); ", ti.id);
        if (ti.isOverload) {
            tw.WriteLine("            base.CheapWrite(__cs);");
        }
        for (int i = 0; i < fields.Length; i++) {
            TypeInfo fi = fields[i].Type;
            if (fi.isInterface) {
                tw.WriteLine("            __cs.Write((object){0}); // {1}",
                             fields[i].Name, fi.kind);
            }
            else if (fi.isArray) {
                if (fi.arrayOf.type != null) {
                    tw.WriteLine("            {0}.CheapWrite(__cs, {1}); // {2}",
                                 fi.arrayOf.kind,
                                 fields[i].Name,
                                 fi.kind);
                }
                else {
                    tw.WriteLine("            __cs.Write({0}); // {1}",
                                 fields[i].Name, fi.kind);
                }
            }
            else if (fi.isEnum) {
                tw.WriteLine("            __cs.Write(unchecked((uint){0})); // {1}",
                             fields[i].Name, fi.kind);
            }
            else if (fi.type != null) {
                tw.WriteLine("            {0}.CheapWrite(__cs, {1}); // {2}",
                             fi.kind,
                             fields[i].Name,
                             fi.kind);
            }
            else {
                // It is a builtin.
                tw.WriteLine("            __cs.Write({0}); // {1}",
                             fields[i].Name, fi.kind);
            }
        }
        tw.WriteLine("            __cs.WriteTypeEnd(0x{0:x8}); ", ti.id);
        tw.WriteLine("        }");
        tw.WriteLine();

        tw.WriteLine("        public static {0}void CheapWriteItem(CheapState __cs, Object __ob) {{",
                     ti.isOverload ? "new " : "");
        tw.WriteLine("            CheapWrite(__cs, ({0})__ob);", type.Name);
        tw.WriteLine("        }");
        tw.WriteLine();

        if (!ti.isAbstract) {
            tw.WriteLine("        public static {0}Object CheapReadItem(uint __id, CheapState __cs) {{",
                         (ti.isOverload && !ti.ParentsAreAllAbstract()) ? "new " : "");
            tw.WriteLine("            if ((__id & 0x8000) != 0) {");
            tw.WriteLine("                return __cs.LoadPtr(__id);");
            tw.WriteLine("            }");
            if (!ti.isRefType) {
                tw.WriteLine("            object __ob = new {0}(__id, __cs);", type.Name);
                tw.WriteLine("            __cs.AddPtr(__ob, __id);");
                tw.WriteLine("            return __ob;");
            }
            else {
                tw.WriteLine("            return new {0}(__id, __cs);", type.Name);
            }
            tw.WriteLine("        }");
            tw.WriteLine();
        }

        tw.WriteLine("        public static void CheapWrite(CheapState __cs, {0} value) {{",
                     type.Name);
        tw.WriteLine("            __cs.Trace(\"Write {0} [outer]\");", type.Name);
        if (ti.isRefType) {
            tw.WriteLine("            if (value == null) {");
            tw.WriteLine("                __cs.WriteType(0);");
            tw.WriteLine("            }");
            tw.WriteLine("            else if (__cs.SavePtr(0x{0:x8}, value)) {{", ti.id);
            tw.WriteLine("                value.CheapWrite(__cs); ");
            tw.WriteLine("            }");
        }
        else {
            tw.WriteLine("            value.CheapWrite(__cs); ");
        }
        tw.WriteLine("        }");
        tw.WriteLine();

        tw.WriteLine("        public static void CheapRead(CheapState __cs, out {0} value) {{",
                     type.Name);
        tw.WriteLine("            __cs.Trace(\"Read {0} [outer]\");", type.Name);
        if (ti.isParent) {
            // Parent ref type.
            tw.WriteLine("             object __ob;");
            tw.WriteLine("            __cs.Read(out __ob);");
            tw.WriteLine("            value = __ob as {0};", type.Name);
        }
        else if (ti.isRefType) {
            // Leaf ref type.
            tw.WriteLine("            uint __id = __cs.ReadTypeOrNull(0x{0:x8});", ti.id);
            tw.WriteLine("            if (__id == 0) {");
            tw.WriteLine("                value = null;");
            tw.WriteLine("            }");
            tw.WriteLine("            else {");
            tw.WriteLine("                value = ({0})CheapReadItem(__id, __cs);", type.Name);
            tw.WriteLine("            }");
        }
        else {
            // Value type.
            tw.WriteLine("            uint __id = __cs.ReadType(0x{0:x8});", ti.id);
            tw.WriteLine("            value = new {0}(__id, __cs);", type.Name);
            tw.WriteLine("            __cs.AddPtr(value, __id);");

        }
        tw.WriteLine("        }");

        if (ti.hasArray != null) {
            string alabel = "";
            if (ti.isOverload && ti.parent.hasArray != null) {
                alabel = "new ";
            }

            tw.WriteLine();
            tw.WriteLine("        public static {0}void CheapWriteArray(CheapState __cs, Object __ob) {{", alabel);
            tw.WriteLine("            CheapWrite(__cs, ({0}[])__ob);", type.Name);
            tw.WriteLine("        }");
            tw.WriteLine();

            tw.WriteLine("        public static void CheapWrite(CheapState __cs, {0}[] value) {{", type.Name);
            tw.WriteLine("            __cs.Trace(\"Write {0}[]\");", ti.kind);
            tw.WriteLine("            if (value == null) {");
            tw.WriteLine("                __cs.WriteType(0);");
            tw.WriteLine("            }");
            tw.WriteLine("            else if (__cs.SavePtr(0x{0:x8}, value)) {{", ti.hasArray.id);
            tw.WriteLine("                __cs.WriteType(0x{0:x8});", ti.hasArray.id);
            tw.WriteLine("                __cs.WriteRaw((uint)value.Length);");
            tw.WriteLine("                for (int i = 0; i < value.Length; i++) {");
            tw.WriteLine("                    CheapWrite(__cs, value[i]);");
            tw.WriteLine("                }");
            tw.WriteLine("                __cs.WriteTypeEnd(0x{0:x8});", ti.hasArray.id);
            tw.WriteLine("            }");
            tw.WriteLine("        }");
            tw.WriteLine();

            tw.WriteLine("        public static void CheapRead(CheapState __cs, out {0}[] value) {{",
                         type.Name);
            tw.WriteLine("            __cs.Trace(\"Read {0}[] [outer]\");", ti.kind);
            tw.WriteLine("            uint __id = __cs.ReadTypeOrNull(0x{0:x8});", ti.hasArray.id);
            tw.WriteLine("            value = CheapReadArrayBody(__id, __cs);");
            tw.WriteLine("        }");
            tw.WriteLine();

            tw.WriteLine("        public static {0}Object CheapReadArray(uint __id, CheapState __cs) {{", alabel);
            tw.WriteLine("            return (Object)CheapReadArrayBody(__id, __cs);");
            tw.WriteLine("        }");
            tw.WriteLine();

            tw.WriteLine("        private static {0}[] CheapReadArrayBody(uint __id, CheapState __cs) {{",
                         type.Name);
            tw.WriteLine("            __cs.Trace(\"Read {0}[] [inner]\");", ti.kind);
            tw.WriteLine("            if (__id == 0) {");
            tw.WriteLine("                return null;");
            tw.WriteLine("            }");
            tw.WriteLine("            else if ((__id & 0x8000) != 0) {");
            tw.WriteLine("                if (__id != 0x{0:x8}) {{", ti.hasArray.id | 0x8000);
            tw.WriteLine("                    throw new Exception(\"__id != Type(0x{0:x8}) for {1}[]\");", ti.hasArray.id | 0x8000, ti.kind);
            tw.WriteLine("                }");
            tw.WriteLine("                return ({0}[])__cs.LoadPtr(__id);", type.Name);
            tw.WriteLine("            }");
            tw.WriteLine("            else {");
            tw.WriteLine("                if (__id != 0x{0:x8}) {{", ti.hasArray.id);
            tw.WriteLine("                    throw new Exception(\"__id != Type(0x{0:x8}) for {1}[]\");", ti.hasArray.id, ti.kind);
            tw.WriteLine("                }");
            tw.WriteLine("                uint len;");
            tw.WriteLine("                __cs.ReadRaw(out len);");
            tw.WriteLine("                {0}[] value = new {1} [len];", type.Name, type.Name);
            tw.WriteLine("                __cs.AddPtr(value, 0x{0:x8});", ti.hasArray.id);
            tw.WriteLine("                for (int i = 0; i < len; i++) {");
            tw.WriteLine("                    CheapRead(__cs, out value[i]);");
            tw.WriteLine("                }");
            tw.WriteLine("                __cs.ReadTypeEnd(0x{0:x8});", ti.hasArray.id);
            tw.WriteLine("                return value;");
            tw.WriteLine("            }");
            tw.WriteLine("        }");
        }
        tw.WriteLine("#endif // !USE_CLR_REMOTING");
        tw.WriteLine();

        if (ti.inner != null) {
            tw.WriteLine();
            foreach (TypeInfo inner in ti.inner) {
                DoClass(inner, tw);
            }
        }
        tw.WriteLine("    }");
        tw.WriteLine();
    }

    private static bool IsMarshalType(MetaDataTypeDefinition type)
    {
        uint flags = (uint)type.Flags & 0xfffffff8;

        if ((type.Flags & TypeAttributes.Serializable) == 0) {
            // We're only looking for serializable types.
            return false;
        }
        if ((type.Flags & TypeAttributes.Interface) != 0) {
            // Skip interfaces.
            return false;
        }
        if ((type.Flags & TypeAttributes.Class) != 0) {
            // We're only looking for classes.
            // return false; // Currently unreachable
        }

        if (type.Name == "CheapState" ||
            type.Name == "ObjectIDGenerator") {
            // we drop some specific classes.
            return false;
        }

        return true;
    }

    private static bool IsMarshalField(MetaDataField field)
    {
        uint flags = (uint)field.Flags & 0xfff8;
        if (TestAndClear(ref flags, (uint)MetaDataField.FieldAttributes.NotSerialized)) {
            // We skip over NonSerialized fields.
            return false;
        }
        if (TestAndClear(ref flags, (uint)MetaDataField.FieldAttributes.Static)) {
            // We skip static.
            return false;
        }
        if (TestAndClear(ref flags, (uint)MetaDataField.FieldAttributes.InitOnly)) {
            return true;
#if false
            // We skip readonly.
            return false;
#endif
        }
        if (TestAndClear(ref flags, (uint)MetaDataField.FieldAttributes.Literal)) {
            // We skip const.
            return false;
        }
        return true;
    }

    private static string ClassToString(MetaDataObject mdo)
    {
        if (mdo is MetaDataTypeDefinition) {
            return ((MetaDataTypeDefinition) mdo).FullName;
        }
        else if (mdo is MetaDataTypeReference) {
            return ((MetaDataTypeReference) mdo).FullName;
        }
        else if (mdo == null) {
            return "<null>";
        }
        else {
            throw new Exception("unknown type: " + mdo.GetType());
        }
    }

    private static string TypeToString(Signature.Type type)
    {
        switch (type.ElementType) {
            case ElementTypes.VOID:
                return "void";
            case ElementTypes.BOOLEAN:
                return "bool";
            case ElementTypes.CHAR:
                return "char";
            case ElementTypes.I1:
                return "sbyte";
            case ElementTypes.U1:
                return "byte";
            case ElementTypes.I2:
                return "short";
            case ElementTypes.U2:
                return "ushort";
            case ElementTypes.I4:
                return "int";
            case ElementTypes.U4:
                return "uint";
            case ElementTypes.I8:
                return "long";
            case ElementTypes.U8:
                return "ulong";
            case ElementTypes.R4:
                return "float";
            case ElementTypes.R8:
                return "double";
            case ElementTypes.STRING:
                return "string";
                //case ElementTypes.PTR:
                //case ElementTypes.BYREF:
            case ElementTypes.VALUETYPE:
                return ClassToString(type.ClassObject);
            case ElementTypes.CLASS:
                return ClassToString(type.ClassObject);
                //case ElementTypes.VAR:
                //case ElementTypes.ARRAY:
                //case ElementTypes.GENERICINST:
                //case ElementTypes.TYPEDBYREF:
            case ElementTypes.I:
                return "IntPtr";
            case ElementTypes.U:
                return "UIntPtr";
                //case ElementTypes.FNPTR:
            case ElementTypes.OBJECT:
                return "object";
            case ElementTypes.SZARRAY:
                return TypeToString(type.TypeObject) + "[]";
                //case ElementTypes.MVAR:
                //case ElementTypes.CMOD_REQD:
                //case ElementTypes.CMOD_OPT:
                //case ElementTypes.INTERNAL:
            default:
                throw new Exception("Unknown Field type");
        }
    }

    private static bool TestAndClear(ref uint flags, uint bit)
    {
        if ((flags & bit) != 0) {
            // Console.WriteLine("                    [{0:x4} had {1:x4}]", flags, bit);
            flags &= ~bit;
            return true;
        }
        return false;
    }

    private class FieldInfo
    {
        public readonly String      Name;
        public readonly TypeInfo    Type;

        public FieldInfo(String name, TypeInfo type)
        {
            this.Name = name;
            this.Type = type;
        }

        public void WriteTestInit(TextWriter tw)
        {
            if (Type.kind == "bool") {
                tw.WriteLine("                value.{0} = true;", Name);
                return;
            }
            if (Type.kind == "char") {
                tw.WriteLine("                value.{0} = 'A';", Name);
                return;
            }
            if (Type.kind == "sbyte") {
                tw.WriteLine("                value.{0} = 0x76;", Name);
                return;
            }
            if (Type.kind == "byte") {
                tw.WriteLine("                value.{0} = 0xfe;", Name);
                return;
            }
            if (Type.kind == "short") {
                tw.WriteLine("                value.{0} = 0x7654;", Name);
                return;
            }
            if (Type.kind == "ushort") {
                tw.WriteLine("                value.{0} = 0xfedc;", Name);
                return;
            }
            if (Type.kind == "int") {
                tw.WriteLine("                value.{0} = 0x76543210;", Name);
                return;
            }
            if (Type.kind == "uint") {
                tw.WriteLine("                value.{0} = 0xfedcba98;", Name);
                return;
            }
            if (Type.kind == "long") {
                tw.WriteLine("                value.{0} = 0x7654321001234567;", Name);
                return;
            }
            if (Type.kind == "ulong") {
                tw.WriteLine("                value.{0} = 0xfedcba9876543210;", Name);
                return;
            }
            if (Type.kind == "string") {
                tw.WriteLine("                value.{0} = \"Hello {1}!\";", Name, Name);
                return;
            }
            if (Type.kind == "object") {
                tw.WriteLine("                value.{0} = new LirBasicBlock();", Name);
                return;
            }
            if (Type.kind == "object[]") {
                tw.WriteLine("                value.{0} = new Object[] " +
                             "{{ new LirBasicBlock(), new LirBasicBlock() }};",
                             Name);
                return;
            }
            if (Type.kind == "uint[]") {
                tw.WriteLine("                value.{0} = new uint[] " +
                             "{{ 0xfedcba98, 0xfedcba97 }};", Name);
                return;
            }
            if (Type.kind == "int[]") {
                tw.WriteLine("                value.{0} = new int[] " +
                             "{{ 0x76543210, 0x76543219 }};", Name);
                return;
            }
            if (Type.isArray) {
                tw.WriteLine("                value.{0} = new {1} {{ null }};",
                             Name, Type.kind);
                return;
            }
            if (Type.isRefType && !Type.isInterface) {
                TypeInfo ti = Type;
                while (ti.isAbstract) {
#if false
                    tw.WriteLine("// {0} Bypassing {1} for {2}",
                                 Name, ti.kind, ti.children[0].kind);
#endif
                    ti = ti.children[0];
                }
                tw.WriteLine("                value.{0} = new {1}();",
                             Name, ti.kind);
            }
        }
    }

    private class TypeInfo
    {
        static TypeInfo()
        {
            used = new SortedList();
            used.Add("0", null);
        }

        public String                   kind;
        public String                   reason;
        public MetaDataTypeDefinition   type;
        public TypeInfo                 parent;
        public TypeInfo[]               children;
        public TypeInfo[]               descendants;
        public TypeInfo[]               inner;
        public TypeInfo[]               users;
        public TypeInfo                 arrayOf;
        public TypeInfo                 hasArray;
        public FieldInfo[]              fields;
        public int      id;
        public bool     isUsedInField;
        public bool     isRefType;
        public bool     isBuiltIn;
        public bool     isArray;
        public bool     isEnum;
        public bool     isStruct;
        public bool     isEnclosed;
        public bool     isSealed;
        public bool     isAbstract;     // "abstract class foo"
        public bool     isParent;       // has children.
        public bool     isOverload;     // has a parent.
        public bool     isInterface;
        // public bool     hasZeroConstructor; // Currently unused

        private TypeInfo()
        {
        }

        public static TypeInfo Add(string builtin)
        {
            TypeInfo ti = new TypeInfo();
            ti.kind = builtin;
            ti.reason = "builtin";
            ti.isBuiltIn = true;
            used.Add(builtin, ti);
            return ti;
        }

        public static TypeInfo Add(MetaDataTypeDefinition md, string reason)
        {
            string kind = md.FullName;

            if (kind == "") {
                System.Diagnostics.Debugger.Break();
            }

            TypeInfo ti;
            int id = used.IndexOfKey(kind);
            if (id > 0) {
                ti = used.GetByIndex(id) as TypeInfo;
                if (ti.type == null) {
                    ti.SetMetaData(md);
                }
            }
            else {
                ti = new TypeInfo();
                ti.kind = kind;
                ti.reason = reason;
                ti.SetMetaData(md);
                used.Add(ti.kind, ti);
            }
            return ti;
        }

        public static TypeInfo Add(Signature.Type st, string reason)
        {
            string kind = TypeToString(st);
            if (kind == "") {
                System.Diagnostics.Debugger.Break();
            }
            int id = used.IndexOfKey(kind);
            TypeInfo ti;
            if (id > 0) {
                ti = used.GetByIndex(id) as TypeInfo;
                if (!ti.isUsedInField) {
                    ti.isUsedInField = true;
                    ti.SetFieldInfo(st);
                }
            }
            else {
                ti = new TypeInfo();
                ti.kind = kind;
                ti.reason = reason;
                ti.SetFieldInfo(st);
                used.Add(ti.kind, ti);
            }
            return ti;
        }

        private void SetMetaData(MetaDataTypeDefinition md)
        {
            type = md;
            isInterface = ((md.Flags & TypeAttributes.Interface) != 0);
            isAbstract = ((md.Flags & TypeAttributes.Abstract) != 0);
            isSealed = ((md.Flags & TypeAttributes.Sealed) != 0);
        }

        private void SetFieldInfo(Signature.Type st)
        {
            switch (st.ElementType) {
                case ElementTypes.VOID:
                    break;
                case ElementTypes.BOOLEAN:
                    isBuiltIn = true;
                    break;
                case ElementTypes.CHAR:
                    isBuiltIn = true;
                    break;
                case ElementTypes.I1:
                    isBuiltIn = true;
                    break;
                case ElementTypes.U1:
                    isBuiltIn = true;
                    break;
                case ElementTypes.I2:
                    isBuiltIn = true;
                    break;
                case ElementTypes.U2:
                    isBuiltIn = true;
                    break;
                case ElementTypes.I4:
                    isBuiltIn = true;
                    break;
                case ElementTypes.U4:
                    isBuiltIn = true;
                    break;
                case ElementTypes.I8:
                    isBuiltIn = true;
                    break;
                case ElementTypes.U8:
                    isBuiltIn = true;
                    break;
                case ElementTypes.R4:
                    isBuiltIn = true;
                    break;
                case ElementTypes.R8:
                    isBuiltIn = true;
                    break;
                case ElementTypes.STRING:
                    isRefType = true;
                    isBuiltIn = true;
                    break;
                    //case ElementTypes.PTR:
                    //case ElementTypes.BYREF:
                case ElementTypes.VALUETYPE:
                    if (type == null) {
                        if (st.ClassObject is MetaDataTypeDefinition) {
                            SetMetaData((MetaDataTypeDefinition)st.ClassObject);
                        }
                    }
                    break;
                case ElementTypes.CLASS:
                    if (type == null) {
                        if (st.ClassObject is MetaDataTypeDefinition) {
                            SetMetaData((MetaDataTypeDefinition)st.ClassObject);
                        }
                    }
                    isRefType = true;
                    break;
                    //case ElementTypes.VAR:
                    //case ElementTypes.ARRAY:
                    //case ElementTypes.GENERICINST:
                    //case ElementTypes.TYPEDBYREF:
                case ElementTypes.I:
                    isBuiltIn = true;
                    break;
                case ElementTypes.U:
                    isBuiltIn = true;
                    break;
                    //case ElementTypes.FNPTR:
                case ElementTypes.OBJECT:
                    isBuiltIn = true;
                    isRefType = true;
                    break;
                case ElementTypes.SZARRAY:
                    isRefType = true;
                    isBuiltIn = false;
                    isArray = true;
                    if (st.TypeObject.ClassObject is MetaDataTypeDefinition) {
                        MetaDataTypeDefinition md = (MetaDataTypeDefinition)st.TypeObject.ClassObject;
                        arrayOf = TypeInfo.Add(md, "arrayed");
                        arrayOf.hasArray = this;
                        if (arrayOf.isBuiltIn) {
                            isBuiltIn = true;
                        }
                    }
                    else {
                        arrayOf = TypeInfo.Find(kind.Remove(kind.Length-2, 2));
                        arrayOf.hasArray = this;
                        if (arrayOf.isBuiltIn) {
                            isBuiltIn = true;
                        }
                    }
                    break;
                    //case ElementTypes.MVAR:
                    //case ElementTypes.CMOD_REQD:
                    //case ElementTypes.CMOD_OPT:
                    //case ElementTypes.INTERNAL:
                default:
                    throw new Exception("Unknown Field type");
            }
        }

        public static TypeInfo Find(string name)
        {
            return used[name] as TypeInfo;
        }

        public static TypeInfo Find(Signature.Type type)
        {
            string name = TypeToString(type);
            return Find(name);
        }

        public ArrayList GetDescendants(ArrayList des)
        {
            if (descendants != null) {
                foreach (TypeInfo di in descendants) {
                    des.Add(di);
                }
            }
            else if (children != null) {
                foreach (TypeInfo di in children) {
                    di.GetDescendants(des);
                    des.Add(di);
                }
            }
            return des;
        }

        public bool ParentsAreAllAbstract()
        {
            for (TypeInfo ti = this; ti.parent != null; ti = ti.parent) {
                if (!ti.parent.isAbstract) {
                    return false;
                }
            }
            return true;
        }
    }

    private static TypeInfo[] FindChildren(string parent)
    {
        ArrayList children = null;

        foreach (MetaData metadata in resolver.MetaDataList) {
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                if (type.Extends != null && type.Extends.FullName == parent) {
                    TypeInfo ti = used[type.FullName] as TypeInfo;
                    if (ti == null) {
                        continue;
                    }

#if false
                    Console.WriteLine("{0} is extended by {1}", parent, ti.kind);
#endif
                    if (children == null) {
                        children = new ArrayList();
                    }
                    children.Add(ti);
                }
            }
        }
        if (children != null) {
            return (TypeInfo[])children.ToArray(typeof(TypeInfo));
        }
        return null;
    }

    private static TypeInfo[] FindUsers(string iface)
    {
        ArrayList users = null;

        foreach (MetaData metadata in resolver.MetaDataList) {
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                foreach (MetaDataObject imd in type.Interfaces) {
                    if (imd.FullName == iface) {
                        TypeInfo ti = used[type.FullName] as TypeInfo;
                        if (ti == null) {
                            continue;
                        }
#if true
                        Console.WriteLine("{0} implemented by {1}", iface, ti.kind);
#endif
                        if (users == null) {
                            users = new ArrayList();
                        }
                        users.Add(ti);
                        break;
                    }
                }
            }
        }
        if (users != null) {
            return (TypeInfo[])users.ToArray(typeof(TypeInfo));
        }
        return null;
    }

    private static TypeInfo[] FindInner(string outer)
    {
        ArrayList inner = null;

        foreach (MetaData metadata in resolver.MetaDataList) {
            foreach (MetaDataTypeDefinition type in metadata.TypeDefs) {
                if ((type.EnclosingClass != null) &&
                    (type.EnclosingClass.FullName == outer)) {
                    TypeInfo ti = used[type.FullName] as TypeInfo;
                    if (ti == null) {
                        continue;
                    }
#if false
                    Console.WriteLine("{0} encloses {1}", outer, ti.kind);
#endif
                    if (inner == null) {
                        inner = new ArrayList();
                    }
                    inner.Add(ti);
                }
            }
        }
        if (inner != null) {
            return (TypeInfo[])inner.ToArray(typeof(TypeInfo));
        }
        return null;
    }

    private static void CompleteTypeInfoFields()
    {
        // First, fill in the missing base information.
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null) {
                continue;
            }

            ti.id = id;

            // Fill in the type definition if we don't have one.
            if (ti.type == null) {
                ti.type = resolver.ResolveName(ti.kind);
                if (ti.type == null && !ti.isBuiltIn && !ti.isArray) {
                    Console.WriteLine("!!! Couldn't resolve: {0}", ti.kind);
                }
            }
        }

        // Now fill in information for inheritance tree.
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null || ti.type == null) {
                continue;
            }

#if false
            Console.WriteLine("{0}:", ti.type.FullName);
#endif
            if (ti.type.Extends != null) {
                ti.isEnum = (ti.type.Extends.FullName == "System.Enum");
                ti.isStruct = (ti.type.Extends.FullName == "System.ValueType");
                if (ti.isEnum == false && ti.isStruct == false) {
                    ti.isOverload = !(ti.type.Extends.FullName == "System.Object");
                }
                ti.parent = TypeInfo.Find(ti.type.Extends.FullName);
            }

            if (ti.type.EnclosingClass != null) {
                ti.isEnclosed = true;
            }

            ti.children = FindChildren(ti.type.FullName);
            ti.inner = FindInner(ti.type.FullName);
            ti.isParent = (ti.children != null);

            if (ti.isStruct || ti.isEnum) {
                ti.isRefType = false;
            }
            else if (!ti.isBuiltIn) {
                ti.isRefType = true;
            }

            if (ti.isInterface) {
                ti.users = FindUsers(ti.kind);
            }
        }

        // Now fill in deep information for inheritance tree.
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null || ti.type == null) {
                continue;
            }

            if (ti.children != null && ti.descendants == null) {
                ArrayList des = ti.GetDescendants(new ArrayList());

                ti.descendants = (TypeInfo[])des.ToArray(typeof(TypeInfo));
            }
        }

        // Now collect all of the field information.
        for (int id = 0; id < used.Count; id++) {
            TypeInfo ti = used.GetByIndex(id) as TypeInfo;
            if (ti == null || ti.type == null) {
                continue;
            }

            ArrayList fieldList = new ArrayList();
            foreach (MetaDataField field in ti.type.Fields) {
                if (!IsMarshalField(field)) {
                    continue;
                }
                TypeInfo fi = TypeInfo.Find(field.Signature.FieldType);

                fieldList.Add(new FieldInfo(field.Name, fi));
            }

            ti.fields = (FieldInfo[])fieldList.ToArray(typeof(FieldInfo));
        }
    }
}
