using System;
using System.Collections;
using System.Collections.Specialized;
using System.IO;
using System.Diagnostics;
using System.Reflection;
using System.Reflection.Emit;
using System.Security.Cryptography;
using System.Text;
using ElementTypes = Bartok.MSIL.ElementTypes;
using Bartok.MSIL;

public class ilgen: ITrackable {
    public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            new ilgen(w, msg).compilation(ast);
        return ast;
    }

    public Stack asts = new Stack();    // top element is current ast node
    public string mainTypeName = null;
    public StringDictionary moduleMap = new StringDictionary();
    public MessageWriter msg;
    public TextWriter wr;
    public BuiltinTypes T;
    public ilgen(TextWriter wr, compilation_unit ast) : this(wr, new MessageWriter()) {
        T = ((compilation)ast.parent).global.Types;
    }
    public ilgen(TextWriter wr, MessageWriter msg) {
        this.wr = wr;
        this.msg = msg;
    }

    // ITrackable
    public object subject {
        get { return asts.Count > 0 ? asts.Peek() : null; }
    }

    public virtual ILState NewILState(ilgen parent) {
        return new ILState(parent);
    }
    public class ILState: gen {
        protected ilgen parent;
        protected int depth = 0;
        public int maxstack = 0;
        protected int offset = 0;
        protected TextWriter w;

        public ILState(ilgen parent) : base(parent.T, parent.msg, parent.asts) {
            this.parent = parent;
            this.w = parent.wr;
        }
        override public object BeginTry() {
            Emit(".try {{");
            return base.BeginTry();
        }
        override public object BeginFinally(object handle) {
            base.BeginFinally(handle);
            Emit("}}");
            Emit("finally {{");
            return -(int)handle;
        }
        override public void boolean_value(binary_expression ast) {
            base.boolean_value(ast);
            if (!(ast.method != null && ast.method.Type == parent.T.Bool && ast.method.declSpace != null))
                Depth -= 1; // account for two loads in boolean_value
        }
        override public void catch_clause(Type ty, Local sym, statement block, object handle) {
            gotoLabel(OpCodes.Leave, (int)handle);
            Emit("}}");
            Emit("catch {0} {{", ClassRef(ty));
            Depth += 1;
            base.catch_clause(ty, sym, block, handle);
        }
        string ClassRef(Type t) { return parent.ClassRef(t); }
        override public void defLabel(int lab) {
            Emit("{0}:", getLabel(lab));
        }
        public int Depth {
            get { return depth; }
            set {
                //w.WriteLine("//depth={0}", value);
                depth = value;
                if (depth < 0) {
                    Debug.Assert(depth >= 0);
                    depth = 0;
                }
                maxstack = Math.Max(depth, maxstack);
            }
        }
        public void Emit(string fmt, params object[] operands) {
            w.WriteLine(fmt, operands);
        }
        public void Emit(OpCode op, params string[] operands) {
            w.Write(op);
            foreach (string s in operands)
                w.Write(" {0}", s);
            w.WriteLine();
            switch (op.StackBehaviourPop) {
            case StackBehaviour.Pop0: break;
            case StackBehaviour.Varpop: break;
            case StackBehaviour.Popref:
            case StackBehaviour.Popi:
            case StackBehaviour.Pop1:       Depth -= 1; break;
            case StackBehaviour.Pop1_pop1:
            case StackBehaviour.Popi_pop1:
            case StackBehaviour.Popi_popi:
            case StackBehaviour.Popi_popi8:
            case StackBehaviour.Popi_popr4:
            case StackBehaviour.Popi_popr8:
            case StackBehaviour.Popref_pop1:
            case StackBehaviour.Popref_popi:    Depth -= 2; break;
            case StackBehaviour.Popi_popi_popi:
            case StackBehaviour.Popref_popi_popi:
            case StackBehaviour.Popref_popi_popi8:
            case StackBehaviour.Popref_popi_popr4:
            case StackBehaviour.Popref_popi_popr8:
            case StackBehaviour.Popref_popi_popref: Depth -= 3; break;
            default: throw new ArgumentException("unknown opcode " + op.ToString());
            }
            switch (op.StackBehaviourPush) {
            case StackBehaviour.Varpush: break;
            case StackBehaviour.Push0: break;
            case StackBehaviour.Pushi:
            case StackBehaviour.Pushi8:
            case StackBehaviour.Pushr4:
            case StackBehaviour.Pushr8:
            case StackBehaviour.Pushref:
            case StackBehaviour.Push1: Depth += 1; break;
            case StackBehaviour.Push1_push1: Depth += 2; break;
            default: throw new ArgumentException("unknown opcode " + op.ToString());
            }
        }
        override public void Emit(OpCode op) { Emit(op, new string[0]); }
        override public void Emit(OpCode op, Constructor x) { Emit(op, (Method)x); }
        override public void Emit(OpCode op, float x) { Emit(op, x.ToString()); }
        override public void Emit(OpCode op, double x) { Emit(op, x.ToString()); }
        override public void Emit(OpCode op, Field x) {
            Emit(op, Name(x.Type), FieldRef(x));
        }
        override public void Emit(OpCode op, Formal x) { Emit(op, (Local)x); }
        override public void Emit(OpCode op, int x) { Emit(op, x.ToString()); }
        override public void Emit(OpCode op, Local x) {
            Emit(op, String.Format("{0} // {1}", x.ordinal, x.Name));
        }
        override public void Emit(OpCode op, Method x) {
            Emit(op, x.IsInstance ? "instance" : "", Name(x.Type), MethodRef(x));
            if (op.Name == "newobj")
                Depth -= x.ArgCount;
            else if (op.Name.StartsWith("call")) {
                Depth -= x.ArgCount + (x.IsInstance ? 1 : 0);
                if (x.Name == "set_Item")
                    Depth -= 1; // value argument
                if (x.Type != parent.T.Void)
                    Depth += 1;
            }
        }
        override public void Emit(OpCode op, string x) { Emit(op, quote(x)); }
        override public void Emit(OpCode op, Type x) { Emit(op, Name(x)); }
        override public void EmitCreateArray(ArrayType ty, Type ety, int rank) {
            Emit(OpCodes.Newobj, "instance void",
                String.Format("{0}::.ctor({1})", Name(ty), repl(",int32", rank).Substring(1)));
            Depth -= rank;
        }
        override public void EmitLoad(int index) {
            Emit(OpCodes.Ldloc, String.Format("{0} // t{0}", index));
        }
        override public void EmitLoadAddress(int index) {
            Emit(OpCodes.Ldloca, String.Format("{0} // t{0}", index));
        }
        override public void EmitLoadElement(ArrayType ty, Type ety, int rank) {
            Emit(OpCodes.Call, "instance", Name(ety),
                String.Format("{0}::Get({1})", Name(ty), repl(",int32", rank).Substring(1)));
            Depth -= rank + 1;
            Depth += 1;
        }
        override public void EmitLoadElementAddress(ArrayType ty, Type ety, int rank) {
            Emit(OpCodes.Call, "instance", Name(ety), "&",
                String.Format("{0}::Address({1})", Name(ty), repl(",int32", rank).Substring(1)));
            Depth -= rank + 1;
            Depth += 1;
        }
        override public void EmitStore(int index) {
            Emit(OpCodes.Stloc, String.Format("{0} // t{0}", index));
        }
        override public void EmitStoreElement(ArrayType ty, Type ety, int rank) {
            Emit(OpCodes.Call, "instance void",
                String.Format("{0}::Set({1}{2})", Name(ty), repl("int32,", rank), Name(ety)));
            Depth -= rank + 2;
        }
        override public void EmitSwitch(int[] caselabels) {
            Emit(OpCodes.Switch, "(");
            for (int i = 0; i < caselabels.Length; i++)
                Emit("{0},", getLabel(caselabels[i]));
            Emit(")");
        }
        override public void EndTry(object handle) {
            if ((int)handle < 0) {
                Emit("endfinally");
                handle = -(int)handle;
            } else
                gotoLabel(OpCodes.Leave, (int)handle);
            Emit("}} // end .try");
            base.EndTry(handle);
        }
        string FieldRef(Field f) { return parent.FieldRef(f); }
        public string getLabel(int lab) {
            return String.Format("${0}", lab);
        }
        override public void gotoLabel(OpCode inst, int lab) {
            Emit(inst, getLabel(lab));
        }
        string MethodRef(Method m) { return parent.MethodRef(m); }
        string Name(Type ty) { return parent.Name(ty); }
        override public int newLocal(Type ty) {
            return newLocal(ty, String.Format("t{0}", offset));
        }
        override public int newLocal(Type ty, string name) {
            int var = offset++;
            Emit(".locals init ([{0}]{1} '{2}')", var, Name(ty), name);
            return var;
        }
        public static string quote(string str) {
            return '"' + str.Replace("\"", "\\\"") + '"';
        }
        public static string repl(string str, int n) {
            string s = "";
            while (n-- > 0)
                s += str;
            return s;
        }
        override public void statement(statement ast, Method m) {
            base.statement(ast, m);
            if (m.Type != parent.T.Void)
                Depth -= 1;
        }
        override public void string_literal(string_literal ast) {
            Emit(OpCodes.Ldstr, ast.token.str);
        }
    }
    public virtual void Assemble(stringList argv, string input, string output, bool verbose, bool debug) {
        Process p = new Process();
        p.StartInfo.UseShellExecute = false;
        string ilasm = "ilasm";
        foreach (string arg in argv) {
            if (arg.StartsWith("/ilasm:") || arg.StartsWith("-ilasm:")) {
                ilasm  = arg.Substring("/ilasm:".Length);
            }
        }
        
        p.StartInfo.FileName = ilasm;
        p.StartInfo.Arguments = String.Format("/nologo /quiet {0} /{1} /noautoinherit /output=\"{2}\" \"{3}\"",
                                              debug ? "/pdb" : "",
                                              output.ToLower().EndsWith(".exe") ? "exe" : "dll",
                                              output,
                                              input);
        if (verbose)
            Console.Error.WriteLine("{0} {1}", p.StartInfo.FileName, p.StartInfo.Arguments);
        p.Start();
        p.WaitForExit();
        if (p.ExitCode != 0)
        {
            msg.Error("ilasm failed, command line: \"{0}\" {1}", p.StartInfo.FileName, p.StartInfo.Arguments);
        }
    }
    public virtual void class_declaration(class_declaration ast) {
        EmitClassHead(ast.sym);
        WriteLine("{{");
        EmitClassBody(ast.attrs, ast.body);
        WriteLine("}} // end of class {0}", ast.sym.FullName);
    }
    public string ClassRef(Type ty) {
        string module = "";
        if (ty.module != null)
            module = String.Format("[{0}]", ModuleName(ty.module));
        string name = "";
        if (ty.RealName.StartsWith("System.") && ty.enclosingType == null)
            name = ty.RealName;
        else {
            // quoting syntax for nested types has changed
            // correct 2.0 syntax is 'namespace-name'.'outer-class-name'/'inner-class-name' 
            // incorrect 1.0 syntax is 'namespace-name.outer-class-name/inner-class-name'
            for ( ; ty.enclosingType != null; ty = ty.enclosingType)
                name = "/'" + ty.Name + "'" + name;
            name = "'" + ty.FullName + "'" + name;
        }
        return module + name;
    }
    public virtual void comment(AST ast) {
        if (ast != null) {
            Write("// {0}: ", ast.begin.ToString());
            source.visit((compilation)ast, wr, null, msg);
            WriteLine();
        }
    }
    public virtual void comment(AST ast, string fmt, params string[] args) {
        if (ast != null) {
            Write("// {0}: ", ast.begin.ToString());
            WriteLine(fmt, args);
        }
    }
    public virtual void compilation(compilation ast) {
        T = ast.global.Types;
        string target = ".exe", outdir = "", oname = null, iname = null;
        foreach (string s in ast.args)
            if (s[0] == '/' || s[0] == '-') {
                string arg = s.Substring(1);
                if (arg.StartsWith("out:")) {
                    oname = arg.Substring(4);
                    iname = Path.GetFileNameWithoutExtension(oname) + ".il";
                } else if (arg.StartsWith("outdir:"))
                    outdir = arg.Substring(7).TrimEnd('/', '\\') + "\\";
                else if (arg.StartsWith("main:") || arg.StartsWith("m:"))
                    mainTypeName = arg.Substring(arg.IndexOf(':')+1);
                else if (arg.StartsWith("target:") || arg.StartsWith("t:"))
                    switch (arg.Substring(arg.IndexOf(':')+1).ToLower()) {
                    case "winexe": case "exe": target = ".exe"; break;
                    case "library": target = ".dll"; break;
                    }
                else if (arg.StartsWith("r:") || arg.StartsWith("reference:")) {
                    foreach (string f in arg.Substring(arg.IndexOf(':')+1).Split(','))
                        if (f.IndexOf('=') >= 0) {
                            string[] map = f.Split('=');
                            map[0] = Path.GetFileNameWithoutExtension(map[0]);
                            moduleMap[map[0]] = map[1];
                        }
                }
            } else if ((s.EndsWith(".cs") || s.EndsWith(".csi")) && iname == null)
                iname = Path.GetFileNameWithoutExtension(s) + ".il";
        if (oname == null && iname == null)
            oname = "a" + target;
        else {
            if (oname == null)
                oname = Path.GetFileNameWithoutExtension(iname) + target;
            iname = outdir + iname;
        }
        try {
            wr.Close();
            wr = new StreamWriter(iname);
        } catch (Exception e) {
            msg.Error("can't write \"{0}\": {1}", iname, e.Message);
            iname = null;
        }
        try {
            SHA1 sha = new SHA1CryptoServiceProvider();
            foreach (string path in ast.assemblyRefs) {
                PELoader pe = new PELoader(path);
                MetaData md = MetaData.loadMetaData(path, pe, false, false);
                MetaDataAssembly mda = (MetaDataAssembly)md.Assemblies[0];

                WriteLine(".assembly extern '{0}' {{", ModuleName(path));
                WriteLine(".ver {0}:{1}:{2}:{3}",
                          mda.MajorVersion,
                          mda.MinorVersion,
                          mda.BuildNumber,
                          mda.RevisionNumber);

                byte[] hash = sha.ComputeHash(mda.PublicKey);
                Write(".publickeytoken = (");
                int len = hash.Length - 1;
                for (int i = 0; i < 8; i++)
                    Emitint(1, (ulong)hash[len - i]);
                WriteLine(" )");

#if VERIFY_HASH_USING_REFLECTION
                try {
                    Assembly asm = Assembly.LoadFrom(path);
                    AssemblyName name = asm.GetName();
                    WriteLine("// .assembly extern '{0}' {{", ModuleName(asm.Location));
                    WriteLine("// .ver {0}", name.Version.ToString().Replace('.',':'));
                    byte[] bytes = name.GetPublicKeyToken();
                    if (bytes != null) {
                        Write("// .publickeytoken = (");
                        for (int i = 0; i < bytes.Length; i++)
                            Emitint(1, (ulong)bytes[i]);
                        WriteLine(" )");
                    }
                }
                catch {
                }
#endif

#if false
                foreach (MetaData md in resolver.MetaDataList) {
                    MetaDataAssembly mda = (MetaDataAssembly)md.Assemblies[0];
                }
                XmlNode asm = manifest.CreateNode(XmlNodeType.Element, "assembly", "");
                AddAttribute(asm, "filename", assemblyname);
                if (mda.MajorVersion != 0 || mda.MinorVersion != 0 ||
                    mda.BuildNumber != 0 || mda.RevisionNumber != 0) {
                    AddAttribute(asm, "version", String.Format("{0}.{1}.{2}.{3}",
                                                               mda.MajorVersion,
                                                               mda.MinorVersion,
                                                               mda.BuildNumber,
                                                               mda.RevisionNumber));
                }
                if (mda.PublicKey != null & mda.PublicKey.Length > 0) {
                    AddAttribute(asm, "publickey", String.Format("{0}",
                                                                 KeyToString(mda.PublicKey)));
                }
                if (mda.Locale != null && mda.Locale != "") {
                    AddAttribute(asm, "locale", mda.Locale);
                }
                AddAttribute(asm, "cache", StripCacheFromPath(file));
                assembliesNode.AppendChild(asm);
#endif

                WriteLine("}}");
            }
            WriteLine(".assembly '{0}' {{", Path.GetFileNameWithoutExtension(oname));

            object o;
            o = Evalattribute(ast.inputs, "System.Reflection.AssemblyVersionAttribute");
            if (o != null && o is String) {
                WriteLine(".ver {0}", ((string)o).Replace('.',':'));
            }
            else {
                WriteLine(".ver 0:0:0:0");
            }

            o = Evalattribute(ast.inputs, "System.Reflection.AssemblyKeyFileAttribute");
            if (o != null && o is String) {
                string file = outdir + (string)o;
                WriteLine("//publickey({0})", file);
                try {
                    FileStream fs = new FileStream(outdir + (string)o,
                                                   FileMode.Open, FileAccess.Read);
                    BinaryReader r = new BinaryReader(fs);
                    byte[] values = r.ReadBytes(0x10000);
                    if (values != null) {
                        Write(".publickey = (", file);
                        int len = values.Length;
                        for (int i = 0; i < len; i++) {
                            Write(" {0:x2}", values[i]);
                            if (i % 16 == 15) {
                                WriteLine();
                                Write("              ");
                            }
                        }
                        WriteLine(" )");
                    }
                    r.Close();
                    if (values.Length >= 8) {
                        WriteLine(".hash algorithm 0x{0:x2}{1:x2}{2:x2}{3:x2}",
                                  values[7],
                                  values[6],
                                  values[5],
                                  values[4]);
                    }
                }
                catch (Exception e) {
                    Console.WriteLine("Couldn't access public key {0}", file);
                    Console.WriteLine("Exception: {0}", e);
                }
            }

            foreach (compilation_unit x in ast.inputs)
                compilation_unit_attr(x);
            WriteLine("}}");

            foreach (compilation_unit x in ast.inputs)
                compilation_unit(x);
        } finally {
            if (wr != Console.Out)
                wr.Close();
        }
        if (iname != null && msg.Count == 0)
            Assemble(ast.args, iname, oname, false, true);
    }

    public virtual object Evalattribute(compilation_unitList units, string name) {
        if (units != null) {
            foreach (compilation_unit x in units) {
                if (x.attributes != null) {
                    foreach (attribute_section s in x.attributes) {
                        foreach (attribute a in s.attributes) {
                            if (a.sym.RealName == name) {
                                foreach (argument n in a.arguments.args) {
                                    return n.expr.value;
                                }
                                return "false";
                            }
                        }
                    }
                }
            }
        }
        return null;
    }

    public virtual void compilation_unit_attr(compilation_unit ast) {
        EmitattributeSectionList(ast.attributes);
    }
    public virtual void compilation_unit(compilation_unit ast) {
        foreach (declaration d in ast.declarations)
            declaration(d);
    }
    public virtual void constant_declaration(constant_declaration ast) {
        foreach (const_declarator x in ast.decls) {
            Constant f = x.sym;
            Write(".field ");
            EmitModifiers(f);
            Write("static literal ");
            Write("{0} '{1}' = ", Name(f.Type), f.Name);
            if (f.value is string)
                WriteLine("{0}", ILState.quote((string)f.value));
            else if (f.Type is EnumType)
                EmitDataItem(((EnumType)f.Type).baseType, f.value);
            else
                EmitDataItem(f.Type, f.value);
        }
    }
    public virtual void constructor_declaration(constructor_declaration ast) {
        Method m = ast.sym;
        Write(".method hidebysig specialname rtspecialname ");
        EmitModifiers(m);
        WriteLine("{0} {1}({2}) {3}{{", Name(m.Type), Name(m), Signature(m),
             ast.block == null && m.declSpace.Owner is DelegateType ? "runtime managed " : "");
        EmitattributeSectionList(ast.attrs);
        declarationList body;
        if (ast.parent is class_declaration)
            body = ((class_declaration)ast.parent).body;
        else
            body = ((struct_declaration)ast.parent).body;
        ILState g = NewILState(this);
        if (ast.decl.init != null)
            constructor_initializer(ast.decl.init, body, g);
        if (m.IsStatic)
            foreach (declaration d in body)
                if (d is field_declaration) {
                    foreach (field_declarator f in ((field_declaration)d).decls)
                        if (f.sym.IsStatic)
                            variable_initializer(f.init, f.sym, g);
                } else if (d is event_declaration1)
                    foreach (event_declarator e in ((event_declaration1)d).decls)
                        if (e.sym.IsStatic)
                            variable_initializer(e.init, e.sym, g);
        int i;
        for (i = 0; i < m.ArgCount; i++)
            m[i].ordinal = m.IsInstance ? i + 1 : i;
        if (ast.block != null)
            EmitMethodBody(m, ast.block, g);
        WriteLine("}} // end of constructor {0}", m.FullName);
    }
    public virtual void constructor_initializer(constructor_initializer ast, declarationList body, ILState g) {
        if (ast is base_initializer) {
            foreach (declaration d in body)
                if (d is field_declaration) {
                    foreach (field_declarator f in ((field_declaration)d).decls)
                        if (f.sym.IsInstance)
                            variable_initializer(f.init, f.sym, g);
                } else if (d is event_declaration1)
                    foreach (event_declarator e in ((event_declaration1)d).decls)
                        if (e.sym.IsInstance)
                        variable_initializer(e.init, e.sym, g);
            g.base_initializer((base_initializer)ast);
        } else
            g.this_initializer((this_initializer)ast);
    }
    public virtual void declaration(declaration ast) {
        asts.Push(ast);
             if (ast is class_declaration) class_declaration((class_declaration)ast);
        else if (ast is constant_declaration) constant_declaration((constant_declaration)ast);
        else if (ast is constructor_declaration) constructor_declaration((constructor_declaration)ast);
        else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast);
        else if (ast is destructor_declaration) destructor_declaration((destructor_declaration)ast);
        else if (ast is enum_declaration) enum_declaration((enum_declaration)ast);
        else if (ast is event_declaration1) event_declaration1((event_declaration1)ast);
        else if (ast is event_declaration2) event_declaration2((event_declaration2)ast);
        else if (ast is field_declaration) field_declaration((field_declaration)ast);
        else if (ast is indexer_declaration) indexer_declaration((indexer_declaration)ast);
        else if (ast is interface_declaration) interface_declaration((interface_declaration)ast);
        else if (ast is interface_event_declaration) interface_event_declaration((interface_event_declaration)ast);
        else if (ast is interface_indexer_declaration) interface_indexer_declaration((interface_indexer_declaration)ast);
        else if (ast is interface_method_declaration) interface_method_declaration((interface_method_declaration)ast);
        else if (ast is interface_property_declaration) interface_property_declaration((interface_property_declaration)ast);
        else if (ast is method_declaration) method_declaration((method_declaration)ast);
        else if (ast is namespace_declaration) namespace_declaration((namespace_declaration)ast);
        else if (ast is operator_declaration) operator_declaration((operator_declaration)ast);
        else if (ast is property_declaration) property_declaration((property_declaration)ast);
        else if (ast is struct_declaration) struct_declaration((struct_declaration)ast);
        else throw new ArgumentException();
        asts.Pop();
    }
    public virtual void delegate_declaration(delegate_declaration ast) {
        EmitClassHead(ast.sym);
        WriteLine("{{");
        EmitattributeSectionList(ast.attrs);
        foreach (Symbol s in ast.sym)
            if (s is Method)
                EmitMethod((Method)s, null, null, null);
        WriteLine("}} // end of delegate {0}", ast.sym.FullName);
    }
    public virtual void destructor_declaration(destructor_declaration ast) {
        EmitMethod(ast.sym, ast.attrs, ast.block, "specialname rtspecialname");
    }
    public virtual void Emitattribute(attribute ast) {
        if (ast.arguments != null) {
            Write(".custom instance void {0}::.ctor({1}) = (", ClassRef(ast.sym),
                  Signature(ast.method, false));
            Emitint(1, 1UL); Emitint(1, 0UL);   // prolog 01 00
            foreach (argument x in ast.arguments.args) {
                WriteLine();
                EmitFixedArg(x.expr.value);
            }
            WriteLine();
            Emitint(2, (ulong)ast.arguments.namedargs.Count);
            foreach (named_argument x in ast.arguments.namedargs) {
                WriteLine();
                EmitNamedArg(x);
            }
        } else {
            Write(".custom instance void {0}::.ctor() = (", ClassRef(ast.sym));
            Emitint(1, 1UL); Emitint(1, 0UL);   // prolog 01 00
            Emitint(2, 0UL);    // no named arguments
        }
        WriteLine(" )");
    }
    public virtual void EmitattributeSectionList(attribute_sectionList attrs) {
        if (attrs != null)
            foreach (attribute_section s in attrs)
                foreach (attribute a in s.attributes)
                    Emitattribute(a);
    }
    public virtual void EmitClassHead(ClassType c) {
        Write(".class ");
        if (c.enclosingType != null)
            Write("nested ");
        EmitModifiers(c);
        if (c is InterfaceType)
            Write("interface abstract ");
        WriteLine("'{0}'", c.Name);
        if (c.baseClass != null)
            WriteLine("\textends {0}", ClassRef(c.baseClass));
        if (c.interfaces.Count > 0) {
            Write("\timplements ");
            for (int i = 0; i < c.interfaces.Count; i++) {
                if (i > 0)
                    Write(",");
                Write("{0}", ClassRef(c.interfaces[i]));
            }
            WriteLine();
        }
    }
    public virtual void EmitClassBody(attribute_sectionList attrs, declarationList body) {
        EmitattributeSectionList(attrs);
        foreach (declaration d in body)
            declaration(d);
    }
    public virtual void EmitDataItem(Type ty, object value) {
        string name = Name(ty);
        if (name.StartsWith("unsigned "))
            name = name.Substring(9);
        WriteLine("{0}({1})", name, value.ToString());
    }
    public virtual void EmitDefaultAccessor(Event e, Method m) {
        Write(".method hidebysig specialname ");
        EmitModifiers(m);
        if (m.IsInstance) {
            Write("instance ");
            m[0].ordinal = 1;
        } else
            m[0].ordinal = 0;
        WriteLine("void {0}({1} 'value') cil managed synchronized {{", Name(m), Name(m[0].Type));
        if (!m.Is("abstract")) {
            ILState g = NewILState(this);
            g.EmitDefaultAccessor(e, m);
            EmitMethodBody(m, null, g);
        }
        WriteLine("}} // end of method {0}", m.FullName);
    }
    public virtual void EmitEvent(Event t, event_accessorList accessors) {
        WriteLine(".event '{0}' '{1}' {{", t.Type.FullName, t.Name);
        WriteLine(".addon {0}void {1}", t.IsStatic ? "" : "instance ", MethodRef(t.Add));
        WriteLine(".removeon {0}void {1}", t.IsStatic ? "" : "instance ", MethodRef(t.Remove));
        WriteLine("}} // end of event {0}", t.FullName);
        if (accessors != null)
            foreach (event_accessor a in accessors)
                EmitMethod(a.sym, a.attrs, a.block, "specialname rtspecialname");
    }
    public virtual void EmitFixedArg(object value) {
        if (value == null)
            Emitint(1, 0xFFUL);
        else if (value is string)
            Emitstring((string)value);
        else if (value is char)
            Emitint(2, (ulong)(ushort)(char)value);
        else if (value is bool)
            Emitint(1, (bool)value ? 1UL : 0UL);
        else if (value is  sbyte) Emitint(1, (ulong)( sbyte)value);
        else if (value is   byte) Emitint(1, (ulong)(  byte)value);
        else if (value is  short) Emitint(2, (ulong)( short)value);
        else if (value is ushort) Emitint(2, (ulong)(ushort)value);
        else if (value is    int) Emitint(4, (ulong)(   int)value);
        else if (value is   uint) Emitint(4, (ulong)(  uint)value);
        else if (value is   long) Emitint(8, (ulong)(  long)value);
        else if (value is  ulong) Emitint(8, (ulong)        value);
        else
            msg.Error("attribute type '{0}' not yet supported", value.GetType().FullName);
    }
    public virtual void Emitint(int len, ulong value) {
        for (int i = 0; i < len; i++) {
            Write(" {0:x2}", value&0xff);
            value >>= 8;
        }
    }
    public virtual void EmitMethod(Method m, attribute_sectionList attrs, statement body, string extraattributes) {
        Write(".method hidebysig ");
        if (extraattributes != null)
            Write("{0} ", extraattributes);
        EmitModifiers(m);
        if (m.IsInstance)
            Write("instance ");
        WriteLine("{0} {1}({2}) {3}{{", Name(m.Type), Name(m), Signature(m),
            body == null && m.declSpace.Owner is DelegateType ? "runtime managed " : "");
        EmitattributeSectionList(attrs);
        if ((mainTypeName == null || mainTypeName == m.GetType().Name)
        && m.Name == "Main" && m.IsStatic)
            WriteLine(".entrypoint");
        if (m.interfaceMethod != null)
            WriteLine(".override {0}::'{1}'", ClassRef(m.interfaceMethod.GetType()),
                m.interfaceMethod.Name);
        int i;
        for (i = 0; i < m.ArgCount; i++)
            m[i].ordinal = m.IsInstance ? i + 1 : i;
        if (m.Name == "set_Item")
            ((Formal)m.locals["value"]).ordinal = m.IsInstance ? i + 1 : i;
        if (body != null)
            EmitMethodBody(m, body, NewILState(this));
        WriteLine("}} // end of method {0}", m.FullName);
    }
    public virtual void EmitMethodBody(Method m, statement body, ILState g) {
        if (body != null)
            g.statement(body, m);
        WriteLine(".maxstack {0}", g.maxstack);
        Debug.Assert(g.Depth == 0);
    }
    public virtual void EmitModifiers(Symbol t) {
        string emit = "";
        foreach (string mod in t.Modifiers)
            switch (mod) {
            case "new":
                emit += " newslot"; break;
            case "override":
                emit += " virtual"; break;
            case "protected":
            case "internal": case "readonly": case "unsafe":
                break;
            case "sealed":
                emit += t is Method ? " final" : " sealed"; break;
            default:
                emit += " " + mod;
                break;
            }
        if (emit.Length > 1)
            Write("{0} ", emit.Substring(1));
    }
    public virtual void EmitNamedArg(named_argument ast) {
        if (ast.sym is Field)
            Emitint(1, 0x53UL);
        else if (ast.sym is Property)
            Emitint(1, 0x54UL);
        Type ty = ast.sym.Type;
             if (ty == T.Bool)   Emitint(1, (ulong)ElementTypes.BOOLEAN);
        else if (ty == T.Byte)   Emitint(1, (ulong)ElementTypes.U1);
        else if (ty == T.Char)   Emitint(1, (ulong)ElementTypes.CHAR);
        else if (ty == T.Double) Emitint(1, (ulong)ElementTypes.R8);
        else if (ty == T.Short)  Emitint(1, (ulong)ElementTypes.I2);
        else if (ty == T.Int)    Emitint(1, (ulong)ElementTypes.I4);
        else if (ty == T.Long)   Emitint(1, (ulong)ElementTypes.I8);
        else if (ty == T.SByte)  Emitint(1, (ulong)ElementTypes.I1);
        else if (ty == T.Float)  Emitint(1, (ulong)ElementTypes.R4);
        else if (ty == T.String) Emitint(1, (ulong)ElementTypes.STRING);
        else if (ty == T.UShort) Emitint(1, (ulong)ElementTypes.U2);
        else if (ty == T.UInt)   Emitint(1, (ulong)ElementTypes.U4);
        else if (ty == T.ULong)  Emitint(1, (ulong)ElementTypes.U8);
        else Debug.Assert(false);
        Emitstring(ast.id.str);
        EmitFixedArg(ast.expr.value);
    }
    public virtual void EmitProperty(Property p, attribute_sectionList attrs, accessor_declarationList decls) {
        Write(".property ");
        if (p.IsInstance)
            Write("instance ");
        WriteLine("{1} {0}() {{",  p.Name, Name(p.Type));
        EmitattributeSectionList(attrs);
        foreach (accessor_declaration d in decls) {
            Write(".{0}", d.id.str);
            if (d.sym.IsInstance)
                Write(" instance");
            WriteLine(" {0} {1}", d.id.str == "get" ? Name(p.Type) : "void", MethodRef(d.sym));
        }
        WriteLine("}} // end of {0} {1}", p.Kind, p.FullName);
        foreach (accessor_declaration d in decls)
            EmitMethod(d.sym, d.attrs, d.body, "specialname");
    }
    public virtual void Emitstring(string value) {
        if (value.Length <= 127)
            Emitint(1, (ulong)value.Length);
        else if (value.Length >= 128 && value.Length <= 16383) {
            uint n = (uint)value.Length;
            Emitint(1, ((n>>8)&0x7fUL)|0x80UL);
            Emitint(1,       n&0xffUL);
        } else {
            uint n = (uint)value.Length;
            Emitint(1, ((n>>24)&0x1fUL)|0xc0UL);
            Emitint(1,  (n>>16)&0xffUL);
            Emitint(1,  (n>> 8)&0xffUL);
            Emitint(1,        n&0xffUL);
        }
        foreach (char c in value)
            Emitint(1, (ulong)(byte)c);
    }
    public virtual void enum_declaration(enum_declaration ast) {
        EnumType e = ast.sym;
        Write(".class ");
        if (e.enclosingType != null)
            Write("nested ");
        EmitModifiers(e);
        WriteLine("auto ansi serializable sealed '{0}' extends {1}", e.Name, ClassRef(T.Enum));
        WriteLine("{{");
        EmitattributeSectionList(ast.attrs);
        string name = "";
        Type ty;
        for (ty = e; ty.enclosingType != null; ty = ty.enclosingType)
            name = "/" + ty.Name + name;
        name = ty.FullName + name;
        foreach (enum_member_declaration d in ast.body) {
            Write(".field public static literal valuetype '{0}' {1} = ", name, d.sym.Name);
            EmitDataItem(e.baseType, d.sym.value);
        }
        WriteLine(".field public rtspecialname specialname {0} value__", Name(e.baseType));
        WriteLine("}} // end of enumeration {0}", e.FullName);
    }
    public virtual void event_declaration1(event_declaration1 ast) {
        EmitattributeSectionList(ast.attrs);
        foreach (event_declarator d in ast.decls) {
            WriteLine(".field private {2}{0} {1}", Name(d.sym.Type), d.sym.Name, d.sym.IsStatic ? "static " : "");
            EmitEvent(d.sym, null);
            EmitDefaultAccessor(d.sym, d.sym.Add);
            EmitDefaultAccessor(d.sym, d.sym.Remove);
        }
    }
    public virtual void event_declaration2(event_declaration2 ast) {
        EmitattributeSectionList(ast.attrs);
        EmitEvent(ast.sym, ast.accessors);
    }
    public virtual void field_declaration(field_declaration ast) {
        foreach (field_declarator x in ast.decls) {
            Field f = x.sym;
            Write(".field ");
            EmitModifiers(f);
            WriteLine("{0} {1}", Name(f.Type), Name(f));
            EmitattributeSectionList(ast.attrs);
        }
    }
    public string FieldRef(Symbol f) {
        return String.Format("{0}::'{1}'", ClassRef(f.GetType()), f.Name);
    }
    public virtual void indexer_declaration(indexer_declaration ast) {
        foreach (accessor_declaration d in ast.accessors)
            if (d.id.str == "get") {
                WriteLine(".property instance {0} Item({1}) {{", Name(d.sym.Type),
                    Signature(d.sym, false));
                break;
            }
        EmitattributeSectionList(ast.attrs);
        foreach (accessor_declaration d in ast.accessors) {
            Write(".{0} instance", d.id.str);
            WriteLine(" {0} {1}", Name(d.sym.Type), MethodRef(d.sym));
        }
        WriteLine("}} // end of property Item");
        foreach (accessor_declaration d in ast.accessors)
            EmitMethod(d.sym, d.attrs, d.body, "specialname");
    }
    public virtual void interface_declaration(interface_declaration ast) {
        EmitClassHead(ast.sym);
        WriteLine("{{");
        EmitClassBody(ast.attrs, ast.body);
        WriteLine("}} // end of interface {0}", ast.sym.FullName);
    }
    public virtual void interface_event_declaration(interface_event_declaration ast) {
        EmitattributeSectionList(ast.attrs);
        EmitEvent(ast.sym, null);
        EmitDefaultAccessor(ast.sym, ast.sym.Add);
        EmitDefaultAccessor(ast.sym, ast.sym.Remove);
    }
    public virtual void interface_indexer_declaration(interface_indexer_declaration ast) {
        foreach (accessor_declaration d in ast.accessors)
            EmitMethod(d.sym, d.attrs, d.body, "specialname");
    }
    public virtual void interface_method_declaration(interface_method_declaration ast) {
        EmitMethod(ast.sym, ast.attrs, null, null);
    }
    public virtual void interface_property_declaration(interface_property_declaration ast) {
        EmitProperty(ast.sym, ast.attrs, ast.accessors);
    }
    public string ModuleName(string path) {
        string name = Path.GetFileNameWithoutExtension(path).ToLower();
        if (moduleMap.ContainsKey(name))
            name = moduleMap[name];
        return name;
    }
    public virtual void method_declaration(method_declaration ast) {
        EmitMethod(ast.sym, ast.attrs, ast.body, null);
    }
    public string MethodRef(Method m) {
        ClassType ty = m.GetType();
        return String.Format("{0}::{1}({2})", ClassRef(ty), Name(m), Signature(m, false));
    }
    public static string Name(Symbol m) {
        if (m is Method && ((Method)m).GetType().Name == m.Name)
            return m.IsStatic ? ".cctor" : ".ctor";
        return String.Format("'{0}'", m.Name);
    }
    public string Name(Type ty) {
             if (ty == T.Bool)   return "bool";
        else if (ty == T.Byte)   return "unsigned int8";
        else if (ty == T.Char)   return "char";
        else if (ty == T.Double) return "float64";
        //else if (ty == T.Decimal)return "decimal";
        else if (ty == T.Short)  return "int16";
        else if (ty == T.Int)    return "int32";
        else if (ty == T.Long)   return "int64";
        else if (ty == T.Object) return "object";
        else if (ty == T.SByte)  return "int8";
        else if (ty == T.Float)  return "float32";
        else if (ty == T.String) return "string";
        else if (ty == T.UShort) return "unsigned int16";
        else if (ty == T.UInt)   return "unsigned int32";
        else if (ty == T.ULong)  return "unsigned int64";
        else if (ty == T.Void)   return "void";
        else if (ty == T.IntPtr) return "native int";
        else if (ty == T.UIntPtr)return "native unsigned int";
        else if (ty is ManagedPointerType)
            return String.Format("{0}&", Name(((PointerType)ty).elementType));
        else if (ty is UnmanagedPointerType)
            return String.Format("{0}*", Name(((PointerType)ty).elementType));
        else if (ty is ArrayType && ((ArrayType)ty).rank == 1)
            return String.Format("{0}[]", Name(((ArrayType)ty).elementType));
        else if (ty is ArrayType)
            return String.Format("{0}[{1}]", Name(((ArrayType)ty).elementType),
                ILState.repl(",0...", ((ArrayType)ty).rank).Substring(1));
        else if (ty is EnumType || ty is StructType)
            return String.Format("value class {0}", ClassRef(ty));
        else if (ty is ClassType)
            return String.Format("class {0}", ClassRef(ty));
        else
            throw new ArgumentException(ty.ToString());
    }
    public virtual void namespace_declaration(namespace_declaration ast) {
        WriteLine(".namespace {0} {{", ast.sym.FullName);
        foreach (declaration d in ast.nb.declarations)
            declaration(d);
        WriteLine("}} // end of namespace {0}", ast.sym.FullName);
    }
    public virtual void operator_declaration(operator_declaration ast) {
        EmitMethod(ast.op.method, ast.attrs, ast.block, "specialname");
    }
    public virtual void property_declaration(property_declaration ast) {
        EmitProperty(ast.sym, ast.attrs, ast.decls);
    }
    public string Signature(Method m, bool showNames) {
        Signature sig = m.signature;
        StringBuilder sb = new StringBuilder();
        int i;
        for (i = 0; i < sig.ArgCount; i++) {
            if (i > 0)
                sb.Append(',');
            Formal f = sig[i];
            if (f.modifier != null && f.modifier.str == "out")
                sb.Append("[out] ");
            sb.Append(Name(f.Type));
            if (f.modifier != null)
                sb.Append('&');
            if (showNames)
                sb.AppendFormat(" '{0}'", f.Name);
        }
        if (m.Name == "set_Item") {
            Formal f = (Formal)m.locals["value"];
            if (i > 0)
                sb.Append(',');
            sb.Append(Name(f.Type));
            if (showNames)
                sb.AppendFormat(" '{0}'", f.Name);
        }
        return sb.ToString();
    }
    public string Signature(Method m) {
        return Signature(m, true);
    }
    public virtual void struct_declaration(struct_declaration ast) {
        EmitClassHead(ast.sym);
        WriteLine("{{");
        EmitClassBody(ast.attrs, ast.body);
        WriteLine("}} // end of struct {0}", ast.sym.FullName);
    }
    public virtual void variable_initializer(variable_initializer ast, Symbol sym, ILState g) {
        if (ast != null) {
            if (sym.IsInstance)
                g.this_access();
            g.variable_initializer(ast);
            g.EmitStore(sym);
        }
    }
    public virtual void Write(string fmt, params object[] args) {
        wr.Write(fmt, args);
    }
    public virtual void WriteLine() {
        wr.WriteLine();
    }
    public virtual void WriteLine(string fmt, params object[] args) {
        wr.WriteLine(fmt, args);
    }
}
