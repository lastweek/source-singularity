using System;
using System.Collections;
using System.IO;
#if SUPPORT_DYNAMIC_LOADING_OF_VISITORS
using System.Reflection;
#endif

public class Compiler {
    public MessageWriter Msg;
    Imports imports;
    VisitorDelegateList visitors = new VisitorDelegateList();
    ArrayList visitorArgs = new ArrayList();

    public void AddLibraryPath(string path) {
        checkArg(path, "path");
        imports.Add(path);
    }
    public bool AddReference(string file) {
        checkArg(file, "file");
        return imports.Load(file);
    }
    public bool AddVisitor(VisitorDelegate visitor) {
        return AddVisitor(visitor, new string[0]);
    }
    public bool AddVisitor(VisitorDelegate visitor, string[] args) {
        visitors.Add(visitor);
        visitorArgs.Add(args.Clone());
        return true;
    }
#if SUPPORT_DYNAMIC_LOADING_OF_VISITORS
    public bool AddVisitor(System.Type type) {
        return AddVisitor(type, new string[0]);
    }
    public bool AddVisitor(System.Type type, string[] args) {
        checkArg(type, "classname");
        checkArg(args, "args");

        MethodInfo m = type.GetMethod("visit",
                                      new System.Type[] { typeof(compilation),
                                                          typeof(TextWriter),
                                                          typeof(string[]),
                                                          typeof(MessageWriter) });

        if (m != null && m.IsStatic && m.IsPublic && m.ReturnType == typeof(compilation)) {
            VisitorDelegate visitor
                = (VisitorDelegate)VisitorDelegate.CreateDelegate(typeof(VisitorDelegate), m);
            return AddVisitor(visitor, args);
        }
        Console.WriteLine("Couldn't find visit method on {0}", type);
        return false;
    }
#endif
    void checkArg(object arg, string name) {
        if (arg == null)
            throw new ArgumentNullException(name);
    }
    void compile(string[] inputs, compilation_unitList asts) {
        foreach (string f in inputs)
            try {
                TextReader r = new StreamReader(f);
                long time = Debug.Clock;
                object ast = Parser.parse(f, r);
                if (ast != null)
                    asts.Add((compilation_unit)ast);
                else
                    Msg.Count++;
                r.Close();
        } catch (Exception e) {
            Msg.Error("can't read \"{0}\": {1}", f, e.Message);
        }
    }
    public int Compile(string[] inputs, string[] argv) {
        checkArg(inputs, "inputs");
        compilation_unitList asts = new compilation_unitList();
        compile(inputs, asts);
        if (Msg.Count == 0 && asts.Count > 0)
            visit(argv, asts, Console.Out);
        return Msg.Count;
    }
    public int Compile(string[] inputs, string output, string[] argv) {
        checkArg(inputs, "inputs");
        checkArg(output, "output");
        compilation_unitList asts = new compilation_unitList();
        compile(inputs, asts);
        if (Msg.Count == 0 && asts.Count > 0) {
            TextWriter w;
            try {
                w = new StreamWriter(output);
            } catch (Exception e) {
                Msg.Error("can't write \"{0}\": {1}", output, e.Message);
                return Msg.Count;
            }
            visit(argv, asts, w);
            w.Close();
        }
        return Msg.Count;
    }
    public int Compile(TextReader input, TextWriter output, string[] argv) {
        checkArg(input, "input");
        long time = Debug.Clock;
        object ast = Parser.parse("<stream>", input);
        if (ast == null)
            Msg.Count++;
        if (Msg.Count == 0 && ast != null)
            visit(argv, compilation_unitList.New((compilation_unit)ast), output);
        return Msg.Count;
    }
    public Compiler() : this(new NullReader(), Console.Error) {}
    public Compiler(IImportReader reader) : this(reader, Console.Error) { }
    public Compiler(IImportReader reader, TextWriter errors) {
        Msg = new MessageWriter(errors);
        imports = new Imports(reader, Msg);
        imports.Add(".");
    }
#if SUPPORT_DYNAMIC_LOADING_OF_VISITORS
    public bool LoadVisitor(string classname) {
        return LoadVisitor(classname, null, new string[0]);
    }
    public bool LoadVisitor(string classname, string filename) {
        checkArg(filename, "filename");
        return LoadVisitor(classname, filename, new string[0]);
    }
    public bool LoadVisitor(string classname, string filename, string[] args) {
        checkArg(classname, "classname");
        checkArg(args, "args");
        Assembly asm;
        try {
            if (filename != null)
                asm = Assembly.LoadFrom(filename);
            else
                asm = Assembly.Load(classname);
        } catch {
            return false;
        }
        System.Type t;
        if (asm == null || (t = asm.GetType(classname)) == null)
            return false;
        return AddVisitor(t, args);
    }
#endif
    void visit(string[] argv, compilation_unitList asts, TextWriter w) {
        compilation ast = new compilation(argv, asts, imports.global);
        ast.link(null);
        for (int i = 0; i < visitors.Count && ast != null; i++) {
            VisitorDelegate visitor = visitors[i];
            string[] args = (string[])visitorArgs[i];

            ast = visitor(ast, w, args, Msg);
        }
    }
}
