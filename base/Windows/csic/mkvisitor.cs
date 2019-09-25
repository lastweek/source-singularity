using System;
using System.Collections;
using System.IO;
using System.Diagnostics;
using System.Reflection;
using SysType = System.Type;

public class visitor {
	static string classname = "CLASSNAME";
	static string args = "ARGTYPE ARG", argnames = "";
	static string returntype = "void";
	static string modifiers = "";
	static bool rewrite = false;
	readonly static string progname = Environment.GetCommandLineArgs()[0];
	public static void Main(string[] argv) {
		int nusage = 0;
		TextWriter w = Console.Out;
		for (int i = 0; i < argv.Length; i++)
			if (argv[i] == "-?") {
				Usage();
				return;
			} else if (argv[i] == "-rewrite") {
				rewrite = true;
				returntype = "AST";
				args = "";
				classname = "rewrite";
			} else if (argv[i] == "-class" && i+1 < argv.Length)
				classname = argv[++i];
			else if (argv[i] == "-args" && i+1 < argv.Length)
				args = argv[++i];
			else if (argv[i] == "-return" && i+1 < argv.Length)
				returntype = argv[++i];
			else if (argv[i] == "-out" && i+1 < argv.Length) {
				if (w != Console.Out)
					w.Close();
				try {
					w = new StreamWriter(argv[++i]);
				} catch (Exception e) {
					Console.Error.WriteLine("{0}: can't write \"{1}\": {2}", progname, argv[i], e.Message);
					w = Console.Out;					
				}
			} else if (argv[i] == "-public"   || argv[i] == "-virtual"
			       ||  argv[i] == "-private"  || argv[i] == "-static"
			       ||  argv[i] == "-sealed"   || argv[i] == "-internal"
			       ||  argv[i] == "-override" || argv[i] == "-abstract"
			       ||  argv[i] == "-protected"|| argv[i] == "-sealed"
			       ||  argv[i] == "-new")
				modifiers += argv[i].Substring(1) + " ";
			else {
				Console.Error.WriteLine("{0}: unrecognized option \"{1}\"", progname, argv[i]);
				if (nusage++ == 0)
					Usage();
			}
		if (args != "") {
			string[] parms = args.Split(',');
			foreach (string arg in parms)
				argnames += ", " + arg.Trim().Split(' ')[1];
			args = ", " + args;
		}
		Generate(w);
		if (w != Console.Out)
			w.Close();
	}
	static void Usage() {
		Console.Error.WriteLine("Usage: {0} [ option ]...\nOptions:", progname);
		foreach (string opt in new string[] {"-?", "-rewrite", "-class classname", "-args argument",
			"-return typename", "-out filename", "-public", "-virtual", "-private", "-static", "-sealed", "-internal",
			"-override", "-abstract", "-protected", "-sealed", "-new"})
				Console.Error.WriteLine("\t{0}", opt);
	}
	static Assembly baseAssembly = Assembly.Load("base");
	static SysType[] GetTypes() {
		return baseAssembly.GetExportedTypes();
	}
	static SysType GetType(string name) {
		return baseAssembly.GetType(name);
	}
	class compare : IComparer {
		int IComparer.Compare(object x, object y) {
			SysType u = (SysType)x, v = (SysType)y;
			return u.Name.CompareTo(v.Name);
		}
	}
	static void Generate(TextWriter w) {
		w.WriteLine(!rewrite ?
@"using System;
using System.IO;

public class {0} {{
	protected TextWriter w;
	public {0}(TextWriter w) {{
		this.w = w;
	}}" : @"using System;

public class {0} {{
	virtual public AST match(AST ast) {{
		return ast;
	}}", classname, args);
		ArrayList q = new ArrayList();
		foreach (SysType t in GetTypes())
			if (InheritsFrom(t, "AST"))
				q.Add(t);
		q.Sort(new compare());
		foreach (SysType t in q)
			ProcessType(t, w);
		GenerateVisit(GetTypes(), w);
		w.WriteLine("}");
	}
	static void GenerateVisit(SysType[] types, TextWriter w) {
		w.WriteLine("\tvirtual public {1} visit(AST ast{0}) {{", args, returntype);
		int n = 0;
		foreach (SysType t in types)
			if (t.BaseType != null && t.BaseType.Name == "AST") {
				if (returntype == "void")
					w.WriteLine("\t\t{2}if (ast is {0}) {0}(({0})ast{1});", t.Name, argnames, n > 0 ? "else " : "     ");
				else
					w.WriteLine("\t\tif (ast is {0}) return {0}(({0})ast{1});", t.Name, argnames);
				n++;
			}
		w.WriteLine("\t\t{0}throw new ArgumentException();", n > 0 ? "else " : "");
		w.WriteLine("\t}");
	}
	static bool IsAnnotated(FieldInfo f) {
		Attribute[] attrs = Attribute.GetCustomAttributes(f, true);
		return attrs.Length > 1 || attrs.Length == 1 && !MayBeNull(f);
	}
	static bool InheritsFrom(SysType t, string name) {
		while ((t = t.BaseType) != null)
			if (t.Name == name)
				return true;
		return false;
	}
	static void ProcessType(SysType t, TextWriter w) {
		if (t.IsAbstract && InheritsFrom(t, "AST"))
			ProcessAbstractType(t, w);
		else if (InheritsFrom(t, "AST"))
			ProcessConcreteType(t, w);
	}
	static void ProcessAbstractType(SysType t, TextWriter w) {
		w.WriteLine("\t{3}{2} {0}({0} ast{1}) {{", t.Name, args, returntype, modifiers);
		int n = 0;
		foreach (SysType u in GetTypes())
			if (u.BaseType == t) {
				w.Write("\t\t{1}if (ast is {0}) ", u.Name, n > 0 ? "else " : "     ");
				if (returntype != "void")
					w.Write("return ");
				w.WriteLine("{0}(({0})ast{1});", u.Name, argnames);
				n++;
			}
		w.WriteLine("\t\t{0}throw new ArgumentException();", n > 0 ? "else " : "");
		w.WriteLine("\t}");
	}
	static void ProcessConcreteType(SysType t, TextWriter w) {
		w.WriteLine("\t{3}{2} {0}({0} ast{1}) {{", t.Name, args, returntype, modifiers);
		foreach (FieldInfo f in t.GetFields())
			if (f.Name != "parent")
				ProcessField(f, w);
		if (rewrite)
			w.WriteLine("\t\treturn match(ast);");
		else if (returntype != "void")
			w.WriteLine("\t\treturn null;");
		w.WriteLine("\t}");
	}
	static bool MayBeNull(FieldInfo f) {
		return Attribute.GetCustomAttribute(f, baseAssembly.GetType("MayBeNullAttribute")) != null;
	}
	static void ProcessField(FieldInfo f, TextWriter w) {
		SysType t = f.FieldType;
		if (t.Name.EndsWith("List") && InheritsFrom(t, "CollectionBase")) {
			string elemname = t.Name.Substring(0, t.Name.Length - 4);
			SysType u = GetType(elemname);
			if (u != null && InheritsFrom(u, "AST") && !IsAnnotated(f)) {
				string indent = "\t\t";
				if (MayBeNull(f)) {
					w.WriteLine("\t\tif (ast.{0} != null)", f.Name);
					indent += "\t";
				}
				if (!rewrite) {
					w.WriteLine("{2}foreach ({0} x in ast.{1})", elemname, f.Name, indent);
					w.WriteLine("{2}\t{0}(x{1});", elemname, argnames, indent);
				} else {
					w.WriteLine("{1}for (int i = 0; i < ast.{0}.Count; i++)", f.Name, indent);
					w.WriteLine("{3}\tast.{1}[i] = ({0}){0}(ast.{1}[i]{2});", elemname, f.Name, argnames, indent);
				}
			} else if (!rewrite)
				CommentField(f, w);
		} else if (InheritsFrom(t, "AST") && !IsAnnotated(f)) {
			if (MayBeNull(f)) {
				w.WriteLine("\t\tif (ast.{0} != null)", f.Name);
				w.Write("\t");
			}
			if (!rewrite)
				w.WriteLine("\t\t{0}(ast.{1}{2});", t.Name, f.Name, argnames);
			else
				w.WriteLine("\t\tast.{1} = ({0}){0}(ast.{1}{2});", t.Name, f.Name, argnames);
		} else if (!rewrite)
			CommentField(f, w);
	}
	static void CommentField(FieldInfo f, TextWriter w) {
		w.Write("\t\t//");
		Attribute[] attrs = Attribute.GetCustomAttributes(f);
		if (attrs.Length > 0) {
			w.Write(" [");
			for (int i = 0; i < attrs.Length; i++) {
				if (i > 0)
					w.Write(",");
				string name = attrs[i].GetType().Name;
				if (name.EndsWith("Attribute"))
					name = name.Substring(0, name.Length-9);
				w.Write("{0}", name);
			}
			w.Write("]");
		}
		w.WriteLine(" {0} ast.{1}", f.FieldType.Name, f.Name);
	}
}