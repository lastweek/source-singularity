using System;
using System.IO;
using System.Collections;
using System.Reflection;
using System.Reflection.Emit;

public class execute {
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		if (msg.Count == 0 && ast is AssemblyBuilder) {
			AssemblyBuilder asm = (AssemblyBuilder)ast;
			object o = null;
			MethodInfo m = null;
			int i;
			if (args.Length > 0 && (i = args[0].LastIndexOf('.')) > 0) {
				o = asm.CreateInstance(args[0].Substring(0, i));
				if (o != null)
					m = o.GetType().GetMethod(args[0].Substring(i+1));
			} else
				m = asm.EntryPoint.DeclaringType.GetMethod(asm.EntryPoint.Name);
			if (m != null && o != null)
				m.Invoke(o, null);
			else if (m != null)
				m.Invoke(null, null);
			else
				msg.Error("{0} not found", args.Length > 0 ? args[0] : "entry point");
		}
		return ast;
	}
}
