using System;
using System.IO;
using System.Collections;
using System.Reflection;
using System.Reflection.Emit;

public class save {
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		if (msg.Count == 0 && ast is AssemblyBuilder) {
			AssemblyBuilder asm = (AssemblyBuilder)ast;
			if (args.Length > 0 && Path.GetExtension(args[0]) != null
			&& Path.GetExtension(args[0]).Length > 0)
				asm.Save(args[0]);
			else if (args.Length > 0)
				asm.Save(args[0] + ".exe");
			else
				asm.Save(asm.GetName().Name + ".exe");
		}
		return ast;
	}
}
