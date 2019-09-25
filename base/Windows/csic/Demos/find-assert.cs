// Search for assert patterns

using System;
using System.Collections;
using System.IO;

public class FindAssertion {
	//
	// Search for
	//	if (...) throw ...
	// 
	public static void doit(AST ast) {
		if (ast is if_statement
		&& ((if_statement)ast).thenpart is throw_statement
		&& ((if_statement)ast).elsepart == null)
			Console.WriteLine("{0}: Possible assertion", ast.begin);
	}
	public static void Main(string[] args) {
		foreach (string s in args)
			try {
				TextReader r = new StreamReader(s);
				object ast = Parser.parse(s, r);
				if (ast != null)
					((AST)ast).visit(new ASTVisitor(doit));
			} catch {}
	}
}
