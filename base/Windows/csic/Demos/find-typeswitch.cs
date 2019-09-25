// Search for typeswitch patterns

using System;
using System.Collections;
using System.IO;

public class SearchAST {
	//
	// Search for
	//	if (... is ...) ...
	//	else if (... is ...) ...
	// 
	public static void doit(AST ast) {
		if (ast is if_statement) {
			if_statement ifst = (if_statement)ast;
			if (ifst.expr is is_expression && ifst.elsepart is if_statement
			&& ((if_statement)ifst.elsepart).expr is is_expression)
				Console.WriteLine("{0}: Possible typeswitch pattern", ast.begin);
		}
	}
	public static void Main(string[] args) {
		foreach (string s in args)
			try {
				TextReader r = new StreamReader(s);
				object ast = Parser.parse(s, r);
				if (ast != null) {
					Console.WriteLine("{0}:", s);
					((AST)ast).visit(new ASTVisitor(doit));
				}
			} catch {}
	}
}
