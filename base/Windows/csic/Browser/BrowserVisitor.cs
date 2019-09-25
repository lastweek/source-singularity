using System;
using System.IO;

namespace Browser {
	public class BrowserVisitor {
		public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
			compilation c = (compilation)ast;
			BrowserForm.Go(c);
			return c;
		}
	}
}

public class browser {
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		return Browser.BrowserVisitor.visit(ast, w, args, msg);
	}
}

public class objectbrowser {
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		Browser.ObjectBrowserForm.Go(ast);
		return ast;
	}
}
