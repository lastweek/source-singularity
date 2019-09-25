using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public class typeswitch_bind {
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		NameSpace global = null;
		if (msg.Count == 0) {
			global = ((compilation)ast).global;
			bind.import("mscorlib.dll", global.imports, msg);
			bind.import("System.dll", global.imports, msg);
			(new typeswitch_Pass1(msg)).compilation((compilation)ast, global.members);
		}
		if (msg.Count == 0)
			(new Pass2(msg)).compilation((compilation)ast, global.members);
		if (msg.Count == 0)
			(new typeswitch_Pass3(msg)).compilation((compilation)ast, global.members);
		return ast;
	}
}

public class typeswitch_Pass1: Pass1 {
	public typeswitch_Pass1(MessageWriter msg) : base(msg) {}
	override public void break_statement(break_statement ast, SymbolTable bindings) {
		for (AST s = ast; s != null; s = s.parent) {
			if (s is finally_clause) {
				msg.Error(ast.begin, "invalid 'break' statement: 'break' cannot exit a finally block");
				return;
			}
			if (s is switch_statement || s is typeswitch_statement
			||  s is for_statement    || s is foreach_statement
			||  s is do_statement     || s is while_statement) {
				ast.stmt = (statement)s;
				return;
			}
		}
		msg.Error(ast.begin, "invalid 'break' statement");
	}
	override public void goto_default_statement(goto_default_statement ast, SymbolTable bindings) {
		for (AST s = ast; s != null; s = s.parent)
			if (s is finally_clause) {
				msg.Error(ast.begin, "invalid 'goto default' statement: 'goto default' cannot exit a finally block");
				return;
			} else if (s is switch_statement || s is typeswitch_statement) {
				ast.stmt = (statement)s;
				return;
			}
		msg.Error(ast.begin, "invalid 'goto default' statement");
	}
	override public void statement(statement ast, SymbolTable bindings) {
		if (ast is typeswitch_statement) typeswitch_statement((typeswitch_statement)ast, bindings);
		else base.statement(ast, bindings);
	}
	public virtual void typeswitch_section(typeswitch_section ast, SymbolTable bindings) {
		ast.block = new Block(bindings);
		statement s = null;
		foreach (statement x in ast.stmts)
			statement(s = x, ast.block.locals);
		if (!(s is return_statement || s is break_statement
		|| s is continue_statement  || s is goto_statement
		|| s is goto_case_statement || s is goto_default_statement
		|| s is throw_statement))
			msg.Error(s.begin, "missing break or other control flow statement in typeswitch case");
	}
	public void typeswitch_statement(typeswitch_statement ast, SymbolTable bindings) {
		foreach (typeswitch_section x in ast.sections)
			typeswitch_section(x, bindings);
	}
}

public class typeswitch_Pass3: Pass3 {
	public typeswitch_Pass3(MessageWriter msg) : base(msg) {}
	override public void statement(statement ast, SymbolTable bindings) {
		if (ast is typeswitch_statement) typeswitch_statement((typeswitch_statement)ast, bindings);
		else base.statement(ast, bindings);
	}
	public virtual void typeswitch_label(typeswitch_label ast, SymbolTable bindings) {
		type(ast.typelabel, bindings);
	}
	public virtual void typeswitch_section(typeswitch_section ast, SymbolTable bindings, ref bool hasdefault) {
		foreach (switch_label x in ast.labels)
			if (x is typeswitch_label)
				typeswitch_label((typeswitch_label)x, bindings);
			else if (x is switch_default) {
				if (hasdefault)
					msg.Error(ast.begin, "duplicate default label");
				hasdefault = true;
			}
		if (ast.id != null) {
			ast.sym = ast.block.AddLocal(ast.id, msg);
			ast.sym.Type = ((typeswitch_label)ast.labels[0]).typelabel.sym;
		}
		foreach (statement x in ast.stmts)
			statement(x, ast.block.locals);
	}
	public void typeswitch_statement(typeswitch_statement ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		bool hasdefault = false;
		foreach (typeswitch_section x in ast.sections)
			typeswitch_section(x, bindings, ref hasdefault);
	}
}
