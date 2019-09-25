using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public class typeswitch_source: source {
    statementList defaultStmts = null;
    int next = 0;
    string id = null;
    new public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            (new typeswitch_source(w)).visit((AST)ast, 0);
        return ast;
    }
    public typeswitch_source(TextWriter w) : base(w) {}
    override public void switch_default(switch_default ast, int indent) {
        if (id == null)
            base.switch_default(ast, indent);
    }
    override public void break_statement(break_statement ast, int indent) {
        if (id != null)
            WriteLine("goto {0}_end;", indent, id);
        else
            base.break_statement(ast, indent);
    }
    public virtual void typeswitch_statement(typeswitch_statement ast, int indent) {
        id = String.Format("yy_{0}", ++next);
        WriteLine("{{", indent);
        Write("object {0} = ", indent + 1, id);
        visit(ast.expr);
        WriteLine(";");
        foreach (typeswitch_section x in ast.sections)
            typeswitch_section(x, indent + 1);
        if (defaultStmts != null) {
            foreach (statement x in defaultStmts)
                visit(x, indent + 1);
            defaultStmts = null;
        }
        WriteLine("{0}_end: ;", indent, id);
        WriteLine("}}", indent);
        id = null;
    }
    public virtual void typeswitch_section(typeswitch_section ast, int indent) {
        if (ast.labels[0] is switch_default) {
            defaultStmts = ast.stmts;
            return;
        }
        Write("if (", indent);
        for (int i = 0; i < ast.labels.Count; i++) {
            if (i > 0)
                Write(" || ");
            Write("{0} is ", id);
            visit(ast.labels[i], 0);
        }
        WriteLine(") {{");
        if (ast.id != null) {
            visit(ast.labels[0], indent + 1);
            Write(" {0} = (", ast.id.str);
            visit(ast.labels[0]);
            WriteLine("){0};", id);
        }
        foreach (statement x in ast.stmts)
            visit(x, indent + 1);
        WriteLine("}}", indent);
    }
    public virtual void typeswitch_label(typeswitch_label ast, int indent) {
        visit(ast.typelabel, indent);
    }
}
