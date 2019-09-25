using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public class typeswitch_typecheck: typecheck {
    public typeswitch_typecheck(TextWriter w, MessageWriter msg) : base(w, msg) {}
    new public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            (new typeswitch_typecheck(w, msg)).compilation(ast);
        return ast;
    }

    override public void statement(statement ast) {
        if (ast is typeswitch_statement) typeswitch_statement((typeswitch_statement)ast);
        else base.statement(ast);
    }
    public virtual void typeswitch_label(typeswitch_label ast) {
        type(ast.typelabel);
    }
    public virtual void typeswitch_section(typeswitch_section ast) {
        foreach (switch_label x in ast.labels)
            if (x is typeswitch_label)
                typeswitch_label((typeswitch_label)x);
        foreach (statement x in ast.stmts)
            statement(x);
    }
    public virtual void typeswitch_statement(typeswitch_statement ast) {
        expression(ast.expr);
        foreach (typeswitch_section x in ast.sections)
            typeswitch_section(x);
    }
}
