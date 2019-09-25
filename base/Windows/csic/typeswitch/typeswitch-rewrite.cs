using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public class typeswitch_rewrite: rewrite {
    public static new compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            new typeswitch_rewrite(w).compilation(ast);
        return ast;
    }

    public typeswitch_rewrite(TextWriter w) : base(w) {}
    override public void statement(statement ast) {
        if (ast is typeswitch_statement) typeswitch_statement((typeswitch_statement)ast);
        else base.statement(ast);
    }
    void typeswitch_section(typeswitch_section ast) {
        foreach (statement s in ast.stmts)
            statement(s);
    }
    void typeswitch_statement(typeswitch_statement ast) {
        ast.expr = expression(ast.expr);
        foreach (typeswitch_section s in ast.sections)
            typeswitch_section(s);
    }
}
