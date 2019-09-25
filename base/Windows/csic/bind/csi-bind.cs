using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public class csi_bind {
    public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        NameSpace global = null;
        if (msg.Count == 0) {
            global = ast.global;
            bool nostdlib = false;
            foreach (string s in ((compilation)ast).args)
                if (s.Replace('/', '-').ToLower() == "-nostdlib") {
                    nostdlib = true;
                    break;
            }
            if (!nostdlib) {
                bind.import("System.dll", global.imports, msg);
            }
            (new csi_Pass1(msg)).compilation((compilation)ast, global.members);
        }
        if (msg.Count == 0)
            (new Pass2(msg)).compilation((compilation)ast, global.members);
        if (msg.Count == 0)
            (new csi_Pass3(msg)).compilation((compilation)ast, global.members);
        return ast;
    }
}

public class csi_Pass1: Pass1 {
    public csi_Pass1(MessageWriter msg) : base(msg) {}
    override public void const_statement(const_statement ast, SymbolTable bindings) {
        foreach (const_declarator x in ast.consts)
            x.sym.value = null; // undo setting "undefined"
    }
    override public void constant_declaration(constant_declaration ast, SymbolTable bindings) {
        base.constant_declaration(ast, bindings);
        foreach (const_declarator x in ast.decls)
            x.sym.value = null; // undo setting "undefined"
    }
    override public void method_body(Symbol t, AST ast, statement block, SymbolTable bindings) {
    }
    override public void using_directive(using_directive ast, SymbolTable bindings, SymbolList usingdirectives) {
        if (ast.parent is namespace_body)
            msg.Error(ast.begin, "using directives are not permitted inside namespaces in csi files");
        base.using_directive(ast, bindings, usingdirectives);
    }
}

public class csi_Pass3: Pass3 {
    public csi_Pass3(MessageWriter msg) : base(msg) {}
    override public void constant_declaration(constant_declaration ast, SymbolTable bindings) {
        attribute_sections(ast.attrs, bindings);
    }
}
