using System;
using System.Collections;
using System.IO;
using System.Diagnostics;
using System.Reflection;
using System.Reflection.Emit;
using System.Text;

public class csi_ilgen: ilgen {
    public new static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            new csi_ilgen(w, msg).compilation(ast);
        return ast;
    }

    public csi_ilgen(TextWriter wr, MessageWriter msg) : base(wr, msg) {
    }
    public override void constant_declaration(constant_declaration ast) {
        foreach (const_declarator x in ast.decls) {
            Constant f = x.sym;
            Write(".field ");
            EmitModifiers(f);
            Write("static literal ");
            Write("{0} '{1}'", Name(f.Type), f.Name);
        }
    }
}
