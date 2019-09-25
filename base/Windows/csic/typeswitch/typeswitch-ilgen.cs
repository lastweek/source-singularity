using System;
using System.Collections;
using System.IO;
using System.Diagnostics;
using System.Reflection.Emit;

public class typeswitch_ilgen: ilgen {
    new public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            (new typeswitch_ilgen(w, msg)).compilation(ast);
        return ast;
    }
    public typeswitch_ilgen(TextWriter w, MessageWriter msg) : base(w, msg) {}

    override public ILState NewILState(ilgen parent) {
        return new typeswitch_ILState(parent);
    }
    public class typeswitch_ILState: ilgen.ILState {
        override public void statement(statement ast) {
            if (ast is typeswitch_statement) typeswitch_statement((typeswitch_statement)ast);
            else base.statement(ast);
        }
        public typeswitch_ILState(ilgen parent) : base(parent) {}
        void typeswitch_section(typeswitch_section ast, typeswitch_statement sw, ref typeswitch_section default_section) {
            if (ast.labels.Count == 1 && ast.labels[0] is switch_default) {
                default_section = ast;
                return;
            }
            int lab = genLabel(2);
            if (ast.id != null) {
                parent.comment(ast, "case {0} ({1}):", ast.sym.Type.Name, ast.id.str);
                EmitLoad(sw.var);
                Emit(OpCodes.Isinst, ast.sym.Type);
                int temp = newLocal(ast.sym.Type);
                EmitStore(temp);
                EmitLoad(temp);
                gotoLabel(OpCodes.Brfalse, lab + 1);
                EmitLoad(temp);
                EmitStore(ast.sym);
            } else {
                foreach (switch_label s in ast.labels) {
                    parent.comment(s, "case {0}:", ((typeswitch_label)s).typelabel.sym.Name);
                    EmitLoad(sw.var);
                    Emit(OpCodes.Isinst, ((typeswitch_label)s).typelabel.sym);
                    if (s == ast.labels[ast.labels.Count-1])
                        gotoLabel(OpCodes.Brfalse, lab + 1);
                    else
                        gotoLabel(OpCodes.Brtrue, lab);
                }
                defLabel(lab);
            }
            foreach (statement s in ast.stmts)
                statement(s);
            defLabel(lab + 1);
        }
        public virtual void typeswitch_statement(typeswitch_statement ast) {
            parent.comment(ast, "typeswitch ({0})", source.ToString(ast.expr));
            ast.lab = genLabel(3);
            ast.var = newLocal(ast.expr.typ);
            expression(ast.expr);
            EmitStore(ast.var);
            typeswitch_section default_section = null;
            foreach (typeswitch_section s in ast.sections)
                typeswitch_section(s, ast, ref default_section);
            defLabel(ast.lab);
            if (default_section != null) {
                parent.comment(default_section, "default:");
                foreach (statement s in default_section.stmts)
                    statement(s);
            }
            defLabel(ast.lab + 2);
        }
    }
}
