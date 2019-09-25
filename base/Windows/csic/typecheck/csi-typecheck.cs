using System;
using System.IO;
using System.Text;
using System.Collections;
using System.Diagnostics;

public class csi_typecheck: typecheck {
    public csi_typecheck(TextWriter w, MessageWriter msg): base(w, msg) {}

    new public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            (new csi_typecheck(w, msg)).compilation(ast);
        return ast;
    }

    override public void accessor_declaration(accessor_declaration ast, type ty) {
        if (ast.sym.IsAny("abstract", "extern") == 0 && ast.body == null) {
            ast.body = mk_return(ty, ast.sym);
            ast.body.link(ast);
        }
        base.accessor_declaration(ast, ty);
    }
    override public void constructor_declaration(constructor_declaration ast) {
        if (!ast.sym.Is("external") && ast.block == null) {
            ast.block = new empty_statement();
            ast.block.link(ast);
        }
        ast.decl.init = null;
        base.constructor_declaration(ast);
    }
    override public void method_declaration(method_declaration ast) {
        if (ast.sym.IsAny("abstract", "extern") == 0 && ast.body == null) {
            ast.body = mk_return(ast.ty, ast.sym);
            ast.body.link(ast);
        }
        base.method_declaration(ast);
    }
    public virtual statement mk_return(type ty, Method m) {
        if (m.Type == T.Void)
            return new empty_statement();
        expression expr = null;
        if (m.Type.FullName == "char")
            expr = new character_literal(new InputElement("'\0'"));
        else if (m.Type.IsNumeric && m.Type != T.Decimal)
            expr = new integer_literal(new InputElement("0"));
        else if (m.Type.IsReferenceType)
            expr = new null_literal(new InputElement("null"));
        else if (m.Type.IsValueType)
            expr = new new_expression(ty, argumentList.New());
        statement stmt = new return_statement(expr);
        stmt.method = m;
        return stmt;
    }
    override public void operator_declaration(operator_declaration ast) {
        if (ast.sym.IsAny("abstract", "extern") == 0 && ast.block == null) {
            ast.block = mk_return(ast.op.ty, ast.sym);
            ast.block.link(ast);
        }
        base.operator_declaration(ast);
    }
}
