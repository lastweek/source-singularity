using System;
using System.Collections;
using System.IO;
using System.Diagnostics;
using System.Reflection;

public class source {
     public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            new source(w).visit((AST)ast);
        return ast;
    }

    const int topprec = 16;
    public TextWriter wr;
    public source(TextWriter w) { wr = w; }

    public static string ToString(AST ast) {
        source src = new source(new StringWriter());
        src.visit(ast);
        string result = ((StringWriter)src.wr).ToString();
        src.wr.Close();
        return result;
    }

    virtual public void accessor_declaration(accessor_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        if (ast.body != null) {
            Write("{0}", ast.id.str);
            statement(ast.body, indent + 1);
        } else
            WriteLine("{0};", ast.id.str);
    }
    virtual public void alias_directive(alias_directive ast, int indent) {
        Write("using {0} = ", indent, ast.id.str);
        visit(ast.name);
        WriteLine("");
    }
    virtual public void anonymous_method_expression(anonymous_method_expression ast, int indent) {
        Write("delegate ");
        if (ast.formals.Count > 0) {
            EmitParameters(ast.formals, null);
            Write(" ");
        }
        Write("{{");
        foreach (statement s in ((block_statement)ast.block).stmts) {
            Write(" ");
            visit(s);
        }
        Write(" }}");
    }
    virtual public void arglist_parameter(arglist_parameter ast, int indent) {
        Write("__arglist", indent);
    }
    virtual public void array_creation_expression1(array_creation_expression1 ast, int parent) {
        Write("new ");
        visit(ast.ty);
        Write("[");
        EmitexpressionList(ast.exprs);
        Write("]");
        if (ast.ranks != null)
            foreach (int rank in ast.ranks)
                Write("[{0}]", "".PadRight(rank, ','));
        if (ast.init != null)
            visit(ast.init);
    }
    virtual public void array_creation_expression2(array_creation_expression2 ast, int parent) {
        Write("new ");
        visit(ast.ty);
        Write(" ");
        visit(ast.init);
    }
    virtual public void array_initializer(array_initializer ast, int indent) {
        Write("{{ ");
        for (int i = 0; i < ast.a.Count; i++) {
            if (i > 0)
                Write(", ");
            visit(ast.a[i]);
        }
        Write(" }}");
    }
    virtual public void array_type(array_type ast, int indent) {
        visit(ast.ty, indent);
        Write("[{0}]", "".PadRight(ast.rank_specifier, ','));
    }
    virtual public void as_expression(as_expression ast, int parent) {
        int myprec = prec("as");
        if (myprec <= parent)
            parenexpr(ast, 0);
        else {
            visit(ast.expr, myprec);
            Write(" as ");
            visit(ast.ty);
        }
    }
    virtual public void assignment_expression(assignment_expression ast, int parent) {
        int myprec = prec("=");
        if (myprec <= parent)
            parenexpr(ast);
        else {
            visit(ast.e1, myprec);
            Write(" = ");
            visit(ast.e2, myprec);
        }
    }
    virtual public void attribute(attribute ast, int indent) {
        visit(ast.name);
        if (ast.arguments != null) {
            Write("(");
            EmitargumentList(ast.arguments.args);
            if (ast.arguments.namedargs.Count > 0) {
                if (ast.arguments.args.Count > 0)
                    Write(", ");
                for (int i = 0; i < ast.arguments.namedargs.Count; i++) {
                    if (i > 0)
                        Write(", ");
                    Write("{0}=", ast.arguments.namedargs[i].id.str);
                    visit(ast.arguments.namedargs[i].expr);
                }
            }
            Write(")");
        }
    }
    virtual public void attribute_section(attribute_section ast, int indent) {
        Write("[", indent);
        if (ast.target != null)
            Write("{0}: ", ast.target.str);
        foreach (attribute a in ast.attributes)
            visit(a);
        WriteLine("]");
    }
    virtual public void base_access(base_access ast, int parent) {
        Write("base");
    }
    virtual public void base_initializer(base_initializer ast, int indent) {
        if (ast.args.Count > 0) {
            Write(" : base");
            EmitargumentList(ast.args);
        }
    }
    virtual public void binary_declarator(binary_declarator ast, int indent) {
        visit(ast.ty, indent);
        Write(" operator {0}(", ast.op.str);
        visit(ast.t1);
        Write(" {0}, ", ast.id1.str);
        visit(ast.t2);
        Write(" {0})", ast.id2.str);
    }
    virtual public void binary_expression(binary_expression ast, int parent) {
        int myprec = prec(ast.op);
        if (myprec <= parent)
            parenexpr(ast);
        else {
            visit(ast.e1, myprec);
            Write(" {0} ", ast.op.str);
            visit(ast.e2, myprec);
        }
    }
    virtual public void block(block_statement ast, int indent) {
        WriteLine("{{");
        foreach (statement s in ast.stmts)
            visit(s, indent);
        Write("}}", indent - 1);
    }
    virtual public void block_statement(block_statement ast, int indent) {
        block(ast, indent);
        if (indent > 0)
            WriteLine("");
    }
    virtual public void bool_type(type ast, int indent) {
        Write("bool", indent);
    }
    virtual public void break_statement(break_statement ast, int indent) {
        Write("break", indent);
        Semicolon(indent);
    }
    virtual public void byte_type(type ast, int indent) {
        Write("byte", indent);
    }
    virtual public void cast_expression(cast_expression ast, int parent) {
        int myprec = prec("cast");
        if (myprec <= parent)
            parenexpr(ast);
        else {
            Write("(");
            visit(ast.ty);
            Write(")");
            visit(ast.expr, myprec);
        }
    }
    virtual public void catch_clause(catch_clause ast, int indent) {
        Write("catch (", indent);
        visit(ast.ty);
        if (ast.id != null)
            Write(" {0}", ast.id.str);
        Write(")");
        statement(ast.block, indent + 1);
    }
    virtual public void catch_clauses(catch_clauses ast, int indent) {
        foreach (catch_clause c in ast.specifics)
            visit(c, indent);
        if (ast.general != null) {
            WriteLine("catch", indent);
            visit(ast.general, indent + 1);
        }
    }
    virtual public void char_type(type ast, int indent) {
        Write("char", indent);
    }
    virtual public void checked_expression(checked_expression ast, int parent) {
        Write("checked (");
        visit(ast.expr, topprec);
        Write(")");
    }
    virtual public void checked_statement(checked_statement ast, int indent) {
        Write("checked", indent);
        statement(ast.stmt, indent + 1);
    }
    virtual public void class_declaration(class_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("class {0}", ast.id.str);
        EmitTypeList(ast.typeparams);
        if (ast.bases.Count > 0) {
            Write(": ");
            visit(ast.bases[(0)]);
            for (int i = 1; i < ast.bases.Count; i++) {
                Write(", ");
                visit(ast.bases[(i)]);
            }
        }
        EmitTypeConstraints(ast.constraints, indent + 1);
        WriteLine(" {{");
        foreach (declaration d in ast.body)
            visit(d, indent + 1);
        WriteLine("}}", indent);
    }
    protected void compilation(compilation ast, int indent) {
        foreach (compilation_unit x in ast.inputs)
            compilation_unit(x, indent);
    }
    virtual public void compilation_unit(compilation_unit ast, int indent) {
        foreach (using_directive u in ast.using_directives)
            visit(u, indent);
        EmitattributeSectionList(ast.attributes, indent);
        foreach (declaration d in ast.declarations) {
            WriteLine("");
            visit(d, indent);
        }
    }
    virtual public void compound_assignment_expression(compound_assignment_expression ast, int parent) {
        int myprec = prec("=");
        if (myprec <= parent)
            parenexpr(ast);
        else {
            visit(ast.e1, myprec);
            Write(" {0} ", ast.op.str);
            visit(ast.e2, myprec);
        }
    }
    virtual public void cond_expression(cond_expression ast, int parent) {
        int myprec = prec("?:");
        if (myprec <= parent)
            parenexpr(ast);
        else {
            visit(ast.cond, myprec);
            Write(" ? ");
            visit(ast.success, myprec);
            Write(" : ");
            visit(ast.failure, myprec);
        }
    }
    virtual public void const_declarator(const_declarator ast, int indent) {
        Write(" = ");
        visit(ast.expr);
    }
    virtual public void const_statement(const_statement ast, int indent) {
        Write("const ", indent);
        EmitdeclaratorList(ast.ty, ast.consts);
        Semicolon(indent);
    }
    virtual public void constant_declaration(constant_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("const ");
        EmitdeclaratorList(ast.ty, ast.decls);
        WriteLine(";");
    }
    virtual public void constructor_constraint(constructor_constraint ast, int indent) {
        Write("new ()");
    }
    virtual public void constructor_declaration(constructor_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("{0}", ast.decl.id.str);
        EmitParameters(ast.decl.f.fixeds, ast.decl.f.param);
        if (ast.decl.init != null)
            visit(ast.decl.init);
        if (ast.block != null)
            statement(ast.block, indent + 1);
        else
            WriteLine(";");
    }
    virtual public void continue_statement(continue_statement ast, int indent) {
        Write("continue", indent);
        Semicolon(indent);
    }
    virtual public void decimal_type(type ast, int indent) {
        Write("decimal", indent);
    }
    virtual public void delegate_declaration(delegate_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("delegate ");
        visit(ast.ty);
        Write(" {0}", ast.id.str);
        EmitTypeList(ast.typeparams);
        EmitParameters(ast.f.fixeds, ast.f.param);
        EmitTypeConstraints(ast.constraints, indent + 1);
        WriteLine(";");
    }
    virtual public void destructor_declaration(destructor_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write(" ~{0}()", ast.id.str);
        if (ast.block != null) {
            WriteLine("");
            visit(ast.block, indent + 1);
        } else
            WriteLine(";");
    }
    virtual public void do_statement(do_statement ast, int indent) {
        Write("do", indent);
        statement(ast.body, indent + 1, false);
        if (ast.body is block_statement)
            Write(" while (");
        else
            Write("while (", indent);
        visit(ast.expr);
        Write(")");
        Semicolon(indent);
    }
    virtual public void double_type(type ast, int indent) {
        Write("double", indent);
    }
    virtual public void element_access(element_access ast, int parent) {
        visit(ast.expr, topprec);
        EmitargumentList(ast.exprs, "[", "]");
    }
    protected void EmitargumentList(argumentList args) {
        EmitargumentList(args, "(", ")");
    }
    protected void EmitargumentList(argumentList args, string lparen, string rparen) {
        Write(lparen);
        for (int i = 0; i < args.Count; i++) {
            if (i > 0)
                Write(", ");
            if (args[i].kind != null)
                Write("{0} ", args[i].kind.str);
            visit(args[i].expr);
        }
        Write(rparen);
    }
    protected void EmitattributeSectionList(attribute_sectionList attrs, int indent) {
        foreach (attribute_section s in attrs)
            attribute_section(s, indent);
    }
    protected void EmitdeclaratorList(type ty, declaratorList decls) {
        visit(ty);
        Write(" ");
        for (int i = 0; i < decls.Count; i++) {
            if (i > 0)
                Write(", ");
            Write(decls[i].id.str);
            visit(decls[i]);
        }
    }
    protected void EmitexpressionList(expressionList exprs) {
        for (int i = 0; i < exprs.Count; i++) {
            if (i > 0)
                Write(", ");
            visit(exprs[i]);
        }
    }
    protected void EmitindexerParameters(parameterList fixeds, parameter param) {
        Write("this[");
        for (int i = 0; i < fixeds.Count; i++) {
            if (i > 0)
                Write(", ");
            visit(fixeds[i]);
        }
        if (param != null) {
            if (fixeds.Count > 0)
                Write(", ");
            visit(param);
        }
        Write("]");
    }
    protected void EmitModifiers(InputElementList mods, int indent, string suffix) {
        Indent(indent);
        if (mods.Count > 0) {
            bool partial = false;
            int n = 0;
            foreach (InputElement e in mods)
                if (e.str == "partial")
                    partial = true;
                else
                    Write(n++ > 0 ? " {0}" : "{0}", e.str);
            if (partial)
                Write(n++ > 0 ? " partial" : "partial");
            Write("{0}", suffix);
        }
    }
    protected void EmitParameters(parameterList fixeds, parameter param) {
        Write("(");
        for (int i = 0; i < fixeds.Count; i++) {
            if (i > 0)
                Write(", ");
            visit(fixeds[i]);
        }
        if (param != null) {
            if (fixeds.Count > 0)
                Write(", ");
            visit(param);
        }
        Write(")");
    }
    protected void EmitTypeConstraints(IList constraints, int indent) {
        for (int i = 0; i < constraints.Count; i++) {
            WriteLine("");
            Indent(indent);
            visit((AST)constraints[i]);
        }
    }
    protected void EmitTypeList(IList types) {
        if (types != null && types.Count > 0) {
            Write("<");
            for (int i = 0; i < types.Count; i++) {
                if (i > 0)
                    Write(", ");
                visit((AST)types[i]);
            }
            Write(">");
        }
    }
    virtual public void empty_statement(empty_statement ast, int indent) {
        Semicolon(indent);
    }
    virtual public void enum_declaration(enum_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("enum {0} ", ast.id.str);
        if (ast.ty != null) {
            Write(": ");
            visit(ast.ty);
        }
        WriteLine(" {{");
        foreach (enum_member_declaration d in ast.body) {
            EmitattributeSectionList(d.attrs, indent + 1);
            Write("{0}", indent + 1, d.id.str);
            if (d.expr != null) {
                Write("=");
                visit(d.expr);
            }
            WriteLine(",");
        }
        WriteLine("}};", indent);
    }
    virtual public void event_declaration1(event_declaration1 ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("event ");
        EmitdeclaratorList(ast.ty, ast.decls);
        WriteLine(";");
    }
    virtual public void event_declaration2(event_declaration2 ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("event ");
        visit(ast.ty);
        Write(" ");
        visit(ast.name);
        WriteLine(" {{");
        foreach (event_accessor a in ast.accessors) {
            EmitattributeSectionList(a.attrs, indent + 1);
            Write("{0}", indent + 1, a.id.str);
            statement(a.block, indent + 2);
        }
        WriteLine("}}", indent);
    }
    virtual public void event_declarator(event_declarator ast, int indent) {
        if (ast.init != null) {
            Write(" = ");
            visit(ast.init);
        }
    }
    virtual public void explicit_declarator(explicit_declarator ast, int indent) {
        Write("explicit operator ", indent);
        visit(ast.ty);
        Write("(");
        visit(ast.t1);
        Write(" {0})", ast.id1.str);
    }
    virtual public void expr_access(expr_access ast, int parent) {
        visit(ast.expr, topprec);
        Write(".{0}", ast.id.str);
        EmitTypeList(ast.typeargs);
    }
    virtual public void expr_initializer(expr_initializer ast, int indent) {
        visit(ast.expr);
    }
    virtual public void expression_statement(expression_statement ast, int indent) {
        Indent(indent);
        visit(ast.expr);
        Semicolon(indent);
    }
    virtual public void field_declaration(field_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        EmitdeclaratorList(ast.ty, ast.decls);
        WriteLine(";");
    }
    virtual public void field_declarator(field_declarator ast, int indent) {
        if (ast.init != null) {
            Write(" = ");
            visit(ast.init);
        }
    }
    virtual public void fixed_declarator(fixed_declarator ast, int indent) {
        Write(" = ", indent);
        visit(ast.expr);
    }
    virtual public void fixed_parameter(fixed_parameter ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        if (ast.mod != null) {
            Write("{0} ", indent, ast.mod.str);
            visit(ast.ty);
        } else
            visit(ast.ty, indent);
        Write(" {0}", ast.id.str);
    }
    virtual public void fixed_statement(fixed_statement ast, int indent) {
        Write("fixed (", indent);
        EmitdeclaratorList(ast.ty, ast.declarators);
        Write(")");
        statement(ast.body, indent + 1);
    }
    virtual public void float_type(type ast, int indent) {
        Write("float", indent);
    }
    virtual public void for_decl(for_decl ast, int indent) {
        EmitdeclaratorList(ast.decl.ty, ast.decl.vars);
    }
    virtual public void for_list(for_list ast, int indent) {
        EmitexpressionList(ast.exprs);
    }
    virtual public void for_statement(for_statement ast, int indent) {
        Write("for (", indent);
        if (ast.init != null)
            visit(ast.init);
        Write("; ");
        if (ast.cond != null)
            visit(ast.cond);
        Write("; ");
        EmitexpressionList(ast.iterators);
        Write(")");
        statement(ast.body, indent + 1);
    }
    virtual public void foreach_statement(foreach_statement ast, int indent) {
        Write("foreach (", indent);
        visit(ast.ty);
        Write(" {0} in ", ast.id.str);
        visit(ast.expr);
        Write(")");
        statement(ast.body, indent + 1);
    }
    virtual public void generic_interface_method_declaration(generic_interface_method_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.ty);
        Write(" {0} ", ast.id.str);
        EmitTypeList(ast.typeparams);
        EmitParameters(ast.f.fixeds, ast.f.param);
        EmitTypeConstraints(ast.constraints, indent + 1);
        WriteLine(";");
    }
    virtual public void generic_method_declaration(generic_method_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.ty);
        Write(" ");
        visit(ast.name);
        EmitTypeList(ast.typeparams);
        EmitParameters(ast.parms.fixeds, ast.parms.param);
        EmitTypeConstraints(ast.constraints, indent + 1);
        if (ast.body != null)
            statement(ast.body, indent + 1);
        else
            WriteLine(";");
    }
    virtual public void goto_case_statement(goto_case_statement ast, int indent) {
        Write("goto case ", indent);
        visit(ast.expr);
        Semicolon(indent);
    }
    virtual public void goto_default_statement(goto_default_statement ast, int indent) {
        Write("goto default", indent);
        Semicolon(indent);
    }
    virtual public void goto_statement(goto_statement ast, int indent) {
        Write("goto {0}", indent, ast.id.str);
        Semicolon(indent);
    }
    virtual public void if_statement(if_statement ast, int indent) {
        Indent(indent);
        ifstmt(ast, indent);
    }
    virtual public void ifstmt(if_statement ast, int indent) {
        Write("if (");
        visit(ast.expr);
        Write(")");
        if (ast.elsepart != null) {
            statement(ast.thenpart, indent + 1, false);
            if (ast.thenpart is block_statement)
                Write(" else");
            else
                Write("else", indent);
            if (ast.elsepart is if_statement) {
                Write(" ");
                ifstmt((if_statement)ast.elsepart, indent);
            } else
                statement(ast.elsepart, indent + 1);
        } else
            statement(ast.thenpart, indent + 1);
    }
    virtual public void implicit_cast_expression(implicit_cast_expression ast, int parent) {
        visit(ast.expr, parent);
    }
    virtual public void implicit_declarator(implicit_declarator ast, int indent) {
        Write("implicit operator ", indent);
        visit(ast.ty);
        Write("(");
        visit(ast.t1);
        Write(" {0})", ast.id1.str);
    }
    protected void Indent(int n) {
        if (n > 0)
            wr.Write("{0}", "".PadRight(n, '\t'));
    }
    virtual public void indexer_declaration(indexer_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.i.ty);
        Write(" ");
        if (ast.i.interfacename != null) {
            visit(ast.i.interfacename);
            Write(".");
        }
        EmitindexerParameters(ast.i.f.fixeds, ast.i.f.param);
        WriteLine(" {{", indent);
        foreach (declaration d in ast.accessors)
            visit(d, indent + 1);
        WriteLine("}}", indent);
    }
    virtual public void int_type(type ast, int indent) {
        Write("int", indent);
    }
    virtual public void interface_declaration(interface_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("interface {0}", ast.id.str);
        EmitTypeList(ast.typeparams);
        if (ast.interfaces.Count > 0) {
            Write(": ");
            visit(ast.interfaces[0]);
            for (int i = 1; i < ast.interfaces.Count; i++) {
                Write(", ");
                visit(ast.interfaces[i]);
            }
        }
        EmitTypeConstraints(ast.constraints, indent + 1);
        WriteLine(" {{");
        foreach (declaration d in ast.body)
            visit(d, indent + 1);
        WriteLine("}}", indent);
    }
    virtual public void interface_event_declaration(interface_event_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("event ");
        visit(ast.ty);
        WriteLine(" {0};", ast.id.str);
    }
    virtual public void interface_indexer_declaration(interface_indexer_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.ty);
        Write(" ");
        EmitindexerParameters(ast.f.fixeds, ast.f.param);
        WriteLine(" {{");
        foreach (accessor_declaration a in ast.accessors)
            visit(a, indent + 1);
        WriteLine("}}", indent);
    }
    virtual public void interface_method_declaration(interface_method_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.ty);
        Write(" {0}", ast.id.str);
        EmitParameters(ast.f.fixeds, ast.f.param);
        WriteLine(";");
    }
    virtual public void interface_property_declaration(interface_property_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.ty);
        Write(" {0} {{", ast.id.str);
        foreach (accessor_declaration a in ast.accessors)
            visit(a, indent + 1);
        WriteLine("}}", indent);
    }
    virtual public void invocation_expression(invocation_expression ast, int parent) {
        visit(ast.expr, topprec);
        EmitargumentList(ast.args);
    }
    virtual public void is_expression(is_expression ast, int parent) {
        int myprec = prec("is");
        if (myprec <= parent)
            parenexpr(ast, 0);
        else {
            visit(ast.expr, myprec);
            Write(" is ");
            visit(ast.ty);
        }
    }
    virtual public void labeled_statement(labeled_statement ast, int indent) {
        WriteLine("{0}:", ast.label.str);
        visit(ast.stmt, indent);
    }
    virtual public void literal(literal ast, int parent) {
        Write("{0}", ast.token.str);
    }
    virtual public void local_expression(local_expression ast, int indent) {
        visit(ast.expr);
    }
    virtual public void local_statement(local_statement ast, int indent) {
        Indent(indent);
        EmitdeclaratorList(ast.ty, ast.vars);
        Semicolon(indent);
    }
    virtual public void lock_statement(lock_statement ast, int indent) {
        Write("lock (", indent);
        visit(ast.expr);
        Write(")");
        statement(ast.body, indent + 1);
    }
    virtual public void long_type(type ast, int indent) {
        Write("long", indent);
    }
    virtual public void member_name(member_name ast, int indent) {
        if (ast.ty != null) {
            visit(ast.ty, indent);
            Write(".{0}", ast.id.str);
        } else
            Write("{0}", indent, ast.id.str);
    }
    virtual public void method_declaration(method_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.ty);
        Write(" ");
        visit(ast.name);
        EmitParameters(ast.parms.fixeds, ast.parms.param);
        if (ast.body != null)
            statement(ast.body, indent + 1);
        else
            WriteLine(";");
    }
    virtual public void dotted_name(dotted_name ast, int indent) {
        if (ast.left != null) {
            visit(ast.left);
            Write(".");
        }
        Write("{0}", ast.right.str);
        EmitTypeList(ast.typeargs);
    }
    virtual public void name_type(name_type ast, int indent) {
        Indent(indent);
        visit(ast.name);
    }
    virtual public void namespace_declaration(namespace_declaration ast, int indent) {
        WriteLine("namespace {0} {{", indent, ast.id);
        foreach (using_directive ud in ast.nb.ud)
            visit(ud, indent + 1);
        foreach (declaration d in ast.nb.declarations)
            visit(d, indent + 1);
        WriteLine("}}", indent);
    }
    virtual public void namespace_directive(namespace_directive ast, int indent) {
        WriteLine("using {0};", indent, ast.name);
    }
    virtual public void new_expression(new_expression ast, int parent) {
        Write("new ");
        visit(ast.ty);
        EmitargumentList(ast.args);
    }
    virtual public void object_type(type ast, int indent) {
        Write("object", indent);
    }
    virtual public void operator_declaration(operator_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.op);
        if (ast.block != null)
            statement(ast.block, indent + 1);
    }
    virtual public void params_parameter(params_parameter ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        Write("params ", indent);
        visit(ast.ty);
        Write(" {0}", ast.id.str);
    }
    virtual public void parenexpr(expression ast) {
        parenexpr(ast, 0);
    }
    virtual public void parenexpr(expression ast, int parent) {
        Write("(");
        visit(ast, parent);
        Write(")");
    }
    virtual public void pointer_access(pointer_access ast, int parent) {
        visit(ast.expr, topprec);
        Write("->{0}", ast.id.str);
    }
    virtual public void pointer_type(pointer_type ast, int indent) {
        visit(ast.ty, indent);
        Write("*");
    }
    virtual public void post_expression(post_expression ast, int parent) {
        visit(ast.expr, topprec);
        Write("{0}", ast.op.str);
    }
    virtual public void pre_expression(pre_expression ast, int parent) {
        int myprec = prec(ast.op.str + "e");
        if (myprec <= parent)
            parenexpr(ast);
        else {
            Write("{0}", ast.op.str);
            visit(ast.expr, myprec);
        }
    }
    public static int prec(string op) {
        switch (op) {
        case  "=": return 1;
        case "?:": return 2;
        case "||": return 3;
        case "&&": return 4;
        case  "|": return 5;
        case  "^": return 6;
        case  "&": return 7;
        case "==": case "!=": return 8;
        case "is": case "as": case ">=": case "<=": case "<": case ">": return 9;
        case ">>": case "<<": return 10;
        case  "+": case  "-": return 11;
        case  "*": case  "/": case "%": return 12;
        case "cast": return 13;
        case "--e": case "++e": return 14;
        case  "-e": case  "+e": case "*e": case "~e": case "!e": case "&e": return 15;
        default:
            Debug.Assert(false);
            return 0;
        }
    }
    public static int prec(InputElement op) {
        return prec(op.str);
    }
    virtual public void predefined_access(predefined_access ast, int indent) {
        Write("{0}.{1}", ast.predefined.str, ast.id.str);
        EmitTypeList(ast.typeargs);
    }
    virtual public void property_declaration(property_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        visit(ast.ty);
        Write(" ");
        visit(ast.name);
        WriteLine(" {{");
        foreach (accessor_declaration d in ast.decls)
            visit(d, indent + 1);
        WriteLine("}}", indent);
    }
    virtual public void qualified_alias_member(qualified_alias_member ast, int indent) {
        Write("{0}::", indent, ast.qualifier.str);
        dotted_name(ast, 0);
    }
    virtual public void qualified_name(qualified_name ast, int indent) {
        Write("{0}::", indent, ast.qualifier.str);
        simple_name(ast, 0);
    }
    virtual public void resource_decl(resource_decl ast, int indent) {
        Indent(indent);
        EmitdeclaratorList(ast.local.ty, ast.local.vars);
    }
    virtual public void resource_expr(resource_expr ast, int indent) {
        visit(ast.expr, indent);
    }
    virtual public void return_statement(return_statement ast, int indent) {
        Write("return", indent);
        if (ast.expr != null) {
            Write(" ");
            visit(ast.expr);
        }
        Semicolon(indent);
    }
    virtual public void sbyte_type(type ast, int indent) {
        Write("sbyte", indent);
    }
    protected void Semicolon(int indent) {
        if (indent > 0)
            WriteLine(";");
        else
            Write(";");
    }
    virtual public void short_type(type ast, int indent) {
        Write("short", indent);
    }
    virtual public void simple_name(simple_name ast, int parent) {
        Write("{0}", ast.id.str);
        EmitTypeList(ast.typeargs);
    }
    virtual public void sizeof_expression(sizeof_expression ast, int parent) {
        Write("sizeof (");
        visit(ast.ty);
        Write(")");
    }
    virtual public void stackalloc_initializer(stackalloc_initializer ast, int indent) {
        Write("stackalloc ", indent);
        visit(ast.ty);
        Write("[");
        visit(ast.expr);
        Write("]");
    }
    virtual public void statement(statement ast, int indent) {
        statement(ast, indent, true);
    }
    virtual public void statement(statement ast, int indent, bool newline) {
        if (ast is block_statement) {
            Write(" ");
            block((block_statement)ast, indent);
            if (newline)
                WriteLine("");
        } else {
            WriteLine("");
            visit(ast, indent);
        }
    }
    virtual public void string_type(type ast, int indent) {
        Write("string", indent);
    }
    virtual public void struct_declaration(struct_declaration ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        EmitModifiers(ast.mods, indent, " ");
        Write("struct {0}", ast.id.str);
        EmitTypeList(ast.typeparams);
        if (ast.interfaces.Count > 0) {
            Write(": ");
            visit(ast.interfaces[0]);
            for (int i = 1; i < ast.interfaces.Count; i++) {
                Write(", ");
                visit(ast.interfaces[i]);
            }
        }
        EmitTypeConstraints(ast.constraints, indent + 1);
        WriteLine(" {{");
        foreach (declaration d in ast.body)
            visit(d, indent + 1);
        WriteLine("}}", indent);
    }
    virtual public void switch_default(switch_default ast, int indent) {
        Write("default:", indent);
    }
    virtual public void switch_expression(switch_expression ast, int indent) {
        Write("case ", indent);
        visit(ast.expr);
        Write(":");
    }
    virtual public void switch_label(switch_label ast, int indent) {
        visit(ast, indent);
        WriteLine("");
    }
    virtual public void switch_statement(switch_statement ast, int indent) {
        Write("switch (", indent);
        visit(ast.expr);
        WriteLine(") {{");
        foreach (switch_section s in ast.sections) {
            foreach (switch_label l in s.labels)
                switch_label(l, indent);
            foreach (statement st in s.stmts)
                visit(st, indent + 1);
        }
        WriteLine("}}", indent);
    }
    virtual public void this_access(this_access ast, int parent) {
        Write("this");
    }
    virtual public void this_initializer(this_initializer ast, int indent) {
        Write(" : this");
        EmitargumentList(ast.args);
    }
    virtual public void throw_statement(throw_statement ast, int indent) {
        Write("throw", indent);
        if (ast.expr != null) {
            Write(" ");
            visit(ast.expr);
        }
        Semicolon(indent);
    }
    virtual public void try_statement(try_statement ast, int indent) {
        Write("try", indent);
        statement(ast.block, indent + 1);
        if (ast.catches != null)
            visit(ast.catches, indent);
        if (ast.finally_block != null) {
            Write("finally", indent);
            statement(ast.finally_block.block, indent + 1);
        }
    }
    virtual public void type_parameter(type_parameter ast, int indent) {
        EmitattributeSectionList(ast.attrs, indent);
        Write("{0}", ast.id.str);
    }
    virtual public void type_parameter_constraints_clause(type_parameter_constraints_clause ast, int indent) {
        Write("where {0}: ", ast.id.str);
        for (int i = 0; i < ast.constraints.Count; i++) {
            if (i > 0)
                Write(", ");
            visit(ast.constraints[i]);
        }
    }
    virtual public void typeof_expression(typeof_expression ast, int parent) {
        Write("typeof (");
        visit(ast.ty);
        Write(")");
    }
    virtual public void uint_type(type ast, int indent) {
        Write("uint", indent);
    }
    virtual public void ulong_type(type ast, int indent) {
        Write("ulong", indent);
    }
    virtual public void unary_declarator(unary_declarator ast, int indent) {
        visit(ast.ty, indent);
        Write(" operator {0}(", ast.op.str);
        visit(ast.t1);
        Write(" {0})", ast.id1.str);
    }
    virtual public void unary_expression(unary_expression ast, int parent) {
        int myprec = prec(ast.op.str + "e");
        if (myprec <= parent)
            parenexpr(ast);
        else {
            Write("{0}", ast.op.str);
            visit(ast.expr, myprec);
        }
    }
    virtual public void unchecked_expression(unchecked_expression ast, int parent) {
        Write("unchecked (");
        visit(ast.expr, topprec);
        Write(")");
    }
    virtual public void unchecked_statement(unchecked_statement ast, int indent) {
        Write("unchecked", indent);
        statement(ast.stmt, indent + 1);
    }
    virtual public void unsafe_statement(unsafe_statement ast, int indent) {
        Write("unsafe", indent);
        statement(ast.block, indent + 1);
    }
    virtual public void ushort_type(type ast, int indent) {
        Write("ushort", indent);
    }
    virtual public void using_statement(using_statement ast, int indent) {
        Write("using (", indent);
        visit(ast.r);
        Write(")");
        statement(ast.body, indent + 1);
    }
    virtual public void var_declarator(var_declarator ast, int indent) {
        if (ast.init != null) {
            Write(" = ");
            visit(ast.init);
        }
    }
    virtual public void visit(AST ast) {
        visit(ast, 0);
    }
    virtual public void visit(AST ast, int indent) {
        const BindingFlags bindingFlags = BindingFlags.Instance|BindingFlags.Public|BindingFlags.NonPublic;
        System.Type t = ast.GetType();
        Debug.Assert(t.IsClass);
        MethodInfo m;
        do {
            m = this.GetType().GetMethod(t.Name, bindingFlags);
            if (m != null)
                break;
            t = t.BaseType;
        } while (t != null);
        if (m != null)
            m.Invoke(this, new object[] { ast, indent });
        else if (indent == 0)
            Write("<{0}>", ast.GetType().Name);
        else
            WriteLine("<{0}>", indent, ast.GetType().Name);
    }
    virtual public void void_pointer_type(void_pointer_type ast, int indent) {
        Write("void*", indent);
    }
    virtual public void void_type(type ast, int indent) {
        Write("void", indent);
    }
    virtual public void while_statement(while_statement ast, int indent) {
        Write("while (", indent);
        visit(ast.expr);
        Write(")");
        statement(ast.body, indent + 1);
    }
    protected void Write(string fmt, int indent, params object[] args) {
        Indent(indent);
        wr.Write(fmt, args);
    }
    protected void Write(string fmt, params object[] args) {
        wr.Write(fmt, args);
    }
    protected void WriteLine(string fmt, int indent, params object[] args) {
        Indent(indent);
        wr.WriteLine(fmt, args);
    }
    protected void WriteLine(string fmt, params object[] args) {
        wr.WriteLine(fmt, args);
    }
    virtual public void yield_return_statement(yield_return_statement ast, int indent) {
        Write("yield return ", indent);
        visit(ast.expr);
        Semicolon(indent);
    }
    virtual public void yield_break_statement(yield_break_statement ast, int indent) {
        Write("yield break", indent);
        Semicolon(indent);
    }
}
