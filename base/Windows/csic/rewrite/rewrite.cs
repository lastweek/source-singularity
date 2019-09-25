using System;
using System.IO;

public class rewrite {
    BuiltinTypes T;
    public static compilation visit(compilation ast, TextWriter w, string[] args, MessageWriter msg) {
        if (msg.Count == 0)
            new rewrite(w).compilation(ast);
        return ast;
    }

    protected TextWriter w;
    public rewrite(TextWriter w) {
        this.w = w;
    }

    static expression wrap(expression ast, int count) {
        if (count > 1)
            ast = new local_expression(ast);
        return ast;
    }

    public virtual void accessor_declaration(accessor_declaration ast) {
        if (ast.body != null)
            statement(ast.body);
    }
    public virtual void argumentList(argumentList args, int lvalue, int rvalue) {
        foreach (argument x in args)
            x.expr = expression(x.expr, lvalue, rvalue);
    }
    public virtual expression array_creation_expression1(array_creation_expression1 ast, int lvalue, int rvalue) {
        for (int i = 0; i < ast.exprs.Count; i++)
            ast.exprs[i] = expression(ast.exprs[i], lvalue, rvalue);
        if (ast.init != null)
            array_initializer(ast.init, lvalue, rvalue);
        return ast;
    }
    public virtual expression array_creation_expression2(array_creation_expression2 ast, int lvalue, int rvalue) {
        array_initializer(ast.init, lvalue, rvalue);
        return ast;
    }
    public virtual void array_initializer(array_initializer ast, int lvalue, int rvalue) {
        foreach (variable_initializer x in ast.a)
            variable_initializer(x, lvalue, rvalue);
    }
    public virtual expression as_expression(as_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
        return wrap(ast, rvalue);
    }
    public virtual expression assignment_expression(assignment_expression ast, int lvalue, int rvalue) {
        ast.e1 = expression(ast.e1, 1, 0);
        ast.e2 = expression(ast.e2, 0, ast.valueUsed ? 2 : 1);
        return wrap(ast, ast.valueUsed ? 2 : 1);
    }
    public virtual void base_initializer(base_initializer ast) {
        argumentList(ast.args, 0, 1);
    }
    public virtual expression binary_expression(binary_expression ast, int lvalue, int rvalue) {
        ast.e1 = expression(ast.e1);
        ast.e2 = expression(ast.e2);
        return wrap(ast, rvalue);
    }
    public virtual void block_statement(block_statement ast) {
        foreach (statement x in ast.stmts)
            statement(x);
    }
    public virtual void break_statement(break_statement ast) {
        ast.exitstry = exitstry(ast, ast.stmt);
    }
    public virtual expression cast_expression(cast_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
        return wrap(ast, rvalue);
    }
    public virtual void catch_clause(catch_clause ast) {
        statement(ast.block);
    }
    public virtual void catch_clauses(catch_clauses ast) {
        if (ast.general != null)
            statement(ast.general);
        foreach (catch_clause x in ast.specifics)
            catch_clause(x);
    }
    public virtual expression checked_expression(checked_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
        return ast;
    }
    public virtual void class_declaration(class_declaration ast) {
        declarationList(ast.body);
    }
    public virtual void compilation(compilation ast) {
        T = ast.global.Types;
        foreach (compilation_unit x in ast.inputs)
            compilation_unit(x);
    }
    public virtual void compilation_unit(compilation_unit ast) {
        declarationList(ast.declarations);
    }
    public virtual expression compound_assignment_expression(compound_assignment_expression ast, int lvalue, int rvalue) {
        ast.e1 = expression(ast.e1, 1, 1);
        ast.e2 = expression(ast.e2, 0, rvalue + 1);
        return ast;
    }
    public virtual expression cond_expression(cond_expression ast, int lvalue, int rvalue) {
        ast.cond = expression(ast.cond);
        ast.failure = expression(ast.failure);
        ast.success = expression(ast.success);
        return wrap(ast, rvalue);
    }
    public virtual void const_declarator(const_declarator ast) {
        ast.expr = expression(ast.expr);
    }
    public virtual void const_statement(const_statement ast) {
        foreach (declarator d in ast.consts)
            declarator(d);
    }
    public virtual void constant_declaration(constant_declaration ast) {
        foreach (declarator d in ast.decls)
            declarator(d);
    }
    public virtual void constructor_declaration(constructor_declaration ast) {
        if (ast.block != null)
            statement(ast.block);
        constructor_declarator(ast.decl);
    }
    public virtual void constructor_declarator(constructor_declarator ast) {
        if (ast.init != null)
            constructor_initializer(ast.init);
    }
    public virtual void constructor_initializer(constructor_initializer ast) {
             if (ast is base_initializer) base_initializer((base_initializer)ast);
        else if (ast is this_initializer) this_initializer((this_initializer)ast);
        else throw new ArgumentException();
    }
    public virtual void continue_statement(continue_statement ast) {
        ast.exitstry = exitstry(ast, ast.stmt);
    }
    public virtual void declaration(declaration ast) {
             if (ast is class_declaration) class_declaration((class_declaration)ast);
        else if (ast is constant_declaration) constant_declaration((constant_declaration)ast);
        else if (ast is constructor_declaration) constructor_declaration((constructor_declaration)ast);
        else if (ast is delegate_declaration) ;
        else if (ast is destructor_declaration) destructor_declaration((destructor_declaration)ast);
        else if (ast is enum_declaration) ;
        else if (ast is event_declaration1) event_declaration1((event_declaration1)ast);
        else if (ast is event_declaration2) event_declaration2((event_declaration2)ast);
        else if (ast is field_declaration) field_declaration((field_declaration)ast);
        else if (ast is indexer_declaration) indexer_declaration((indexer_declaration)ast);
        else if (ast is interface_declaration) ;
        else if (ast is interface_event_declaration) ;
        else if (ast is interface_indexer_declaration) ;
        else if (ast is interface_method_declaration) ;
        else if (ast is interface_property_declaration) ;
        else if (ast is method_declaration) method_declaration((method_declaration)ast);
        else if (ast is namespace_declaration) namespace_declaration((namespace_declaration)ast);
        else if (ast is operator_declaration) operator_declaration((operator_declaration)ast);
        else if (ast is property_declaration) property_declaration((property_declaration)ast);
        else if (ast is struct_declaration) struct_declaration((struct_declaration)ast);
        else throw new ArgumentException();
    }
    public virtual void declarationList(declarationList decls) {
        foreach (declaration d in decls)
            declaration(d);
    }
    public virtual void declarator(declarator ast) {
             if (ast is const_declarator) const_declarator((const_declarator)ast);
        else if (ast is event_declarator) event_declarator((event_declarator)ast);
        else if (ast is field_declarator) field_declarator((field_declarator)ast);
        else if (ast is fixed_declarator) fixed_declarator((fixed_declarator)ast);
        else if (ast is var_declarator) var_declarator((var_declarator)ast);
        else throw new ArgumentException();
    }
    public virtual void destructor_declaration(destructor_declaration ast) {
        if (ast.block != null)
            statement(ast.block);
    }
    public virtual void do_statement(do_statement ast) {
        statement(ast.body);
        ast.expr = expression(ast.expr);
    }
    public virtual expression element_access(element_access ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, lvalue + rvalue);
        argumentList(ast.exprs, lvalue, lvalue + rvalue);
        return ast;
    }
    public virtual void event_accessor(event_accessor ast) {
        statement(ast.block);
    }
    public virtual void event_declaration1(event_declaration1 ast) {
        foreach (declarator d in ast.decls)
            declarator(d);
    }
    public virtual void event_declaration2(event_declaration2 ast) {
        foreach (event_accessor e in ast.accessors)
            event_accessor(e);
    }
    public virtual void event_declarator(event_declarator ast) {
        if (ast.init != null)
            variable_initializer(ast.init, 0, 1);
    }
    public virtual bool exitstry(statement ast, AST lca) {
        for (AST s = ast; s != null && s != lca; s = s.parent)
            if (is_try(s))
                return true;
        return false;
    }
    public virtual expression expr_access(expr_access ast, int lvalue, int rvalue) {
        if (ast.sym is Type)
            return ast;
        ast.expr = expression(ast.expr, lvalue, rvalue);
        return wrap(ast, rvalue);
    }
    public virtual void expr_initializer(expr_initializer ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
    }
    public virtual expression expression(expression ast) {
        return expression(ast, 0, 1);
    }
    public virtual expression expression(expression ast, int lvalue, int rvalue) {
             if (ast is array_creation_expression1) return array_creation_expression1((array_creation_expression1)ast, lvalue, rvalue);
        else if (ast is array_creation_expression2) return array_creation_expression2((array_creation_expression2)ast, lvalue, rvalue);
        else if (ast is as_expression) return as_expression((as_expression)ast, lvalue, rvalue);
        else if (ast is assignment_expression) return assignment_expression((assignment_expression)ast, lvalue, rvalue);
        else if (ast is base_access) return ast;
        else if (ast is binary_expression) return binary_expression((binary_expression)ast, lvalue, rvalue);
        else if (ast is literal) return ast;
        else if (ast is cast_expression) return cast_expression((cast_expression)ast, lvalue, rvalue);
        else if (ast is checked_expression) return checked_expression((checked_expression)ast, lvalue, rvalue);
        else if (ast is compound_assignment_expression) return compound_assignment_expression((compound_assignment_expression)ast, lvalue, rvalue);
        else if (ast is cond_expression) return cond_expression((cond_expression)ast, lvalue, rvalue);
        else if (ast is element_access) return element_access((element_access)ast, lvalue, rvalue);
        else if (ast is member_access) return member_access((member_access)ast, lvalue, rvalue);
        else if (ast is implicit_cast_expression) return implicit_cast_expression((implicit_cast_expression)ast, lvalue, rvalue);
        else if (ast is invocation_expression) return invocation_expression((invocation_expression)ast, lvalue, rvalue);
        else if (ast is is_expression) return is_expression((is_expression)ast, lvalue, rvalue);
        else if (ast is new_expression) return new_expression((new_expression)ast, lvalue, rvalue);
        else if (ast is post_expression) return post_expression((post_expression)ast, lvalue, rvalue);
        else if (ast is pre_expression) return pre_expression((pre_expression)ast, lvalue, rvalue);
        else if (ast is simple_name) return simple_name((simple_name)ast, lvalue, rvalue);
        else if (ast is sizeof_expression) return sizeof_expression((sizeof_expression)ast, lvalue, rvalue);
        else if (ast is this_access) return ast;
        else if (ast is typeof_expression) return ast;
        else if (ast is unary_expression) return unary_expression((unary_expression)ast, lvalue, rvalue);
        else if (ast is unchecked_expression) return unchecked_expression((unchecked_expression)ast, lvalue, rvalue);
        else throw new ArgumentException();
    }
    public virtual void expression_statement(expression_statement ast) {
        ast.expr = expression(ast.expr, 0, 0);
    }
    public virtual void field_declaration(field_declaration ast) {
        foreach (declarator d in ast.decls)
            declarator(d);
    }
    public virtual void field_declarator(field_declarator ast) {
        if (ast.init != null)
            variable_initializer(ast.init, 0, 1);
    }
    public virtual void finally_clause(finally_clause ast) {
        statement(ast.block);
    }
    public virtual void fixed_declarator(fixed_declarator ast) {
        ast.expr = expression(ast.expr);
    }
    public virtual void fixed_statement(fixed_statement ast) {
        statement(ast.body);
        foreach (declarator d in ast.declarators)
            declarator(d);
    }
    public virtual void for_decl(for_decl ast) {
        local_statement(ast.decl);
    }
    public virtual void for_init(for_init ast) {
             if (ast is for_decl) for_decl((for_decl)ast);
        else if (ast is for_list) for_list((for_list)ast);
        else throw new ArgumentException();
    }
    public virtual void for_list(for_list ast) {
        for (int i = 0; i < ast.exprs.Count; i++)
            ast.exprs[i] = expression(ast.exprs[i], 0, 0);
    }
    public virtual void for_statement(for_statement ast) {
        statement(ast.body);
        if (ast.cond != null)
            ast.cond = expression(ast.cond);
        if (ast.init != null)
            for_init(ast.init);
        for (int i = 0; i < ast.iterators.Count; i++)
            ast.iterators[i] = expression(ast.iterators[i], 0, 0);
    }
    public virtual void foreach_statement(foreach_statement ast) {
        statement(ast.body);
        ast.expr = expression(ast.expr);
    }
    public virtual void goto_case_statement(goto_case_statement ast) {
        ast.exitstry = exitstry(ast, ast.stmt);
    }
    public virtual void goto_default_statement(goto_default_statement ast) {
        ast.exitstry = exitstry(ast, ast.stmt);
    }
    public virtual void goto_statement(goto_statement ast) {
        ast.exitstry = exitstry(ast, AST.leastCommonAncestor(ast.target, ast));
    }
    public virtual void if_statement(if_statement ast) {
        if (ast.elsepart != null)
            statement(ast.elsepart);
        ast.expr = expression(ast.expr);
        statement(ast.thenpart);
    }
    public virtual expression implicit_cast_expression(implicit_cast_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
        return wrap(ast, rvalue);
    }
    public virtual void indexer_declaration(indexer_declaration ast) {
        foreach (accessor_declaration d in ast.accessors)
            accessor_declaration(d);
    }
    public virtual expression invocation_expression(invocation_expression ast, int lvalue, int rvalue) {
        argumentList(ast.args, 0, 1);
        ast.expr = expression(ast.expr);
        return wrap(ast, rvalue);
    }
    public virtual expression is_expression(is_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr);
        return wrap(ast, rvalue);
    }
    public virtual bool is_try(AST s) {
        if (s is try_statement   || s is catch_clauses
        ||  s is using_statement || s is lock_statement)
            return true;
        if (s is foreach_statement) {
            foreach_statement ast = (foreach_statement)s;
            if (ast.expr.typ is ArrayType)
                return false;
            if (ast.GetEnumerator.Type.Implements(T.IDisposable)
            || !ast.GetEnumerator.Type.Is("sealed"))
                return true;
        }
        return false;
    }
    public virtual void local_statement(local_statement ast) {
        foreach (declarator d in ast.vars)
            declarator(d);
    }
    public virtual void lock_statement(lock_statement ast) {
        statement(ast.body);
        ast.expr = expression(ast.expr);
    }
    public virtual expression member_access(member_access ast, int lvalue, int rvalue) {
             if (ast is expr_access) return expr_access((expr_access)ast, lvalue, rvalue);
        else if (ast is pointer_access) return pointer_access((pointer_access)ast, lvalue, rvalue);
        else if (ast is predefined_access) return predefined_access((predefined_access)ast, lvalue, rvalue);
        else throw new ArgumentException();
    }
    public virtual void method_declaration(method_declaration ast) {
        if (ast.body != null)
            statement(ast.body);
    }
    public virtual void namespace_declaration(namespace_declaration ast) {
        declarationList(ast.nb.declarations);
    }
    public virtual expression new_expression(new_expression ast, int lvalue, int rvalue) {
        argumentList(ast.args, lvalue, rvalue);
        return wrap(ast, rvalue);
    }
    public virtual void operator_declaration(operator_declaration ast) {
        if (ast.block != null)
            statement(ast.block);
    }
    public virtual expression pointer_access(pointer_access ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
        return ast;
    }
    public virtual expression post_expression(post_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, 1, 1);
        return wrap(ast, rvalue);
    }
    public virtual expression pre_expression(pre_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, 1, 1);
        return wrap(ast, rvalue);
    }
    public virtual expression predefined_access(predefined_access ast, int lvalue, int rvalue) {
        return wrap(ast, rvalue);
    }
    public virtual void property_declaration(property_declaration ast) {
        foreach (accessor_declaration d in ast.decls)
            accessor_declaration(d);
    }
    public virtual void resource(resource ast) {
             if (ast is resource_decl) resource_decl((resource_decl)ast);
        else if (ast is resource_expr) resource_expr((resource_expr)ast);
        else throw new ArgumentException();
    }
    public virtual void resource_decl(resource_decl ast) {
        local_statement(ast.local);
    }
    public virtual void resource_expr(resource_expr ast) {
        ast.expr = expression(ast.expr);
    }
    public virtual void return_statement(return_statement ast) {
        if (ast.expr != null)
            ast.expr = expression(ast.expr);
        ast.exitstry = exitstry(ast, null);
    }
    public virtual expression simple_name(simple_name ast, int lvalue, int rvalue) {
        if (ast.sym is EnumMember || ast.sym is Type)
            return ast;
        return wrap(ast, rvalue);
    }
    public virtual expression sizeof_expression(sizeof_expression ast, int lvalue, int rvalue) {
        return ast;
    }
    public virtual void stackalloc_initializer(stackalloc_initializer ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
    }
    public virtual void statement(statement ast) {
             if (ast is block_statement) block_statement((block_statement)ast);
        else if (ast is break_statement) break_statement((break_statement)ast);
        else if (ast is checked_statement) statement(((checked_statement)ast).stmt);
        else if (ast is const_statement) const_statement((const_statement)ast);
        else if (ast is continue_statement) break_statement((break_statement)ast);
        else if (ast is do_statement) do_statement((do_statement)ast);
        else if (ast is empty_statement) ;
        else if (ast is expression_statement) expression_statement((expression_statement)ast);
        else if (ast is fixed_statement) fixed_statement((fixed_statement)ast);
        else if (ast is for_statement) for_statement((for_statement)ast);
        else if (ast is foreach_statement) foreach_statement((foreach_statement)ast);
        else if (ast is goto_case_statement) goto_case_statement((goto_case_statement)ast);
        else if (ast is goto_default_statement)  goto_default_statement((goto_default_statement)ast);
        else if (ast is goto_statement) goto_statement((goto_statement)ast);
        else if (ast is if_statement) if_statement((if_statement)ast);
        else if (ast is labeled_statement) statement(((labeled_statement)ast).stmt);
        else if (ast is local_statement) local_statement((local_statement)ast);
        else if (ast is lock_statement) lock_statement((lock_statement)ast);
        else if (ast is return_statement) return_statement((return_statement)ast);
        else if (ast is switch_statement) switch_statement((switch_statement)ast);
        else if (ast is throw_statement) throw_statement((throw_statement)ast);
        else if (ast is try_statement) try_statement((try_statement)ast);
        else if (ast is unchecked_statement) statement(((unchecked_statement)ast).stmt);
        else if (ast is unsafe_statement) statement(((unsafe_statement)ast).block);
        else if (ast is using_statement) using_statement((using_statement)ast);
        else if (ast is while_statement) while_statement((while_statement)ast);
        else throw new ArgumentException();
    }
    public virtual void struct_declaration(struct_declaration ast) {
        declarationList(ast.body);
    }
    public virtual void switch_expression(switch_expression ast) {
        ast.expr = expression(ast.expr);
    }
    public virtual void switch_section(switch_section ast) {
        foreach (statement x in ast.stmts)
            statement(x);
    }
    public virtual void switch_statement(switch_statement ast) {
        ast.expr = expression(ast.expr);
        foreach (switch_section s in ast.sections)
            switch_section(s);
    }
    public virtual void this_initializer(this_initializer ast) {
        argumentList(ast.args, 0, 1);
    }
    public virtual void throw_statement(throw_statement ast) {
        if (ast.expr != null)
            ast.expr = expression(ast.expr);
    }
    public virtual void try_statement(try_statement ast) {
        statement(ast.block);
        if (ast.catches != null)
            catch_clauses(ast.catches);
        if (ast.finally_block != null)
            finally_clause(ast.finally_block);
    }
    public virtual expression unary_expression(unary_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr);
        return wrap(ast, rvalue);
    }
    public virtual expression unchecked_expression(unchecked_expression ast, int lvalue, int rvalue) {
        ast.expr = expression(ast.expr, lvalue, rvalue);
        return ast;
    }
    public virtual void using_statement(using_statement ast) {
        statement(ast.body);
        resource(ast.r);
    }
    public virtual void var_declarator(var_declarator ast) {
        if (ast.init != null)
            variable_initializer(ast.init, 0, 1);
    }
    public virtual void variable_initializer(variable_initializer ast, int lvalue, int rvalue) {
             if (ast is array_initializer) array_initializer((array_initializer)ast, lvalue, rvalue);
        else if (ast is expr_initializer) expr_initializer((expr_initializer)ast, lvalue, rvalue);
        else if (ast is stackalloc_initializer) stackalloc_initializer((stackalloc_initializer)ast, lvalue, rvalue);
        else throw new ArgumentException();
    }
    public virtual void while_statement(while_statement ast) {
        statement(ast.body);
        ast.expr = expression(ast.expr);
    }
}
