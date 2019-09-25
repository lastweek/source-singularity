using System;
using System.IO;
using System.Collections;

public class Pair {
    object first, second;
    public Pair(object first, object second) {
        this.first = first;
        this.second = second;
    }
    public object First {
        get { return first; }
        set { first = value; }
    }
    public object Second {
        get { return second; }
        set { second = value; }
    }
}

public class sortmembers {
    public static compilation visit(compilation ast, TextWriter w, string[] lists, MessageWriter msg) {
        (new sortmembers()).compilation(ast, null);
        return ast;
    }
    class compare : IComparer {
        int IComparer.Compare(object x, object y) {
            Pair u = (Pair)x, v = (Pair)y;
            return ((string)u.First).CompareTo((string)v.First);
        }
    }
    declarationList Sort(ArrayList q) {
        q.Sort(new compare());
        declarationList decls = new declarationList();
        foreach (Pair x in q)
            decls.Add((declaration)x.Second);
        return decls;
    }
    void class_declaration(class_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
        list = new ArrayList();
        foreach (declaration x in ast.body)
            declaration(x, list);
        ast.body = Sort(list);
    }
    void compilation(compilation ast, ArrayList list) {
        list = new ArrayList();
        foreach (compilation_unit x in ast.inputs)
            compilation_unit(x, list);
    }
    void compilation_unit(compilation_unit ast, ArrayList list) {
        foreach (declaration x in ast.declarations)
            declaration(x, list);
        ast.declarations = Sort(list);
    }
    void constant_declaration(constant_declaration ast, ArrayList list) {
        foreach (declarator x in ast.decls)
            list.Add(new Pair(x.id.str, ast));
    }
    void constructor_declaration(constructor_declaration ast, ArrayList list) {
        list.Add(new Pair(((constructor_declarator)ast.decl).id.str, ast));
    }
    void declaration(declaration ast, ArrayList list) {
        if (ast is namespace_declaration) { namespace_declaration((namespace_declaration)ast, list); return; }
        if (ast is constant_declaration) { constant_declaration((constant_declaration)ast, list); return; }
        if (ast is field_declaration) { field_declaration((field_declaration)ast, list); return; }
        if (ast is method_declaration) { method_declaration((method_declaration)ast, list); return; }
        if (ast is property_declaration) { property_declaration((property_declaration)ast, list); return; }
        if (ast is event_declaration1) { event_declaration1((event_declaration1)ast, list); return; }
        if (ast is event_declaration2) { event_declaration2((event_declaration2)ast, list); return; }
        if (ast is indexer_declaration) { indexer_declaration((indexer_declaration)ast, list); return; }
        if (ast is operator_declaration) { operator_declaration((operator_declaration)ast, list); return; }
        if (ast is constructor_declaration) { constructor_declaration((constructor_declaration)ast, list); return; }
        if (ast is destructor_declaration) { destructor_declaration((destructor_declaration)ast, list); return; }
        if (ast is struct_declaration) { struct_declaration((struct_declaration)ast, list); return; }
        if (ast is interface_declaration) { interface_declaration((interface_declaration)ast, list); return; }
        if (ast is interface_method_declaration) { interface_method_declaration((interface_method_declaration)ast, list); return; }
        if (ast is interface_property_declaration) { interface_property_declaration((interface_property_declaration)ast, list); return; }
        if (ast is interface_event_declaration) { interface_event_declaration((interface_event_declaration)ast, list); return; }
        if (ast is interface_indexer_declaration) { interface_indexer_declaration((interface_indexer_declaration)ast, list); return; }
        if (ast is enum_declaration) { enum_declaration((enum_declaration)ast, list); return; }
        if (ast is class_declaration) { class_declaration((class_declaration)ast, list); return; }
        if (ast is delegate_declaration) { delegate_declaration((delegate_declaration)ast, list); return; }
        throw new ArgumentException();
    }
    void delegate_declaration(delegate_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
    }
    void destructor_declaration(destructor_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
    }
    void enum_declaration(enum_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
    }
    void event_declaration1(event_declaration1 ast, ArrayList list) {
        foreach (event_declarator x in ast.decls)
            list.Add(new Pair(x.id.str, ast));
    }
    void event_declaration2(event_declaration2 ast, ArrayList list) {
        list.Add(new Pair(member_name(ast.name), ast));
    }
    void field_declaration(field_declaration ast, ArrayList list) {
        foreach (field_declarator x in ast.decls)
            list.Add(new Pair(x.id.str, ast));
    }
    void indexer_declaration(indexer_declaration ast, ArrayList list) {
        list.Add(new Pair("this", ast));
    }
    void interface_declaration(interface_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
        list = new ArrayList();
        foreach (declaration x in ast.body)
            declaration(x, list);
        ast.body = Sort(list);
    }
    void interface_event_declaration(interface_event_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
    }
    void interface_indexer_declaration(interface_indexer_declaration ast, ArrayList list) {
        list.Add(new Pair("this", ast));
    }
    void interface_method_declaration(interface_method_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
    }
    void interface_property_declaration(interface_property_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
    }
    string member_name(member_name ast) {
        if (ast.ty != null)
            return type(ast.ty) + "." + ast.id.str;
        else
            return ast.id.str;
    }
    void method_declaration(method_declaration ast, ArrayList list) {
        list.Add(new Pair(member_name(ast.name), ast));
    }
    void namespace_declaration(namespace_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.ToString(), ast));
        list = new ArrayList();
        foreach (declaration x in ast.nb.declarations)
            declaration(x, list);
        ast.nb.declarations = Sort(list);
    }
    void operator_declaration(operator_declaration ast, ArrayList list) {
        InputElement op;
             if (ast.op is unary_declarator)    op = ((unary_declarator)ast.op).op;
        else if (ast.op is binary_declarator)   op = ((binary_declarator)ast.op).op;
        else if (ast.op is implicit_declarator) op = ((implicit_declarator)ast.op).id1;
        else if (ast.op is explicit_declarator) op = ((explicit_declarator)ast.op).id1;
        else
            throw new ArgumentException();
        list.Add(new Pair(op.str, ast));
    }
    void property_declaration(property_declaration ast, ArrayList list) {
        list.Add(new Pair(member_name(ast.name), ast));
    }
    void struct_declaration(struct_declaration ast, ArrayList list) {
        list.Add(new Pair(ast.id.str, ast));
        list = new ArrayList();
        foreach (declaration x in ast.body)
            declaration(x, list);
        ast.body = Sort(list);
    }
    string type(type ast) {
        if (ast is name_type)
            return ((name_type)ast).name.ToString();
        throw new ArgumentException();
    }
}
