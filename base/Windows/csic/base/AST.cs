using System;
using System.Collections;
using System.Reflection.Emit;

public class List {
	public static IList Cons(IList a, object o) {
		a.Add(o);
		return a;
	}
	public static IList Sort(IList a) {
		ArrayList array = new ArrayList(a);
		array.Sort();
		a.Clear();
		foreach (object o in array)
			a.Add(o);
		return a;
	}
	public static void visit(IList list, ASTVisitor prefix, ASTVisitor postfix) {
		foreach (AST x in list)
			x.visit(prefix, postfix);
	}
}

public class accessor_declaration: declaration {
	public accessor_declaration(IList attrs, IList mods, InputElement id, statement body) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.id = id;
		this.body = body;
	}
	public accessor_declaration(IList attrs, InputElement id) : this(attrs, InputElementList.New(), id, null) {}
	public attribute_sectionList attrs;
	[MayBeNull] public statement body;
	public InputElement id;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		if (body != null)
			body.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Method sym;	// bind: symbol-table entry for id
	[Emit] public MethodBuilder builder;	// emit
}

public class alias_directive: using_directive {
	public alias_directive(InputElement id, dotted_name name) {
		this.id = id;
		this.name = name;
	}
	public InputElement id;
	public dotted_name name;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		name.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Symbol sym;
}

public class anonymous_method_expression: expression {
	public parameterList formals;
	public statement block;
	public anonymous_method_expression(IList formals, statement block) {
		this.formals = (parameterList)formals;
		this.block = block;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(formals, prefix, postfix);
		block.visit(prefix, postfix);
		postfix(this);
	}
}

public class arglist_parameter: parameter {
	public InputElement arglist;
	public arglist_parameter(InputElement arglist) : base(attribute_sectionList.New()) {
		this.arglist = arglist;
	}
}

public class argument: AST {
	public argument(InputElement kind, expression expr) {
		this.kind = kind;
		this.expr = expr;
	}
	public expression expr;
	[MayBeNull] public InputElement kind;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Type typ;	// typecheck
}

public class array_creation_expression1: expression {
	public array_creation_expression1(type ty, IList exprs, IList ranks, array_initializer init) {
		this.ty = ty;
		this.exprs = (expressionList)exprs;
		this.ranks = (intList)ranks;
		this.init = init;
	}
	public expressionList exprs;
	[MayBeNull] public array_initializer init;
	public intList ranks;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		List.visit(exprs, prefix, postfix);
		if (init != null)
			init.visit(prefix, postfix);
		postfix(this);
	}
}

public class array_creation_expression2: expression {
	public array_creation_expression2(type ty, array_initializer init) {
		this.ty = ty;
		this.init = init;
	}
	public array_initializer init;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		init.visit(prefix, postfix);
		postfix(this);
	}
}

public class array_initializer: variable_initializer {
	public variable_initializerList a;
	public array_initializer(IList a) {
		this.a = (variable_initializerList)a;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (this.a != null)
			List.visit(this.a, prefix, postfix);
		postfix(this);
	}
}

public class array_type: type {
	public array_type(type ty, int rank_specifier) {
		this.ty = ty;
		this.rank_specifier = rank_specifier;
	}
	public int rank_specifier;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		postfix(this);
	}
}

public class as_expression: expression {
	public as_expression(expression expr, type ty) {
		this.expr = expr;
		this.ty = ty;
	}
	public expression expr;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		ty.visit(prefix, postfix);
		postfix(this);
	}
	[Bind2] public Type sym;	// bind
}

public class assignment_expression: expression {
	public assignment_expression(expression e1, expression e2) {
		this.e1 = e1;
		this.e2 = e2;
	}
	public expression e1;
	public expression e2;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		e1.visit(prefix, postfix);
		e2.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck,MayBeNull] public Method method;	// typecheck
}

public class attribute: AST {
	[MayBeNull] public attribute_arguments arguments;
	public attribute(type name, attribute_arguments arguments) {
		this.name = name;
		this.arguments = (attribute_arguments)arguments;
	}
	public type name;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		name.visit(prefix, postfix);
		if (arguments != null)
			arguments.visit(prefix, postfix);
		postfix(this);
	}
	[Bind3] public ClassType sym;	// bind
	[Typecheck] public Constructor method;	// typecheck
}

public class attribute_arguments: AST {
	public argumentList args;
	public attribute_arguments(IList args, IList namedargs) {
		this.args = argumentList.New();
		foreach (expression e in (expressionList)args)
			this.args.Add(new argument(null, e));
		this.namedargs = (named_argumentList)namedargs;
	}
	public named_argumentList namedargs;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(args, prefix, postfix);
		List.visit(namedargs, prefix, postfix);
		postfix(this);
	}
}

public class attribute_section: AST {
	public attribute_section(InputElement target, IList attributes) {
		this.target = target;
		this.attributes = (attributeList)attributes;
	}
	public attributeList attributes;
	[MayBeNull] public InputElement target;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attributes, prefix, postfix);
		postfix(this);
	}
}

public class base_access: expression {
	public base_access() {
	}
	[Bind2] public ClassType sym;	// bind
}

public class base_initializer: constructor_initializer {
	public argumentList args;
	public base_initializer(IList args) {
		this.args = (argumentList)args;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(args, prefix, postfix);
		postfix(this);
	}
}

public class binary_declarator: operator_declarator {
	public binary_declarator(type ty, InputElement op, type t1, InputElement id1, type t2, InputElement id2) {
		this.ty = ty;
		this.op = op;
		this.t1 = t1;
		this.id1 = id1;
		this.t2 = t2;
		this.id2 = id2;
	}
	public InputElement id1;
	public InputElement id2;
	public InputElement op;
	public type t1;
	public type t2;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		t1.visit(prefix, postfix);
		t2.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Formal sym1, sym2;	// bind: symbol-table entries for id1, id2
}

public class binary_expression: expression {
	public binary_expression(expression e1, InputElement op, expression e2) {
		this.e1 = e1;
		this.op = op;
		this.e2 = e2;
	}
	public expression e1;
	public expression e2;
	public InputElement op;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		e1.visit(prefix, postfix);
		e2.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Method method;	// typecheck
}

public class block_statement: statement {
	public block_statement(IList stmts) {
		this.stmts = (statementList)stmts;
	}
	public statementList stmts;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(stmts, prefix, postfix);
		postfix(this);
	}
	[Bind1] public Block sym;	// bind: Block for stmts
}

public class bool_type: type {
	public bool_type() {
	}
}

public class boolean_literal: literal {
	public boolean_literal(InputElement token) {
		this.token = token;
	}
}

public class break_statement: statement {
	public break_statement() {
	}
	[Bind1] public statement stmt;	// associated for, foreach, while, do, or switch
	[Rewrite] public bool exitstry;	// rewrite: true if goto exits try block
}

public class byte_type: type {
	public byte_type() {
	}
}

public class cast_expression: expression {
	public cast_expression(type ty, expression expr) {
		this.ty = ty;
		this.expr = expr;
	}
	public expression expr;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Bind2] public Type sym;	// bind
	[MayBeNull,Typecheck] public Method method;	// typecheck
}

public class catch_clause: AST {
	public statement block;
	public catch_clause(type ty, InputElement id, statement block) {
		this.ty = ty;
		this.id = id;
		this.block = block;
	}
	[MayBeNull] public InputElement id;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (ty != null)
			ty.visit(prefix, postfix);
		block.visit(prefix, postfix);
		postfix(this);
	}
	[MayBeNull,Bind1] public Local sym;	// bind: symbol-table entry for id
}

public class catch_clauses: AST {
	public catch_clauses(IList specifics, statement general) {
		this.specifics = (catch_clauseList)specifics;
		this.general = general;
	}
	[MayBeNull] public statement general;
	public catch_clauseList specifics;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(specifics, prefix, postfix);
		if (general != null)
			general.visit(prefix, postfix);
		postfix(this);
	}
}

public class char_type: type {
	public char_type() {
	}
}

public class character_literal: literal {
	public character_literal(InputElement token) {
		this.token = token;
	}
}

public class checked_expression: expression {
	public checked_expression(expression expr) {
		this.expr = expr;
	}
	public expression expr;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class checked_statement: statement {
	public checked_statement(statement stmt) {
		this.stmt = stmt;
	}
	public statement stmt;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		stmt.visit(prefix, postfix);
		postfix(this);
	}
}

public class class_declaration: type_declaration {
	public attribute_sectionList attrs;
	public type_parameterList typeparams;
	public typeList bases;
	public type_parameter_constraints_clauseList constraints;
	public declarationList body;
	public class_declaration(IList attrs, IList mods, InputElement id, IList typeparams, IList bases, IList constraints, IList body) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.id = id;
		this.typeparams = (type_parameterList)typeparams;
		this.bases = (typeList)bases;
		this.constraints = (type_parameter_constraints_clauseList)constraints;
		this.body = (declarationList)body;
	}
	public InputElement id;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		List.visit(bases, prefix, postfix);
		List.visit(body, prefix, postfix);
		postfix(this);
	}
	[Bind1] public ClassType sym;	// bind: ClassType for this class
	[Bind1] override public Type typ { get { return sym; } }	// bind
}

public class compilation: AST {
	public NameSpace global;
	public stringList args;
	public compilation_unitList inputs;
	public compilation(string[] args, compilation_unitList inputs, NameSpace global) {
		this.args = new stringList();
		foreach (string arg in args)
			this.args.Add(arg);
		this.inputs = inputs;
		this.global = global;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(inputs, prefix, postfix);
		postfix(this);
	}
	[Bind2] public stringList assemblyRefs;	// referenced assemblies
}

public class compilation_unit: AST {
	public attribute_sectionList attributes;
	public compilation_unit(IList using_directives, IList attributes, IList declarations) {
		this.using_directives = (using_directiveList)using_directives;
		this.attributes = (attribute_sectionList)attributes;
		this.declarations = (declarationList)declarations;
	}
	public declarationList declarations;
	public using_directiveList using_directives;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(using_directives, prefix, postfix);
		List.visit(attributes, prefix, postfix);
		List.visit(declarations, prefix, postfix);
		postfix(this);
	}
	[Bind1] public NameSpace sym;	// bind: global NameSpace
}

public class compound_assignment_expression: expression {
	public compound_assignment_expression(expression e1, InputElement op, expression e2) {
		this.e1 = e1;
		this.op = op;
		this.e2 = e2;
	}
	public expression e1;
	public expression e2;
	public InputElement op;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		e1.visit(prefix, postfix);
		e2.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Method opmethod;	// typecheck
	[Typecheck,MayBeNull] public Method method;	// typecheck
}

public class cond_expression: expression {
	public expression cond;
	public cond_expression(expression cond, expression success, expression failure) {
		this.cond = cond;
		this.success = success;
		this.failure = failure;
	}
	public expression failure;
	public expression success;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		cond.visit(prefix, postfix);
		success.visit(prefix, postfix);
		failure.visit(prefix, postfix);
		postfix(this);
	}
}

public class const_declarator: declarator {
	public const_declarator(InputElement id, expression expr) : base(id) {
		this.expr = expr;
	}
	public expression expr;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (expr != null)
			expr.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Constant sym;	// bind: symbol-table entry for id
	[Emit] public FieldBuilder builder;	// emit
}

public class const_statement: statement {
	public const_statement(type ty, IList consts) {
		this.ty = ty;
		this.consts = (declaratorList)consts;
	}
	public declaratorList consts;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		List.visit(consts, prefix, postfix);
		postfix(this);
	}
}

public class constant_declaration: declaration {
	public attribute_sectionList attrs;
	public constant_declaration(IList attrs, IList mods, type ty, IList decls) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.ty = ty;
		this.decls = (declaratorList)decls;
	}
	public declaratorList decls;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		List.visit(decls, prefix, postfix);
		postfix(this);
	}
}

public class constructor_constraint: type {
	public constructor_constraint() {
	}
}

public class constructor_declaration: declaration {
	public attribute_sectionList attrs;
	[MayBeNull] public statement block;
	public constructor_declaration(IList attrs, IList mods, constructor_declarator decl, statement block) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.decl = decl;
		this.block = block;
	}
	public constructor_declarator decl;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		decl.visit(prefix, postfix);
		if (block != null)
			block.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Constructor sym;	// bind: symbol-table entry for this constructor
	[Emit] public ConstructorBuilder builder;	// emit
}

public class constructor_declarator: AST {
	public constructor_declarator(InputElement id, formals f, constructor_initializer init) {
		this.id = id;
		this.f = f;
		this.init = init;
	}
	public formals f;
	public InputElement id;
	[MayBeNull] public constructor_initializer init;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		f.visit(prefix, postfix);
		if (init != null)
			init.visit(prefix, postfix);
		postfix(this);
	}
}

public abstract class constructor_initializer: AST {
	public constructor_initializer() {
	}
	[Typecheck] public Constructor method;	// typecheck
}

public class continue_statement: statement {
	public continue_statement() {
	}
	[Bind1] public statement stmt;	// associated for, foreach, while, do, or switch
	[Rewrite] public bool exitstry;	// rewrite: true if goto exits try block
}

public class decimal_type: type {
	public decimal_type() {
	}
}

public abstract class declaration: AST {
	public InputElementList mods;
	public declaration() {
	}
}

public abstract class declarator: AST {
	public declarator(InputElement id) {
		this.id = id;
	}
	public InputElement id;
}

public class delegate_declaration: type_declaration {
	public attribute_sectionList attrs;
	public type_parameterList typeparams;
	public type_parameter_constraints_clauseList constraints;
	public delegate_declaration(IList attrs, IList mods, type ty, InputElement id, formals f, IList typeparams, IList constraints) {
		this.attrs = (attribute_sectionList)attrs;
		this.typeparams = (type_parameterList)typeparams;
		this.constraints = (type_parameter_constraints_clauseList)constraints;
		this.mods = (InputElementList)mods;
		this.ty = ty;
		this.id = id;
		this.f = f;
	}
	public formals f;
	public InputElement id;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		f.visit(prefix, postfix);
		List.visit(typeparams, prefix, postfix);
		List.visit(constraints, prefix, postfix);
		postfix(this);
	}
	[Bind1] public DelegateType sym;	// bind: DeletegateType for id
	[Bind1] override public Type typ { get { return sym; } }	// bind
}

public class destructor_declaration: declaration {
	public attribute_sectionList attrs;
	[MayBeNull] public statement block;
	public destructor_declaration(IList attrs, IList mods, InputElement id, statement block) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.id = id;
		this.block = block;
	}
	public InputElement id;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		if (block != null)
			block.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Method sym;	// bind: symbol-table entry for id
	[Emit] public MethodBuilder builder;	// emit
}

public class do_statement: statement {
	public statement body;
	public do_statement(statement body, expression expr) {
		this.body = body;
		this.expr = expr;
	}
	public expression expr;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		body.visit(prefix, postfix);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class dotted_name: AST, IImage {
	public dotted_name(dotted_name left, InputElement right) : this(left, right, null) {}
	public dotted_name(dotted_name left, InputElement right, IList typeargs) {
		this.left = left;
		this.right = right;
		this.typeargs = (typeList)typeargs;
	}
	[MayBeNull] public dotted_name left;
	public InputElement right;
	[MayBeNull] public typeList typeargs;
	override public string ToString() {
		if (left != null)
			return (left.ToString() + ".") + right.str;
		else
			return right.str;
	}
	string IImage.Image() {
		return ToString();
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (left != null)
			left.visit(prefix, postfix);
		if (typeargs != null)
			List.visit(typeargs, prefix, postfix);
		postfix(this);
	}
	[Bind2] public Symbol sym;	// bind
}

public class double_type: type {
	public double_type() {
	}
}

public class element_access: expression {
	public element_access(expression expr, IList exprs) {
		this.expr = expr;
		this.exprs = new argumentList();
		foreach (expression e in (expressionList)exprs) {
			argument arg = new argument(null, e);
			arg.begin = e.begin;
			arg.end = e.end;
			this.exprs.Add(arg);
		}
	}
	public expression expr;
	public argumentList exprs;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		List.visit(exprs, prefix, postfix);
		postfix(this);
	}
	[MayBeNull,Typecheck] public Method get, set;	// typecheck
}

public class empty_statement: statement {
	public empty_statement() {
	}
}

public class enum_declaration: type_declaration {
	public attribute_sectionList attrs;
	public enum_member_declarationList body;
	public enum_declaration(IList attrs, IList mods, InputElement id, type ty, IList body) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.id = id;
		this.ty = ty;
		this.body = (enum_member_declarationList)body;
	}
	public InputElement id;
	[MayBeNull] public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		if (ty != null)
			ty.visit(prefix, postfix);
		List.visit(body, prefix, postfix);
		postfix(this);
	}
	[Bind1] public EnumType sym;	// bind: EnumType for id
	[Bind1] override public Type typ { get { return sym; } }	// bind
}

public class enum_member_declaration: AST {
	public attribute_sectionList attrs;
	public enum_member_declaration(IList attrs, InputElement id, expression expr) {
		this.attrs = (attribute_sectionList)attrs;
		this.id = id;
		this.expr = expr;
	}
	[MayBeNull] public expression expr;
	public InputElement id;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		if (expr != null)
			expr.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public EnumMember sym;	// bind: symbol-table entry for id
	[Emit] public FieldBuilder builder;	// emit
}

public class event_accessor: AST {
	public attribute_sectionList attrs;
	public statement block;
	public event_accessor(IList attrs, InputElement id, statement block) {
		this.attrs = (attribute_sectionList)attrs;
		this.id = id;
		this.block = block;
	}
	public InputElement id;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		block.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Method sym;	// bind: symbol-table entry for id
	[Emit] public MethodBuilder builder;	// emit
}

public class event_declaration1: declaration {
	public attribute_sectionList attrs;
	public declaratorList decls;
	public event_declaration1(IList attrs, IList mods, type ty, IList decls) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.ty = ty;
		this.decls = (declaratorList)decls;
		for (int i = 0; i < this.decls.Count; i++)
			this.decls[i] = new event_declarator((var_declarator)this.decls[i]);
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		List.visit(decls, prefix, postfix);
		postfix(this);
	}
}

public class event_declaration2: declaration {
	public event_accessorList accessors;
	public attribute_sectionList attrs;
	public event_declaration2(IList attrs, IList mods, type ty, member_name name, IList accessors) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.ty = ty;
		this.name = name;
		this.accessors = (event_accessorList)accessors;
	}
	public member_name name;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		name.visit(prefix, postfix);
		List.visit(accessors, prefix, postfix);
		postfix(this);
	}
	[Bind1] public Event sym;	// bind: symbol-table entry for name
	[Emit] public EventBuilder builder;	// emit
}

public class event_declarator: declarator {
	[MayBeNull] public variable_initializer init;
	public event_declarator(InputElement id, variable_initializer init) : base(id) {
		this.init = init;
	}
	public event_declarator(var_declarator decl) : base(decl.id) {
		this.init = decl.init;
		this.begin = decl.begin;
		this.end = decl.end;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (init != null)
			init.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Event sym;	// bind: symbol-table entry for id
	[Emit] public FieldBuilder builder;	// emit
	[Emit] public EventBuilder event_builder;
	[Emit] public MethodBuilder add_builder, remove_builder;	// emit
}

public class explicit_declarator: operator_declarator {
	public explicit_declarator(type ty, type t1, InputElement id1) {
		this.ty = ty;
		this.t1 = t1;
		this.id1 = id1;
	}
	public InputElement id1;
	public type t1;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		t1.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Formal sym;	// bind: symbol-table entry for id1
}

public class expr_access: member_access {
	public expression expr;
	public expr_access(expression expr, InputElement id, IList typeargs) : base(id, typeargs) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		if (typeargs != null)
			List.visit(typeargs, prefix, postfix);
		postfix(this);
	}
}

public class expr_initializer: variable_initializer {
	public expression expr;
	public expr_initializer(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public abstract class expression: AST {
	public expression annotate(bool valueUsed) {
		this.valueUsed = valueUsed;
		return this;
	}
	public expression() {
	}
	public bool valueUsed = true;
	[Typecheck] public Type typ;	// typecheck
	[MayBeNull,Typecheck] public object value;	// typecheck
}

public class expression_statement: statement {
	public expression expr;
	public expression_statement(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class field_declaration: declaration {
	public attribute_sectionList attrs;
	public declaratorList decls;
	public field_declaration(IList attrs, IList mods, type ty, IList decls) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.ty = ty;
		this.decls = (declaratorList)decls;
		for (int i = 0; i < this.decls.Count; i++)
			this.decls[i] = new field_declarator((var_declarator)this.decls[i]);
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		List.visit(decls, prefix, postfix);
		postfix(this);
	}
}

public class field_declarator: declarator {
	[MayBeNull] public variable_initializer init;
	public field_declarator(InputElement id, variable_initializer init) : base(id) {
		this.init = init;
	}
	public field_declarator(var_declarator decl) : base(decl.id) {
		this.init = decl.init;
		this.begin = decl.begin;
		this.end = decl.end;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (init != null)
			init.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Field sym;	// bind: symbol-table entry for id
	[Emit] public FieldBuilder builder;	// emit
}

public class finally_clause: AST {
	public statement block;
	public finally_clause(statement block) {
		this.block = block;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		block.visit(prefix, postfix);
		postfix(this);
	}
}

public class fixed_declarator: declarator {
	public expression expr;
	public fixed_declarator(InputElement id, expression expr) : base(id) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Local sym;	// bind: symbol-table entry for id
}

public class fixed_parameter: parameter {
	public fixed_parameter(IList attrs, InputElement mod, type ty, InputElement id) : base(attrs){
		this.mod = mod;
		this.ty = ty;
		this.id = id;
	}
	public InputElement id;
	[MayBeNull] public InputElement mod;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		postfix(this);
	}
}

public class fixed_statement: statement {
	public statement body;
	public declaratorList declarators;
	public fixed_statement(type ty, IList declarators, statement body) {
		this.ty = ty;
		this.declarators = (declaratorList)declarators;
		this.body = body;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		List.visit(declarators, prefix, postfix);
		body.visit(prefix, postfix);
		postfix(this);
	}
}

public class float_type: type {
	public float_type() {
	}
}

public class for_decl: for_init {
	public local_statement decl;
	public for_decl(local_statement decl) {
		this.decl = decl;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		decl.visit(prefix, postfix);
		postfix(this);
	}
}

public abstract class for_init: AST {
	public for_init() {
	}
	[Bind2] public Block sym;	// bind
}

public class for_list: for_init {
	public expressionList exprs;
	public for_list(IList exprs) {
		this.exprs = (expressionList)exprs;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(exprs, prefix, postfix);
		postfix(this);
	}
}

public class for_statement: statement {
	public statement body;
	[MayBeNull] public expression cond;
	public for_statement(for_init init, expression cond, IList iterators, statement body) {
		this.init = init;
		this.cond = cond;
		this.iterators = (expressionList)iterators;
		this.body = body;
	}
	[MayBeNull] public for_init init;
	public expressionList iterators;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (init != null)
			init.visit(prefix, postfix);
		if (cond != null)
			cond.visit(prefix, postfix);
		List.visit(iterators, prefix, postfix);
		body.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Block sym;	// bind: Block for body
}

public class foreach_statement: statement {
	public statement body;
	public expression expr;
	public foreach_statement(type ty, InputElement id, expression expr, statement body) {
		this.ty = ty;
		this.id = id;
		this.expr = expr;
		this.body = body;
	}
	public InputElement id;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		expr.visit(prefix, postfix);
		body.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Local sym;	// bind: Block for body
	[Typecheck,MayBeNull] public Method GetEnumerator;
	[Typecheck,MayBeNull] public Method MoveNext;
	[Typecheck,MayBeNull] public Property Current;
}

public class formals: AST {
	public parameterList fixeds;
	public formals(IList fixeds, parameter param) {
		this.fixeds = (parameterList)fixeds;
		this.param = param;
	}
	[MayBeNull] public parameter param;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(fixeds, prefix, postfix);
		if (param != null)
			param.visit(prefix, postfix);
		postfix(this);
	}
}

public class generic_interface_method_declaration: interface_method_declaration {
	public type_parameterList typeparams;
	public type_parameter_constraints_clauseList constraints;
	public generic_interface_method_declaration(IList attrs, InputElement newopt, type ty, InputElement id,
			IList typeparams, formals f, IList constraints) : base(attrs, newopt, ty, id, f) {
		this.typeparams = (type_parameterList)typeparams;
		this.constraints = (type_parameter_constraints_clauseList)constraints;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		List.visit(typeparams, prefix, postfix);
		f.visit(prefix, postfix);
		List.visit(constraints, prefix, postfix);
		postfix(this);
	}
}

public class generic_method_declaration: method_declaration {
	public type_parameterList typeparams;
	public type_parameter_constraints_clauseList constraints;
	public generic_method_declaration(IList attrs, IList mods, type ty, member_name name,
			IList typeparams, formals parms, IList constraints, statement body) : base(attrs, mods, ty, name, parms, body) {
		this.typeparams = (type_parameterList)typeparams;
		this.constraints = (type_parameter_constraints_clauseList)constraints;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		name.visit(prefix, postfix);
		List.visit(typeparams, prefix, postfix);
		parms.visit(prefix, postfix);
		List.visit(constraints, prefix, postfix);
		if (body != null)
			body.visit(prefix, postfix);
		postfix(this);
	}
}

public class goto_case_statement: statement {
	public expression expr;
	public goto_case_statement(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public statement stmt;	// bind: associated switch statement
	[Typecheck] public switch_label label;	// typecheck: associated switch label
	[Rewrite] public bool exitstry;	// rewrite: true if goto exits try block
}

public class goto_default_statement: statement {
	public goto_default_statement() {
	}
	[Bind1] public statement stmt;	// associated switch
	[Rewrite] public bool exitstry;	// rewrite: true if goto exits try block
}

public class goto_statement: statement {
	public goto_statement(InputElement id) {
		this.id = id;
	}
	public InputElement id;
	[Bind2] public labeled_statement target;	// bind
	[Bind2] public Label sym;	// bind
	[Rewrite] public bool exitstry;	// rewrite: true if goto exits try block
}

public class if_statement: statement {
	[MayBeNull] public statement elsepart;
	public expression expr;
	public if_statement(expression expr, statement thenpart, statement elsepart) {
		this.expr = expr;
		this.thenpart = thenpart;
		this.elsepart = elsepart;
	}
	public statement thenpart;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		thenpart.visit(prefix, postfix);
		if (elsepart != null)
			elsepart.visit(prefix, postfix);
		postfix(this);
	}
}

public class implicit_cast_expression: expression {
	public implicit_cast_expression(type ty, expression expr) {
		this.ty = ty;
		this.expr = expr;
		this.begin = expr.begin;
		this.end = expr.end;
	}
	[MayBeNull] public type ty;
	public expression expr;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (ty != null)
			ty.visit(prefix, postfix);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[MayBeNull,Typecheck] public Method method;	// typecheck
}

public class implicit_declarator: operator_declarator {
	public InputElement id1;
	public implicit_declarator(type ty, type t1, InputElement id1) {
		this.ty = ty;
		this.t1 = t1;
		this.id1 = id1;
	}
	public type t1;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		t1.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Formal sym;	// bind: symbol-table entry for id1
}

public class indexer: AST {
	public formals f;
	public indexer(type ty, name_type interfacename, formals f) {
		this.ty = ty;
		this.interfacename = interfacename;
		this.f = f;
	}
	[MayBeNull] public name_type interfacename;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		if (interfacename != null)
			interfacename.visit(prefix, postfix);
		f.visit(prefix, postfix);
		postfix(this);
	}
}

public class indexer_declaration: declaration {
	public accessor_declarationList accessors;
	public attribute_sectionList attrs;
	public indexer i;
	public indexer_declaration(IList attrs, IList mods, indexer i, IList accessors) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.i = i;
		this.accessors = (accessor_declarationList)accessors;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		i.visit(prefix, postfix);
		List.visit(accessors, prefix, postfix);
		postfix(this);
	}
	[Emit] public PropertyBuilder builder;	// emit
}

public class int_type: type {
	public int_type() {
	}
}

public class integer_literal: literal {
	public integer_literal(InputElement token) {
		this.token = token;
	}
}

public class interface_declaration: type_declaration {
	public attribute_sectionList attrs;
	public type_parameterList typeparams;
	public type_parameter_constraints_clauseList constraints;
	public declarationList body;
	public InputElement id;
	public interface_declaration(IList attrs, IList mods, InputElement id, IList typeparams, IList interfaces, IList constraints, IList body) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.id = id;
		this.typeparams = (type_parameterList)typeparams;
		this.interfaces = (typeList)interfaces;
		this.constraints = (type_parameter_constraints_clauseList)constraints;
		this.body = (declarationList)body;
	}
	public typeList interfaces;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		List.visit(interfaces, prefix, postfix);
		List.visit(body, prefix, postfix);
		postfix(this);
	}
	[Bind1] public InterfaceType sym;	// bind: InterfaceType for this interface
	[Bind1] override public Type typ { get { return sym; } }	// bind
}

public class interface_event_declaration: declaration {
	public attribute_sectionList attrs;
	public InputElement id;
	public interface_event_declaration(IList attrs, InputElement newopt, type ty, InputElement id) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = new InputElementList();
		if (newopt != null)
			this.mods.Add(newopt);
		this.ty = ty;
		this.id = id;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Event sym;	// bind: symbol-table entry for id
	[Emit] public EventBuilder builder;	// emit
}

public class interface_indexer_declaration: declaration {
	public accessor_declarationList accessors;
	public attribute_sectionList attrs;
	public formals f;
	public interface_indexer_declaration(IList attrs, InputElement newopt, type ty, formals f, IList accessors) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = new InputElementList();
		if (newopt != null)
			this.mods.Add(newopt);
		this.ty = ty;
		this.f = f;
		this.accessors = (accessor_declarationList)accessors;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		f.visit(prefix, postfix);
		List.visit(accessors, prefix, postfix);
		postfix(this);
	}
	[Emit] public PropertyBuilder builder;	// emit
}

public class interface_method_declaration: declaration {
	public attribute_sectionList attrs;
	public formals f;
	public InputElement id;
	public interface_method_declaration(IList attrs, InputElement newopt, type ty, InputElement id, formals f) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = new InputElementList();
		if (newopt != null)
			this.mods.Add(newopt);
		this.ty = ty;
		this.id = id;
		this.f = f;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		f.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Method sym;	// bind: symbol-table entry for id
	[Emit] public MethodBuilder builder;	// emit
}

public class interface_property_declaration: declaration {
	public accessor_declarationList accessors;
	public attribute_sectionList attrs;
	public InputElement id;
	public interface_property_declaration(IList attrs, InputElement newopt, type ty, InputElement id, IList accessors) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = new InputElementList();
		if (newopt != null)
			this.mods.Add(newopt);
		this.ty = ty;
		this.id = id;
		this.accessors = (accessor_declarationList)accessors;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		List.visit(accessors, prefix, postfix);
		postfix(this);
	}
	[Bind1] public Property sym;	// bind: symbol-table entry for id
	[Emit] public PropertyBuilder builder;	// emit
}

public class invocation_expression: expression {
	public argumentList args;
	public expression expr;
	public invocation_expression(expression expr, IList args) {
		this.expr = expr;
		this.args = (argumentList)args;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		List.visit(args, prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Method method;	// typecheck
}

public class is_expression: expression {
	public expression expr;
	public is_expression(expression expr, type ty) {
		this.expr = expr;
		this.ty = ty;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		ty.visit(prefix, postfix);
		postfix(this);
	}
	[Bind2] public Type sym;	// bind
}

public class labeled_statement: statement {
	public InputElement label;
	public labeled_statement(InputElement label, statement stmt) {
		this.label = label;
		this.stmt = stmt;
	}
	public statement stmt;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		stmt.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Label sym;	// bind: symbol-table entry for label
}

public abstract class literal: expression {
	public literal() {
	}
	public InputElement token;
}

public class local_expression: expression {
	public local_expression(expression expr) {
		this.expr = expr;
		this.typ = expr.typ;
		this.valueUsed = expr.valueUsed;
		this.parent = expr.parent;
		expr.parent = this;
	}
	public expression expr;
	new public expression value = null;
}

public class local_statement: statement {
	public local_statement(type ty, IList vars) {
		this.ty = ty;
		this.vars = (declaratorList)vars;
	}
	public type ty;
	public declaratorList vars;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		List.visit(vars, prefix, postfix);
		postfix(this);
	}
}

public class lock_statement: statement {
	public statement body;
	public expression expr;
	public lock_statement(expression expr, statement body) {
		this.expr = expr;
		this.body = body;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		body.visit(prefix, postfix);
		postfix(this);
	}
}

public class long_type: type {
	public long_type() {
	}
}

public abstract class member_access: expression {
	public member_access(InputElement id) : this(id, null) {}
	public member_access(InputElement id, IList typeargs) {
		this.id = id;
		this.typeargs = (typeList)typeargs;
	}
	public InputElement id;
	[MayBeNull] public typeList typeargs;
	[Typecheck] public Symbol sym;	// typecheck
	[MayBeNull,Typecheck] public Method method;	// typecheck
}

public class member_name: AST {
	public InputElement id;
	public member_name(type ty, InputElement id) {
		this.ty = ty;
		this.id = id;
	}
	[MayBeNull] public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (ty != null)
			ty.visit(prefix, postfix);
		postfix(this);
	}
	[Bind2] public InterfaceType sym;	// bind
}

public class method_declaration: declaration {
	public attribute_sectionList attrs;
	[MayBeNull] public statement body;
	public method_declaration(IList attrs, IList mods, type ty, member_name name, formals parms, statement body) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.ty = ty;
		this.name = name;
		this.parms = parms;
		this.body = body;
	}
	public member_name name;
	public formals parms;
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		name.visit(prefix, postfix);
		parms.visit(prefix, postfix);
		if (body != null)
			body.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Method sym;	// bind: symbol-table entry for name
	[Emit] public MethodBuilder builder;	// emit
}

public class name_type: type {
	public dotted_name name;
	public name_type(dotted_name name) {
		this.name = name;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		name.visit(prefix, postfix);
		postfix(this);
	}
}

public class named_argument: AST {
	public expression expr;
	public InputElement id;
	public named_argument(InputElement id, expression expr) {
		this.id = id;
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Bind3] public Symbol sym;	// bind; associated field or property
}

public class namespace_body: AST {
	public declarationList declarations;
	public namespace_body(IList ud, IList declarations) {
		this.ud = (using_directiveList)ud;
		this.declarations = (declarationList)declarations;
	}
	public using_directiveList ud;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(ud, prefix, postfix);
		List.visit(declarations, prefix, postfix);
		postfix(this);
	}
}

public class namespace_declaration: declaration {
	public dotted_name id;
	public namespace_declaration(dotted_name id, namespace_body nb) {
		this.mods = new InputElementList();
		this.id = id;
		this.nb = nb;
	}
	public namespace_body nb;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		id.visit(prefix, postfix);
		nb.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public NameSpace sym;	// bind: symbol-table entry for id
}

public class namespace_directive: using_directive {
	public dotted_name name;
	public namespace_directive(dotted_name name) {
		this.name = name;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		name.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public NameSpace sym;	// bind: NameSpace for name
}

public class new_expression: expression {
	public argumentList args;
	public new_expression(type ty, IList args) {
		this.ty = ty;
		this.args = (argumentList)args;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		List.visit(args, prefix, postfix);
		postfix(this);
	}
	[MayBeNull,Typecheck] public Constructor method;	// typecheck
}

public class null_literal: literal {
	public null_literal(InputElement token) {
		this.token = token;
	}
}

public class object_type: type {
	public object_type() {
	}
}

public class operator_declaration: declaration {
	public attribute_sectionList attrs;
	[MayBeNull] public statement block;
	public operator_declarator op;
	public operator_declaration(IList attrs, IList mods, operator_declarator op, statement block) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.op = op;
		this.block = block;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		op.visit(prefix, postfix);
		if (block != null)
			block.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Method sym;	// bind: symbol-table entry for op
}

public abstract class operator_declarator: AST {
	public operator_declarator() {
	}
	public type ty;
	[Bind1] public Method method;	// bind: symbol-table entry for operator method
}

public abstract class parameter: AST {
	public attribute_sectionList attrs;
	public parameter(IList attrs) {
		this.attrs = (attribute_sectionList)attrs;
	}
	[Bind1] public Method method;	// bind: symbol-table entry for associated method
}

public class params_parameter: parameter {
	public InputElement id;
	public params_parameter(IList attrs, type ty, InputElement id) : base(attrs) {
		this.ty = ty;
		this.id = id;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		postfix(this);
	}
}

public class pointer_access: member_access {
	public expression expr;
	public pointer_access(expression expr, InputElement id) : base(id) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class pointer_type: type {
	public pointer_type(type ty) {
		this.ty = ty;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		postfix(this);
	}
}

public class post_expression: expression {
	public expression expr;
	public InputElement op;
	public post_expression(InputElement op, expression expr) {
		this.op = op;
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Method method;	// typecheck
}

public class pre_expression: expression {
	public expression expr;
	public InputElement op;
	public pre_expression(InputElement op, expression expr) {
		this.op = op;
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Method method;	// typecheck
}

public class predefined_access: member_access {
	public InputElement predefined;
	public predefined_access(InputElement predefined, InputElement id, IList typeargs) : base(id, typeargs) {
		this.predefined = predefined;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (typeargs != null)
			List.visit(typeargs, prefix, postfix);
		postfix(this);
	}
	[Bind2] public Type type;	// bind
}

public class property_declaration: declaration {
	public attribute_sectionList attrs;
	public accessor_declarationList decls;
	public member_name name;
	public property_declaration(IList attrs, IList mods, type ty, member_name name, IList decls) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.ty = ty;
		this.name = name;
		this.decls = (accessor_declarationList)decls;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		ty.visit(prefix, postfix);
		name.visit(prefix, postfix);
		List.visit(decls, prefix, postfix);
		postfix(this);
	}
	[Bind1] public Property sym;	// bind: symbol-table entry for id
	[Emit] public PropertyBuilder builder;	// emit
}

public class qualified_alias_member: dotted_name {
	public InputElement qualifier;
	public qualified_alias_member(InputElement qualifier, InputElement right, IList typeargs) : base(null, right, typeargs) {
		this.qualifier = qualifier;
	}
	override public string ToString() {
		Debug.Assert(left == null);
		return qualifier.str + "::" + right.str;
	}
}

public class qualified_name: simple_name {
	public InputElement qualifier;
	public qualified_name(InputElement qualifier, InputElement id, IList typeargs) : base(id, typeargs) {
		this.qualifier = qualifier;
	}
}

public class real_literal: literal {
	public real_literal(InputElement token) {
		this.token = token;
	}
}

public abstract class resource: AST {
	public resource() {
	}
	[Typecheck] public Method dispose;	// dispose method for associated type
}

public class resource_decl: resource {
	public local_statement local;
	public resource_decl(local_statement local) {
		this.local = local;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		local.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck,MayBeNull] public Method method;	// conversion to IDisposable
}

public class resource_expr: resource {
	public expression expr;
	public resource_expr(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class return_statement: statement {
	[MayBeNull] public expression expr;
	public return_statement(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (expr != null)
			expr.visit(prefix, postfix);
		postfix(this);
	}
	[Rewrite] public bool exitstry;	// rewrite: true if return exits try block
}

public class sbyte_type: type {
	public sbyte_type() {
	}
}

public class short_type: type {
	public short_type() {
	}
}

public class simple_name: expression {
	public InputElement id;
	[MayBeNull] public typeList typeargs;
	public simple_name(InputElement id, IList typeargs) {
		this.id = id;
		this.typeargs = (typeList)typeargs;
	}
	[Bind2] public Symbol sym;	// bind
	[MayBeNull,Typecheck] public Method method;	// typecheck
	override public void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (typeargs != null)
			List.visit(typeargs, prefix, postfix);
		postfix(this);
	}
}

public class sizeof_expression: expression {
	public sizeof_expression(type ty) {
		this.ty = ty;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		postfix(this);
	}
}

public class stackalloc_initializer: variable_initializer {
	public expression expr;
	public stackalloc_initializer(type ty, expression expr) {
		this.ty = ty;
		this.expr = expr;
	}
	public type ty;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public abstract class statement: AST {
	public statement() {
	}
	[Bind1] public Method method;	// associated method
	[ILGen] public int lab;	// associated label or 0
}

public class string_literal: literal {
	public string_literal(InputElement token) {
		this.token = token;
	}
}

public class string_type: type {
	public string_type() {
	}
}

public class struct_declaration: type_declaration {
	public attribute_sectionList attrs;
	public type_parameterList typeparams;
	public type_parameter_constraints_clauseList constraints;
	public declarationList body;
	public InputElement id;
	public typeList interfaces;
	public struct_declaration(IList attrs, IList mods, InputElement id, IList typeparams, IList interfaces, IList constraints, IList body) {
		this.attrs = (attribute_sectionList)attrs;
		this.mods = (InputElementList)mods;
		this.id = id;
		this.typeparams = (type_parameterList)typeparams;
		this.interfaces = (typeList)interfaces;
		this.constraints = (type_parameter_constraints_clauseList)constraints;
		this.body = (declarationList)body;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		List.visit(interfaces, prefix, postfix);
		List.visit(body, prefix, postfix);
		postfix(this);
	}
	[Bind1] public StructType sym;	// bind: StructType for id
	[Bind1] override public Type typ { get { return sym; } }	// bind
}

public class switch_default: switch_label {
	public switch_default() {
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		postfix(this);
	}
}

public class switch_expression: switch_label {
	public expression expr;
	public switch_expression(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public abstract class switch_label: AST {
	public switch_label() {
	}
}

public class switch_section: AST {
	public switch_labelList labels;
	public statementList stmts;
	public switch_section(IList labels, IList stmts) {
		this.labels = (switch_labelList)labels;
		this.stmts = (statementList)stmts;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(labels, prefix, postfix);
		List.visit(stmts, prefix, postfix);
		postfix(this);
	}
	[ILGen] public int lab;	// ilgen: associated label
}

public class switch_statement: statement {
	public expression expr;
	public switch_sectionList sections;
	public switch_statement(expression expr, IList sections) {
		this.expr = expr;
		this.sections = (switch_sectionList)sections;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		List.visit(sections, prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Type typ;	// typecheck: switch expression type
	[Typecheck] public switch_expressionList values;	// typecheck: case label values
}

public class this_access: expression {
	public this_access() {
	}
	[Bind2] public ClassType sym;	// bind
}

public class this_initializer: constructor_initializer {
	public argumentList args;
	public this_initializer(IList args) {
		this.args = (argumentList)args;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(args, prefix, postfix);
		postfix(this);
	}
}

public class throw_statement: statement {
	[MayBeNull] public expression expr;
	public throw_statement(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (expr != null)
			expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class try_statement: statement {
	public statement block;
	[MayBeNull] public catch_clauses catches;
	[MayBeNull] public finally_clause finally_block;
	public try_statement(statement block, catch_clauses catches, finally_clause finally_block) {
		this.block = block;
		this.catches = catches;
		this.finally_block = finally_block;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		block.visit(prefix, postfix);
		if (catches != null)
			catches.visit(prefix, postfix);
		if (finally_block != null)
			finally_block.visit(prefix, postfix);
		postfix(this);
	}
}

public abstract class type: AST {
	public type() {
	}
	[Bind2] public Type sym;	// bind
}

public abstract class type_declaration: declaration {
	public type_declaration() {
	}
	[Emit] public System.Type type;	// emit
	[Emit] public TypeBuilder builder { get { return (TypeBuilder)type; } }	// emit
	[Bind1] abstract public Type typ { get; }	// bind
}

public class type_parameter: type {
	public attribute_sectionList attrs;
	public InputElement id;
	public type_parameter(IList attrs, InputElement id) {
		this.attrs = (attribute_sectionList)attrs;
		this.id = id;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(attrs, prefix, postfix);
		postfix(this);
	}
}

public class type_parameter_constraints_clause: AST {
	public InputElement id;
	public typeList constraints;
	public type_parameter_constraints_clause(InputElement id, IList constraints) {
		this.id = id;
		this.constraints = (typeList)constraints;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		List.visit(constraints, prefix, postfix);
		postfix(this);
	}
}

public class typeof_expression: expression {
	public type ty;
	public typeof_expression(type ty) {
		this.ty = ty;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		postfix(this);
	}
}

public class uint_type: type {
	public uint_type() {
	}
}

public class ulong_type: type {
	public ulong_type() {
	}
}

public class unary_declarator: operator_declarator {
	public InputElement id1;
	public InputElement op;
	public type t1;
	public unary_declarator(type ty, InputElement op, type t1, InputElement id1) {
		this.ty = ty;
		this.op = op;
		this.t1 = t1;
		this.id1 = id1;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		ty.visit(prefix, postfix);
		t1.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Formal sym;	// bind: symbol-table entry for id1
}

public class unary_expression: expression {
	public expression expr;
	public InputElement op;
	public unary_expression(InputElement op, expression expr) {
		this.op = op;
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
	[Typecheck] public Method method;	// typecheck
}

public class unchecked_expression: expression {
	public expression expr;
	public unchecked_expression(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class unchecked_statement: statement {
	public statement stmt;
	public unchecked_statement(statement stmt) {
		this.stmt = stmt;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		stmt.visit(prefix, postfix);
		postfix(this);
	}
}

public class unsafe_statement: statement {
	public statement block;
	public unsafe_statement(statement block) {
		this.block = block;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		block.visit(prefix, postfix);
		postfix(this);
	}
}

public class ushort_type: type {
	public ushort_type() {
	}
}

public abstract class using_directive: AST {
	public using_directive() {
	}
}

public class using_statement: statement {
	public statement body;
	public resource r;
	public using_statement(resource r, statement body) {
		this.r = r;
		this.body = body;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		r.visit(prefix, postfix);
		body.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Block sym;	// bind: Block for body
}

public class var_declarator: declarator {
	[MayBeNull] public variable_initializer init;
	public var_declarator(InputElement id, variable_initializer init) : base(id) {
		this.init = init;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		if (init != null)
			init.visit(prefix, postfix);
		postfix(this);
	}
	[Bind1] public Local sym;	// bind: symbol-table entry for id
}

public abstract class variable_initializer: AST {
	public variable_initializer() {
	}
	[Typecheck] public Type typ;	// typecheck: type of field or variable
}

public class void_pointer_type: type {
	public void_pointer_type() {
	}
}

public class void_type: type {
	public void_type() {
	}
}

public class while_statement: statement {
	public statement body;
	public expression expr;
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		body.visit(prefix, postfix);
		postfix(this);
	}
	public while_statement(expression expr, statement body) {
		this.expr = expr;
		this.body = body;
	}
}

public abstract class yield_statement: statement {
}

public class yield_return_statement: yield_statement {
	public expression expr;
	public yield_return_statement(expression expr) {
		this.expr = expr;
	}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		expr.visit(prefix, postfix);
		postfix(this);
	}
}

public class yield_break_statement: yield_statement {
	public yield_break_statement() {}
	public override void visit(ASTVisitor prefix, ASTVisitor postfix) {
		prefix(this);
		postfix(this);
	}
}
