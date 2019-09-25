using System;
using System.Collections;
using System.IO;
using System.Diagnostics;

public abstract class bind {
	protected MessageWriter msg;
	public bind(MessageWriter msg) { this.msg = msg; }
	public static void import(string name, Imports imp, MessageWriter msg) {
		if (!imp.Load(name))
			msg.Warning("can't find '{0}'", name);
	}
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		NameSpace global = null;
		if (msg.Count == 0) {
			global = ((compilation)ast).global;
			bool nostdlib = false;
			foreach (string s in ((compilation)ast).args)
				if (s.Replace('/', '-').ToLower() == "-nostdlib") {
					nostdlib = true;
					break;
				}
			if (!nostdlib) {
				import("mscorlib.dll", global.imports, msg);
				import("System.dll", global.imports, msg);
			}
			(new Pass1(msg)).compilation((compilation)ast, global.members);
		}
		if (msg.Count == 0)
			(new Pass2(msg)).compilation((compilation)ast, global.members);
		if (msg.Count == 0)
			(new Pass3(msg)).compilation((compilation)ast, global.members);
		return ast;
	}
	static public string binaryOpName(InputElement op) {
		return binaryOpName(op.str);
	}
	static public string binaryOpName(string op) {
		switch (op) {
		case "+":  return "op_Addition";
		case "-":  return "op_Subtraction";
		case "*":  return "op_Multiply";
		case "/":  return "op_Division";
		case "%":  return "op_Remainder";
		case "&&":
		case "&":  return "op_BitwiseAnd";
		case "||":
		case "|":  return "op_BitwiseOr";
		case "^":  return "op_BitwiseXor";
		case "<<": return "op_LeftShift";
		case ">>": return "op_RightShift";
		case "==": return "op_Equality";
		case "!=": return "op_Inequality";
		case ">":  return "op_GreaterThan";
		case "<":  return "op_LessThan";
		case ">=": return "op_GreaterThanOrEqual";
		case "<=": return "op_LessThanOrEqual";
		default: throw new ArgumentException(op);
		}
	}
	public static string unaryOpName(InputElement op) {
		return unaryOpName(op.str);
	}
	public static string unaryOpName(string op) {
		switch (op) {
		case "+":  return "op_UnaryPlus";
		case "-":  return "op_UnaryMinus";
		case "!":  return "op_LogicalNot";
		case "~":  return "op_OnesComplement";
		case "++": return "op_Increment";
		case "--": return "op_Decrement";
		case "true":  return "op_True";
		case "false": return "op_False";
		default: throw new ArgumentException(op);
		}
	}
	protected BuiltinTypes Type;
	public virtual void compilation(compilation ast) {
		Type = ast.global.Types;
		Type.msg = msg;
	}

	public abstract void namespace_declaration(namespace_declaration ast, SymbolTable bindings);
	public abstract void class_declaration(class_declaration ast, SymbolTable bindings);
	public abstract void constant_declaration(constant_declaration ast, SymbolTable bindings);
	public abstract void constructor_declaration(constructor_declaration ast, SymbolTable bindings);
	public abstract void delegate_declaration(delegate_declaration ast, SymbolTable bindings);
	public abstract void destructor_declaration(destructor_declaration ast, SymbolTable bindings);
	public abstract void enum_declaration(enum_declaration ast, SymbolTable bindings);
	public abstract void event_declaration1(event_declaration1 ast, SymbolTable bindings);
	public abstract void event_declaration2(event_declaration2 ast, SymbolTable bindings);
	public abstract void field_declaration(field_declaration ast, SymbolTable bindings);
	public abstract void indexer_declaration(indexer_declaration ast, SymbolTable bindings);
	public abstract void interface_declaration(interface_declaration ast, SymbolTable bindings);
	public abstract void interface_event_declaration(interface_event_declaration ast, SymbolTable bindings);
	public abstract void interface_indexer_declaration(interface_indexer_declaration ast, SymbolTable bindings);
	public abstract void interface_method_declaration(interface_method_declaration ast, SymbolTable bindings);
	public abstract void interface_property_declaration(interface_property_declaration ast, SymbolTable bindings);
	public abstract void method_declaration(method_declaration ast, SymbolTable bindings);
	public abstract void operator_declaration(operator_declaration ast, SymbolTable bindings);
	public abstract void property_declaration(property_declaration ast, SymbolTable bindings);
	public abstract void struct_declaration(struct_declaration ast, SymbolTable bindings);
	public virtual void declaration(declaration ast, SymbolTable bindings) {
		     if (ast is namespace_declaration) namespace_declaration((namespace_declaration)ast, bindings);
		else if (ast is class_declaration) class_declaration((class_declaration)ast, bindings);
		else if (ast is constant_declaration) constant_declaration((constant_declaration)ast, bindings);
		else if (ast is constructor_declaration) constructor_declaration((constructor_declaration)ast, bindings);
		else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast, bindings);
		else if (ast is destructor_declaration) destructor_declaration((destructor_declaration)ast, bindings);
		else if (ast is enum_declaration) enum_declaration((enum_declaration)ast, bindings);
		else if (ast is event_declaration1) event_declaration1((event_declaration1)ast, bindings);
		else if (ast is event_declaration2) event_declaration2((event_declaration2)ast, bindings);
		else if (ast is field_declaration) field_declaration((field_declaration)ast, bindings);
		else if (ast is indexer_declaration) indexer_declaration((indexer_declaration)ast, bindings);
		else if (ast is interface_declaration) interface_declaration((interface_declaration)ast, bindings);
		else if (ast is interface_event_declaration) interface_event_declaration((interface_event_declaration)ast, bindings);
		else if (ast is interface_indexer_declaration) interface_indexer_declaration((interface_indexer_declaration)ast, bindings);
		else if (ast is interface_method_declaration) interface_method_declaration((interface_method_declaration)ast, bindings);
		else if (ast is interface_property_declaration) interface_property_declaration((interface_property_declaration)ast, bindings);
		else if (ast is method_declaration) method_declaration((method_declaration)ast, bindings);
		else if (ast is operator_declaration) operator_declaration((operator_declaration)ast, bindings);
		else if (ast is property_declaration) property_declaration((property_declaration)ast, bindings);
		else if (ast is struct_declaration) struct_declaration((struct_declaration)ast, bindings);
		else throw new ArgumentException();
	}

	public abstract void binary_declarator(binary_declarator ast, SymbolTable bindings);
	public abstract void explicit_declarator(explicit_declarator ast, SymbolTable bindings);
	public abstract void implicit_declarator(implicit_declarator ast, SymbolTable bindings);
	public abstract void unary_declarator(unary_declarator ast, SymbolTable bindings);
	public virtual void operator_declarator(operator_declarator ast, SymbolTable bindings) {
		     if (ast is binary_declarator) binary_declarator((binary_declarator)ast, bindings);
		else if (ast is explicit_declarator) explicit_declarator((explicit_declarator)ast, bindings);
		else if (ast is implicit_declarator) implicit_declarator((implicit_declarator)ast, bindings);
		else if (ast is unary_declarator) unary_declarator((unary_declarator)ast, bindings);
		else throw new ArgumentException();
	}
	
	public abstract void arglist_parameter(arglist_parameter ast, SymbolTable bindings);
	public abstract void fixed_parameter(fixed_parameter ast, SymbolTable bindings);
	public abstract void params_parameter(params_parameter ast, SymbolTable bindings);
	public virtual void parameter(parameter ast, SymbolTable bindings) {
		     if (ast is arglist_parameter) arglist_parameter((arglist_parameter)ast, bindings);
		else if (ast is fixed_parameter) fixed_parameter((fixed_parameter)ast, bindings);
		else if (ast is params_parameter) params_parameter((params_parameter)ast, bindings);
		else throw new ArgumentException();
	}
	public virtual void block_statement(block_statement ast, SymbolTable bindings) {}
	public virtual void break_statement(break_statement ast, SymbolTable bindings) {}
	public virtual void checked_statement(checked_statement ast, SymbolTable bindings) {}
	public virtual void const_statement(const_statement ast, SymbolTable bindings) {}
	public virtual void continue_statement(continue_statement ast, SymbolTable bindings) {}
	public virtual void do_statement(do_statement ast, SymbolTable bindings) {}
	public virtual void empty_statement(empty_statement ast, SymbolTable bindings) {}
	public virtual void expression_statement(expression_statement ast, SymbolTable bindings) {}
	public virtual void fixed_statement(fixed_statement ast, SymbolTable bindings) {}
	public virtual void foreach_statement(foreach_statement ast, SymbolTable bindings) {}
	public virtual void for_statement(for_statement ast, SymbolTable bindings) {}
	public virtual void goto_case_statement(goto_case_statement ast, SymbolTable bindings) {}
	public virtual void goto_default_statement(goto_default_statement ast, SymbolTable bindings) {}
	public virtual void goto_statement(goto_statement ast, SymbolTable bindings) {}
	public virtual void if_statement(if_statement ast, SymbolTable bindings) {}
	public virtual void labeled_statement(labeled_statement ast, SymbolTable bindings) {}
	public virtual void local_statement(local_statement ast, SymbolTable bindings) {}
	public virtual void lock_statement(lock_statement ast, SymbolTable bindings) {}
	public virtual void return_statement(return_statement ast, SymbolTable bindings) {}
	public virtual void switch_statement(switch_statement ast, SymbolTable bindings) {}
	public virtual void throw_statement(throw_statement ast, SymbolTable bindings) {}
	public virtual void try_statement(try_statement ast, SymbolTable bindings) {}
	public virtual void unchecked_statement(unchecked_statement ast, SymbolTable bindings) {}
	public virtual void unsafe_statement(unsafe_statement ast, SymbolTable bindings) { }
	public virtual void using_statement(using_statement ast, SymbolTable bindings) {}
	public virtual void while_statement(while_statement ast, SymbolTable bindings) {}
	public virtual void statement(statement ast, SymbolTable bindings) {
		     if (ast is block_statement) block_statement((block_statement)ast, bindings);
		else if (ast is break_statement) break_statement((break_statement)ast, bindings);
		else if (ast is checked_statement) checked_statement((checked_statement)ast, bindings);
		else if (ast is const_statement) const_statement((const_statement)ast, bindings);
		else if (ast is continue_statement) continue_statement((continue_statement)ast, bindings);
		else if (ast is do_statement) do_statement((do_statement)ast, bindings);
		else if (ast is empty_statement) empty_statement((empty_statement)ast, bindings);
		else if (ast is expression_statement) expression_statement((expression_statement)ast, bindings);
		else if (ast is fixed_statement) fixed_statement((fixed_statement)ast, bindings);
		else if (ast is foreach_statement) foreach_statement((foreach_statement)ast, bindings);
		else if (ast is for_statement) for_statement((for_statement)ast, bindings);
		else if (ast is goto_case_statement) goto_case_statement((goto_case_statement)ast, bindings);
		else if (ast is goto_default_statement) goto_default_statement((goto_default_statement)ast, bindings);
		else if (ast is goto_statement) goto_statement((goto_statement)ast, bindings);
		else if (ast is if_statement) if_statement((if_statement)ast, bindings);
		else if (ast is labeled_statement) labeled_statement((labeled_statement)ast, bindings);
		else if (ast is local_statement) local_statement((local_statement)ast, bindings);
		else if (ast is lock_statement) lock_statement((lock_statement)ast, bindings);
		else if (ast is return_statement) return_statement((return_statement)ast, bindings);
		else if (ast is switch_statement) switch_statement((switch_statement)ast, bindings);
		else if (ast is throw_statement) throw_statement((throw_statement)ast, bindings);
		else if (ast is try_statement) try_statement((try_statement)ast, bindings);
		else if (ast is unchecked_statement) unchecked_statement((unchecked_statement)ast, bindings);
		else if (ast is unsafe_statement) unsafe_statement((unsafe_statement)ast, bindings);
		else if (ast is using_statement) using_statement((using_statement)ast, bindings);
		else if (ast is while_statement) while_statement((while_statement)ast, bindings);
		else throw new ArgumentException();
	}
	abstract public Symbol dotted_name(dotted_name ast, SymbolTable bindings);
	public virtual Type type(type ast, SymbolTable bindings) {
		if (ast is array_type)
			return new ArrayType(type(((array_type)ast).ty, bindings), ((array_type)ast).rank_specifier + 1, Type.Array);
		else if (ast is bool_type) return Type.Bool;
		else if (ast is byte_type) return Type.Byte;
		else if (ast is char_type) return Type.Char;
		else if (ast is decimal_type) return Type.Decimal;
		else if (ast is double_type) return Type.Double;
		else if (ast is float_type) return Type.Float;
		else if (ast is int_type) return Type.Int;
		else if (ast is long_type) return Type.Long;
		else if (ast is name_type) {
			Type ty = dotted_name(((name_type)ast).name, bindings) as Type;
			if (ty == null)
				ty = Type.Int;
			return ty;
		} else if (ast is object_type) return Type.Object;
		else if (ast is pointer_type) return new UnmanagedPointerType(type(((pointer_type)ast).ty, bindings));
		else if (ast is sbyte_type) return Type.SByte;
		else if (ast is short_type) return Type.Short;
		else if (ast is string_type) return Type.String;
		else if (ast is uint_type) return Type.UInt;
		else if (ast is ulong_type) return Type.ULong;
		else if (ast is ushort_type) return Type.UShort;
		else if (ast is void_pointer_type) return new UnmanagedPointerType(Type.Void);
		else if (ast is void_type) return Type.Void;
		else throw new ArgumentException();
	}
}

public class Pass1: bind {
	string unsafeModifier = "";
	public Pass1(MessageWriter msg) : base(msg) {}

	public virtual void AddModifiers(Symbol t, InputElementList mods, string validModifiers, string defaultaccess) {
		int count = 0;
		validModifiers += unsafeModifier;
		stringList modifiers = new stringList();
		for (int i = 0; i < mods.Count; i++) {
			string m = mods[i].str;
			if (modifiers.Contains(m))
				msg.Error(mods[i], "duplicate '{0}' modifier", m);
			else if (validModifiers.IndexOf(m) < 0) {
				if (m == "unsafe")
					msg.Error(mods[i], "unsafe code permitted only when compiling with /unsafe");
				else
					msg.Error(mods[i], "'{0}' modifier is not permitted in this context", m);
			} else if (m == "protected" && modifiers.Contains("internal")
			     ||  m == "internal"  && modifiers.Contains("protected"))
				modifiers.Add(m);
			else {
				if (m == "private"   || m == "public"
			    ||  m == "protected" || m == "internal")
					if (++count >= 2)
						msg.Error(mods[i], "more than one access modifier");
				modifiers.Add(m);
			}
		}
		if (count == 0 && defaultaccess != null)
			modifiers.Add(defaultaccess);
		t.Modifiers = modifiers;
	}
	override public void arglist_parameter(arglist_parameter ast, SymbolTable bindings) {
		ast.method.AddFormal(ast.arglist, msg);
	}
	public virtual void argument(argument ast, SymbolTable bindings) {
	}
	public virtual void attribute(attribute ast, SymbolTable bindings) {
		if (ast.arguments != null)
			attribute_arguments(ast.arguments, bindings);
	}
	public virtual void attribute_arguments(attribute_arguments ast, SymbolTable bindings) {
		foreach (named_argument x in ast.namedargs)
			named_argument(x, bindings);
	}
	public virtual void attribute_section(attribute_section ast, SymbolTable bindings) {
		foreach (attribute x in ast.attributes)
			attribute(x, bindings);
	}
	public virtual void attribute_sections(attribute_sectionList attrs, SymbolTable bindings) {
		foreach (attribute_section x in attrs)
			attribute_section(x, bindings);
	}
	override public void binary_declarator(binary_declarator ast, SymbolTable bindings) {
		ClassType c = (ClassType)bindings.Owner;
		Method m = c.AddMethod(new InputElement(binaryOpName(ast.op), ast.begin), msg);
		ast.sym1 = m.AddFormal(ast.id1, msg);
		ast.sym2 = m.AddFormal(ast.id2, msg);
		ast.method = m;
	}
	override public void block_statement(block_statement ast, SymbolTable bindings) {
		Block b = new Block(bindings);
		foreach (statement x in ast.stmts)
			statement(x, b.locals);
		ast.sym = b;
	}
	override public void break_statement(break_statement ast, SymbolTable bindings) {
		ast.stmt = loop_exit(ast, "break");
	}
	public virtual void catch_clause(catch_clause ast, SymbolTable bindings) {
		Debug.Assert(bindings.Owner is Block);
		statement(ast.block, bindings);
		if (ast.id != null)
			ast.sym = ((block_statement)ast.block).sym.AddLocal(ast.id, msg);
	}
	public virtual void catch_clauses(catch_clauses ast, SymbolTable bindings) {
		foreach (catch_clause x in ast.specifics)
			catch_clause(x, bindings);
		if (ast.general != null)
			statement(ast.general, bindings);
	}
	public virtual void CheckIndexers(attribute_sectionList attrs, declarationList decls) {
		foreach (declaration d in decls)
			if (d is indexer_declaration || d is interface_indexer_declaration) {
				// [System.Reflection.DefaultMemberAttribute("Item")]
				dotted_name name = null;
				foreach (string id in new string[] { "System", "Reflection", "DefaultMemberAttribute" })
					name = new dotted_name(name, new InputElement(id));
				string_literal Item = new string_literal(new InputElement("string-literal", "\"Item\"", "", 0, 0));
				attribute_section ast = new attribute_section(null, attributeList.New(new attribute(
					new name_type(name),
					new attribute_arguments(expressionList.New(Item), named_argumentList.New()))));
				attrs.Add(ast);
				break;
			}
	}
	override public void checked_statement(checked_statement ast, SymbolTable bindings) {
		statement(ast.stmt, bindings);
	}
	public virtual void CheckMethodModifiers(Symbol t) {
		if (t.IsAny("static", "virtual", "override") > 1)
			msg.Error(t.id, "{0} '{1}' cannot specify more than one of 'static', 'virtual', or 'override'", t.Kind, t.FullName);
		if (t.IsAny("new", "override") > 1)
			msg.Error(t.id, "{0} '{1}' cannot specify 'new' and 'override'", t.Kind, t.FullName);
		if (t.Is("abstract") && t.IsAny("static", "virtual", "extern") > 0)
			msg.Error(t.id, "abstract {0} '{1}' cannot specify any of 'static', 'virtual' or 'extern'", t.Kind, t.FullName);
		if (t.Is("private") && t.IsAny("abstract", "virtual", "override") > 0)
			msg.Error(t.id, "private {0} '{1}' cannot specify any of 'abstract', 'virtual' or 'override'", t.Kind, t.FullName);
		if (t.Is("sealed") && !t.Is("override"))
			msg.Error(t.id, "sealed {0} '{1}' must also specify 'override'", t.Kind, t.FullName);
		if (t.Name == t.declSpace.Owner.Name)
			msg.Error(t.id, "{0} '{1}' cannot be the same as its enclosing type '{2}'", t.Kind, t.Name, t.declSpace.Owner.FullName);
	}	
	override public void class_declaration(class_declaration ast, SymbolTable bindings) {
		ClassType t = new ClassType(ast.id, bindings);
		if (bindings.Owner is ClassType)
			t.enclosingType = (ClassType)bindings.Owner;
		CheckIndexers(ast.attrs, ast.body);
		attribute_sections(ast.attrs, bindings);
		t.Add(ast.id, bindings, msg);
		AddModifiers(t, ast.mods, "new public protected internal private abstract sealed",
			bindings.Owner is ClassType ? "private" : "internal");
		if (t.Is("abstract") && t.Is("sealed"))
			msg.Error(t.id, "{0} '{1}' cannot be 'abstract' and 'sealed'", t.Kind, t.FullName);
		foreach (declaration x in ast.body)
			declaration(x, t.members);
		default_constructors(t, ast, ast.body);
		ast.sym = t;
	}
	public virtual void compilation(compilation ast, SymbolTable bindings) {
		foreach (string s in ast.args)
			if (s.Replace('/', '-').ToLower() == "-unsafe") {
				unsafeModifier = " unsafe";
				break;
			}
		base.compilation(ast);
		foreach (compilation_unit x in ast.inputs)
			compilation_unit(x, bindings);
	}
	public virtual void compilation_unit(compilation_unit ast, SymbolTable bindings) {
		ast.sym = (NameSpace)bindings.Owner;
		SymbolList usingdirectives = new SymbolList();
		foreach (using_directive x in ast.using_directives)
			using_directive(x, bindings, usingdirectives);
		ast.sym.usingdirectives = usingdirectives;
		attribute_sections(ast.attributes, bindings);
		foreach (declaration x in ast.declarations) {
			declaration(x, bindings);
			if (contains(x.mods, "protected") || contains(x.mods, "private"))
				msg.Error(x.begin, "Namespace members cannot be declared 'private' or 'protected'");
		}
		ast.sym.usingdirectives = null;
	}
	override public void const_statement(const_statement ast, SymbolTable bindings) {
		Block b = (Block)bindings.Owner;
		foreach (const_declarator x in ast.consts) {
			x.sym = b.AddConstant(x.id, msg);
			x.sym.value = x;	// signifies "undefined"
		}
	}
	override public void constant_declaration(constant_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ClassType c = (ClassType)bindings.Owner;
		foreach (const_declarator x in ast.decls) {
			x.sym = c.AddConstant(x.id, msg);
			AddModifiers(x.sym, ast.mods, "new public protected internal private", "private");
			x.sym.value = x;	// signifies "undefined"
		}
	}
	override public void constructor_declaration(constructor_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		Constructor t;
		if (contains(ast.mods, "static")) {
			t = static_constructor_declarator(ast.decl, bindings);
			AddModifiers(t, ast.mods, "static extern", "private");
		} else {
			t = constructor_declarator(ast.decl, bindings);
			AddModifiers(t, ast.mods, "public protected internal private extern", "private");
		}
		method_body(t, ast, ast.block, t.locals);
		ast.sym = t;
	}
	public virtual Constructor constructor_declarator(constructor_declarator ast, SymbolTable bindings) {
		ClassType c = (ClassType)bindings.Owner;
		if (c.Name != ast.id.str)
			msg.Error(ast.id, "'{0}' is an invalid constructor name", ast.id.str);
		Constructor t = c.AddConstructor(ast.id, msg);
		formals(ast.f, bindings, t);
		if (c is StructType) {
			if (t.ArgCount == 0 && t.IsInstance)
				msg.Error(ast.id, "structs may not declare a parameterless instance constructor");
			if (ast.init is base_initializer)
				msg.Error(ast.id, "struct instance constructors may not specify a base initializer");
		} else if (ast.init == null && t.IsInstance && c.baseClass != null) {
			ast.init = new base_initializer(new argumentList());
			ast.init.link(ast);
			ast.init.begin = ast.begin;
			ast.init.end = ast.end;
		}
		return t;
	}
	public static bool contains(InputElementList mods, string modifier) {
		foreach (InputElement x in mods)
			if (x.str == modifier)
				return true;
		return false;
	}
	override public void continue_statement(continue_statement ast, SymbolTable bindings) {
		ast.stmt = loop_exit(ast, "continue");
	}
	public virtual void default_constructors(ClassType t, declaration ast, declarationList body) {
		bool needstatic = false, needinstance = true;
		foreach (declaration d in body)
			if (d is field_declaration)
				foreach (field_declarator f in ((field_declaration)d).decls)
					if (f.sym.IsStatic && f.init != null)
						needstatic = true;
		foreach (declaration d in body)
			if (d is constructor_declaration)
				if (((constructor_declaration)d).sym.IsInstance)
					needinstance = false;
				else
					needstatic = false;		
		if (needinstance || t is StructType) {
			constructor_declaration decl =
				new constructor_declaration(
					attribute_sectionList.New(),
					InputElementList.New(new InputElement(t.Is("abstract") ? "protected" : "public")),
					new constructor_declarator(
						new InputElement(t.Name),
						new formals(parameterList.New(), null),
						new base_initializer(new argumentList())),
					new block_statement(statementList.New()));
			decl.link(ast);
			declaration(decl, t.members);
			body.Add(decl);
		}
		if (needstatic) {
			constructor_declaration decl =
				new constructor_declaration(
					attribute_sectionList.New(),
					InputElementList.New(new InputElement("static")),
					new constructor_declarator(
						new InputElement(t.Name),
						new formals(parameterList.New(), null),
						null),
				new block_statement(statementList.New()));
			decl.link(ast);
			declaration(decl, t.members);
			body.Add(decl);
		}
	}
	override public void delegate_declaration(delegate_declaration ast, SymbolTable bindings) {
		DelegateType t = new DelegateType(ast.id, bindings);
		t.baseClass = Type.MulticastDelegate;
		attribute_sections(ast.attrs, bindings);
		t.Add(ast.id, bindings, msg);
		AddModifiers(t, ast.mods, "new public protected internal private",
			bindings.Owner is ClassType ? "private" : "internal");
		t.Modifiers.Add("sealed");
		// Invoke
		t.invoke = t.AddMethod(new InputElement("Invoke", ast.id.coord), msg);
		t.invoke.Modifiers.Add("public");
		t.invoke.Modifiers.Add("virtual");
		formals(ast.f, t.invoke.locals, t.invoke);
		// constructor
		Method m = t.AddConstructor(ast.id, msg);
		m.Modifiers.Add("public");
		m.AddFormal(new InputElement("object", ast.id.coord), msg).Type = Type.Object;
		m.AddFormal(new InputElement("method", ast.id.coord), msg).Type = Type.IntPtr;
		m.Type = Type.Void;
		ast.sym = t;
	}
	override public void destructor_declaration(destructor_declaration ast, SymbolTable bindings) {
		ClassType c = (ClassType)bindings.Owner;
		attribute_sections(ast.attrs, bindings);
		if (c.Name != ast.id.str)
			msg.Error(ast.id, "'{0}' is an invalid destructor name", ast.id.str);
		if (c is StructType)
			msg.Error(ast.id, "structs may not declare a destructor");
		Method t = c.AddMethod(new InputElement("Finalize", ast.id.coord), msg);
		AddModifiers(t, ast.mods, "extern", "private");
		method_body(t, ast, ast.block, t.locals);
		ast.sym = t;
	}
	override public void do_statement(do_statement ast, SymbolTable bindings) {
		statement(ast.body, bindings);
	}
	override public Symbol dotted_name(dotted_name ast, SymbolTable bindings) {
		Symbol t;
		NameSpace n = (NameSpace)bindings.Owner;
		if (ast.left != null) {
			n = (NameSpace)dotted_name(ast.left, bindings);
			if (n == null)
				return null;
			t = n[ast.right.str];
		} else
			t = n.Lookup(ast.right, msg);	// searches using namespaces, too
		if (t == null) {
			t = new NameSpace(ast.right, n.members);
			t.Add(ast.right, msg);
		}
		return t as NameSpace;
	}
	override public void enum_declaration(enum_declaration ast, SymbolTable bindings) {
		EnumType t = new EnumType(ast.id, bindings);
		if (bindings.Owner is ClassType)
			t.enclosingType = (ClassType)bindings.Owner;
		attribute_sections(ast.attrs, bindings);
		t.Add(ast.id, bindings, msg);
		AddModifiers(t, ast.mods, "new public protected internal private",
			bindings.Owner is ClassType ? "private" : "internal");
		foreach (enum_member_declaration x in ast.body)
			enum_member_declaration(x, t.members);
		ast.sym = t;
	}
	public virtual void enum_member_declaration(enum_member_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		EnumType c = (EnumType)bindings.Owner;
		ast.sym = c.AddEnumMember(ast.id, msg);
		ast.sym.value = ast;	// signifies "undefined"
	}
	public virtual void event_accessor(event_accessor ast, Event t, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		Method m = ast.id.str == "add" ? t.Add : t.Remove;
		method_body(t, ast, ast.block, m.locals);
		m.Modifiers = t.Modifiers;
		ast.sym = m;
	}
	override public void event_declaration1(event_declaration1 ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ClassType c = (ClassType)bindings.Owner;
		foreach (event_declarator x in ast.decls) {
			Event t = c.AddEvent(x.id, msg);
			t.IsFieldLike = true;
			AddModifiers(t, ast.mods, "new public protected internal private static virtual sealed override abstract extern", "private");
			CheckMethodModifiers(t);
			t.Add.Type = Type.Void;
			t.Add.Modifiers = t.Modifiers;
			t.Remove.Type = Type.Void;
			t.Remove.Modifiers = t.Modifiers;
			x.sym = t;
		}
	}
	override public void event_declaration2(event_declaration2 ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ClassType c = (ClassType)bindings.Owner;
		Event t = c.AddEvent(member_name(ast.name, bindings), msg);
		if (ast.name.ty != null)
			AddModifiers(t, ast.mods, "extern", "private");
		else {
			AddModifiers(t, ast.mods, "new public protected internal private static virtual sealed override", "private");
			CheckMethodModifiers(t);
		}
		foreach (event_accessor x in ast.accessors)
			event_accessor(x, t, bindings);
		t.Add.Type = Type.Void;
		t.Remove.Type = Type.Void;
		ast.sym = t;
	}
	override public void explicit_declarator(explicit_declarator ast, SymbolTable bindings) {
		ClassType c = (ClassType)bindings.Owner;
		Method m = c.AddMethod(new InputElement("op_Explicit", ast.begin), msg);
		ast.sym = m.AddFormal(ast.id1, msg);
		ast.method = m;
	}
	override public void field_declaration(field_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ClassType c = (ClassType)bindings.Owner;
		foreach (field_declarator x in ast.decls) {
			Field t = c.AddField(x.id, msg);
			AddModifiers(t, ast.mods, "new public protected internal private static readonly volatile", "private");
			if (t.Name == c.Name)
				msg.Error(t.id, "{0} '{1}' cannot be the same as its enclosing type '{2}'",
					t.Kind, t.Name, c.FullName);
			if (t.Is("readonly") && t.Is("volatile"))
				msg.Error(t.id, "{0} {1} cannot be 'readonly' and 'volatile'", t.Kind, t.FullName);
			if (x.init != null) {
				if (c is StructType && t.IsInstance)
					msg.Error(x.id, "struct instance field '{1}' cannot have an initializer", x.id.str);
			}
			t.Modifiers.Remove("new");
			x.sym = t;
		}
	}
	override public void fixed_parameter(fixed_parameter ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ast.method.AddFormal(ast.id, msg).modifier = ast.mod;
	}
	override public void fixed_statement(fixed_statement ast, SymbolTable bindings) {
		Block b = (Block)bindings.Owner;
		foreach (fixed_declarator x in ast.declarators)
			x.sym = b.AddLocal(x.id, msg);
		statement(ast.body, bindings);
	}
	override public void for_statement(for_statement ast, SymbolTable bindings) {
		Block b = new Block(bindings);
		statement(ast.body, b.locals);
		ast.sym = b;
	}
	override public void foreach_statement(foreach_statement ast, SymbolTable bindings) {
		Block b = new Block(bindings);
		Local t = b.AddLocal(ast.id, msg);
		t.ReadOnly = true;
		statement(ast.body, b.locals);
		ast.sym = t;
	}
	public virtual void formals(formals ast, SymbolTable bindings, Method m) {
		foreach (parameter x in ast.fixeds) {
			x.method = m;
			parameter(x, bindings);
		}
		if (ast.param != null) {
			ast.param.method = m;
			parameter(ast.param, bindings);
		}
	}
	override public void if_statement(if_statement ast, SymbolTable bindings) {
		statement(ast.thenpart, bindings);
		if (ast.elsepart != null)
			statement(ast.elsepart, bindings);
	}
	override public void implicit_declarator(implicit_declarator ast, SymbolTable bindings) {
		ClassType c = (ClassType)bindings.Owner;
		Method m = c.AddMethod(new InputElement("op_Implicit", ast.begin), msg);
		ast.sym = m.AddFormal(ast.id1, msg);
		ast.method = m;
	}
	override public void indexer_declaration(indexer_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ClassType c = (ClassType)bindings.Owner;
		string prefix = "";
		if (ast.i.interfacename != null)
			prefix = ast.i.interfacename.name.ToString() + ".";
		foreach (accessor_declaration x in ast.accessors) {
			attribute_sections(x.attrs, bindings);
			Method m = c.AddMethod(new InputElement(prefix + x.id.str + "_Item", x.id.coord), msg);
			if (ast.i.interfacename != null)
				AddModifiers(m, ast.mods, "extern", "private");
			else {
				AddModifiers(m, ast.mods, "new public protected internal private virtual sealed override abstract extern", "private");
				CheckMethodModifiers(m);
			}
			formals(ast.i.f, bindings, m);
			if (x.id.str == "set") {
				Formal value = m.AddFormal(new InputElement("value", x.id.coord), msg);
				m.signature.formals.Remove(value);
			}
			method_body(m, x, x.body, m.locals);
			x.sym = m;
		}
	}
	override public void interface_declaration(interface_declaration ast, SymbolTable bindings) {
		InterfaceType t = new InterfaceType(ast.id, bindings);
		t.Add(ast.id, bindings, msg);
		CheckIndexers(ast.attrs, ast.body);
		attribute_sections(ast.attrs, bindings);
		AddModifiers(t, ast.mods, "new public protected internal private",
			 bindings.Owner is ClassType ? "private" : "internal");
		foreach (declaration x in ast.body)
			declaration(x, t.members);
		ast.sym = t;
	}
	override public void interface_event_declaration(interface_event_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		InterfaceType c = (InterfaceType)bindings.Owner;
		Event t = c.AddEvent(ast.id, msg);
		AddModifiers(t, ast.mods, "new", "public");
		CheckMethodModifiers(t);
		foreach (string mod in t.Modifiers) {
			t.Add.Modifiers.Add(mod);
			t.Remove.Modifiers.Add(mod);
		}
		t.Add.Type = Type.Void;
		t.Add.Modifiers.Add("abstract");
		t.Add.Modifiers.Add("virtual");
		t.Remove.Type = Type.Void;
		t.Remove.Modifiers.Add("abstract");
		t.Remove.Modifiers.Add("virtual");
		ast.sym = t;
	}
	override public void interface_indexer_declaration(interface_indexer_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		InterfaceType c = (InterfaceType)bindings.Owner;
		foreach (accessor_declaration x in ast.accessors) {
			attribute_sections(x.attrs, bindings);
			Method m = c.AddMethod(new InputElement(x.id.str + "_Item", x.id.coord), msg);
			formals(ast.f, bindings, m);
			if (x.id.str == "set") {
				Formal value = m.AddFormal(new InputElement("value", x.id.coord), msg);
				m.signature.formals.Remove(value);
			}
			m.Modifiers.Add("public");
			m.Modifiers.Add("abstract");
			m.Modifiers.Add("virtual");
			x.sym = m;
		}
	}
	override public void interface_method_declaration(interface_method_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		InterfaceType c = (InterfaceType)bindings.Owner;
		Method t = c.AddMethod(ast.id, msg);
		AddModifiers(t, ast.mods, "new", "public");
		formals(ast.f, bindings, t);
		t.Modifiers.Add("abstract");
		t.Modifiers.Add("virtual");
		ast.sym = t;
	}
	override public void interface_property_declaration(interface_property_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		InterfaceType c = (InterfaceType)bindings.Owner;
		Property t = c.AddProperty(ast.id, msg);
		AddModifiers(t, ast.mods, "new", "public");
		foreach (accessor_declaration x in ast.accessors) {
			attribute_sections(x.attrs, bindings);
			Method m;
			if (x.id.str == "get")
				m = t.AddGet(ast.id);
			else {
				m = t.AddSet(ast.id);
				m.Type = Type.Void;
			}
			m.Modifiers.Add("public");
			m.Modifiers.Add("abstract");
			m.Modifiers.Add("virtual");
			x.sym = m;
		}
		ast.sym = t;
	}
	override public void labeled_statement(labeled_statement ast, SymbolTable bindings) {
		ast.sym = ((Block)bindings.Owner).AddLabel(ast.label, msg);
		ast.sym.definition = ast;
		statement(ast.stmt, bindings);
	}
	override public void lock_statement(lock_statement ast, SymbolTable bindings) {
		statement(ast.body, bindings);
	}
	public virtual statement loop_exit(statement ast, string kind) {
		for (AST s = ast; s != null; s = s.parent) {
			if (s is finally_clause) {
				msg.Error(ast.begin, "invalid '{0}' statement: '{0}' cannot exit a finally block", kind);
				return null;
			}
			if (s is switch_statement
			||  s is for_statement || s is foreach_statement
			||  s is do_statement  || s is while_statement)
				return (statement)s;
		}
		msg.Error(ast.begin, "invalid '{0}' statement", kind);
		return null;
	}
	public virtual InputElement member_name(member_name ast, SymbolTable bindings) {
		if (ast.ty is name_type)
			return new InputElement(((name_type)ast.ty).name.ToString() + "." + ast.id.str, ast.id.coord);
		else
			return ast.id;
	}
	public virtual void method_body(Symbol t, AST ast, statement block, SymbolTable bindings) {
		if (t.IsAny("extern", "abstract") > 0 && block != null)
			msg.Error(block.begin, "extraneous method body");
		else if (t.IsAny("extern", "abstract") == 0 && block == null)
			msg.Error(ast.end, "missing method body");
		if (block != null)
			statement(block, bindings);
	}
	override public void method_declaration(method_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ClassType c = (ClassType)bindings.Owner;
		Method t = c.AddMethod(member_name(ast.name, bindings), msg);
		if (ast.name.ty != null)
			AddModifiers(t, ast.mods, "extern", "private");
		else if (c is StructType)
			AddModifiers(t, ast.mods, "new public protected internal private static sealed override extern", "private");
		else
			AddModifiers(t, ast.mods, "new public protected internal private static virtual sealed override abstract extern", "private");
		CheckMethodModifiers(t);
		formals(ast.parms, bindings, t);
		method_body(t, ast, ast.body, t.locals);
		ast.sym = t;
	}
	public virtual void named_argument(named_argument ast, SymbolTable bindings) {
	}
	public virtual void namespace_body(namespace_body ast, SymbolTable bindings) {
		NameSpace t = (NameSpace)bindings.Owner;
		SymbolList usingdirectives = new SymbolList();
		foreach (using_directive x in ast.ud)
			using_directive(x, bindings, usingdirectives);
		t.usingdirectives = usingdirectives;
		foreach (declaration x in ast.declarations) {
			declaration(x, bindings);
			if (contains(x.mods, "protected") || contains(x.mods, "private"))
				msg.Error(x.begin, "namespace members cannot be declared 'private' or 'protected'");
		}
		t.usingdirectives = null;
	}
	override public void namespace_declaration(namespace_declaration ast, SymbolTable bindings) {
		ast.sym = (NameSpace)dotted_name(ast.id, bindings);
		if (ast.sym == null)
			msg.Error(ast.id.begin, "'{0}' is not a namespace", ast.id.ToString());
		namespace_body(ast.nb, ast.sym == null ? bindings : ast.sym.members);
	}
	override public void operator_declaration(operator_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		operator_declarator(ast.op, bindings);
		Method m = ast.op.method;
		AddModifiers(m, ast.mods, "extern static public", null);
		if (!m.Is("public") && !m.Is("static"))
			msg.Error(ast.op.begin, "operators must declared 'public' and 'static'");
		method_body(m, ast, ast.block, m.locals);
		ast.sym = m;
	}
	override public void params_parameter(params_parameter ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ast.method.AddFormal(ast.id, msg).IsParams = true;
	}
	override public void property_declaration(property_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		ClassType c = (ClassType)bindings.Owner;
		Property t = c.AddProperty(member_name(ast.name, bindings), msg);
		if (ast.name.ty != null)
			AddModifiers(t, ast.mods, "extern", "private");
		else {
			AddModifiers(t, ast.mods, "new public protected internal private static virtual sealed override abstract extern", "private");
			CheckMethodModifiers(t);
		}
		foreach (accessor_declaration x in ast.decls) {
			attribute_sections(x.attrs, bindings);
			Method m;
			if (x.id.str == "get")
				m = t.AddGet(member_name(ast.name, bindings));
			else {
				m = t.AddSet(member_name(ast.name, bindings));
				m.Type = Type.Void;
			}
			method_body(t, x, x.body, m.locals);
			m.Modifiers = t.Modifiers;
			x.sym = m;
		}
		ast.sym = t;
	}
	public virtual Block resource(resource ast, SymbolTable bindings) {
		if (ast is resource_expr)
			return (Block)bindings.Owner;
		if (ast is resource_decl) {
			foreach (var_declarator x in ((resource_decl)ast).local.vars)
				if (x.init == null)
					msg.Error(x.begin, "missing initializer");
			return new Block(bindings);
		}
		throw new ArgumentException();
	}
	public virtual void return_statement(statement ast, SymbolTable bindings) {
		if (Pass3.find_finally(ast) != null)
			msg.Error(ast.begin, "invalid 'return' statement: 'return' cannot exit a finally block");
	}
	override public void statement(statement ast, SymbolTable bindings) {
		if (bindings.Owner is Method)
			ast.method = (Method)bindings.Owner;
		else
			ast.method = ((Block)bindings.Owner).GetMethod();
		base.statement(ast, bindings);
	}
	public virtual Constructor static_constructor_declarator(constructor_declarator ast, SymbolTable bindings) {
		ClassType c = (ClassType)bindings.Owner;
		if (c.Name != ast.id.str)
			msg.Error(ast.id, "'{0}' is an invalid static constructor name", ast.id.str);
		Constructor t = c.AddConstructor(ast.id, msg);
		formals(ast.f, bindings, t);
		if (ast.init != null)
			msg.Error(ast.id, "static constructors may not have constructor initializers");
		return t;
	}
	override public void struct_declaration(struct_declaration ast, SymbolTable bindings) {
		StructType t = new StructType(ast.id, bindings);
		t.Add(ast.id, bindings, msg);
		if (bindings.Owner is ClassType)
			t.enclosingType = (ClassType)bindings.Owner;
		CheckIndexers(ast.attrs, ast.body);
		attribute_sections(ast.attrs, bindings);
		AddModifiers(t, ast.mods, "new public protected internal private",
			 bindings.Owner is ClassType ? "private" : "internal");
		t.Modifiers.Add("sealed");
		foreach (declaration x in ast.body) {
			declaration(x, t.members);
			if (contains(x.mods, "protected") || contains(x.mods, "internal"))
				msg.Error(x.begin, "struct members cannot be declared 'protected' or 'internal'"); 
		}
		ast.sym = t;
	}
	public virtual void switch_section(switch_section ast, SymbolTable bindings) {
		foreach (statement x in ast.stmts)
			statement(x, bindings);
	}
	override public void switch_statement(switch_statement ast, SymbolTable bindings) {
		foreach (switch_section x in ast.sections)
			switch_section(x, bindings);
	}
	override public void throw_statement(throw_statement ast, SymbolTable bindings) {
		if (ast.expr == null) {
			for (AST s = ast; s != null; s = s.parent)
				if (s is catch_clauses)
					return;
			msg.Error(ast.begin, "invalid 'throw' statement: 'throw' may appear in only catch clauses");
			}
	}
	override public void try_statement(try_statement ast, SymbolTable bindings) {
		statement(ast.block, bindings);
		if (ast.catches != null)
			catch_clauses(ast.catches, bindings);
		if (ast.finally_block != null)
			statement(ast.finally_block.block, bindings);
	}
	override public void unary_declarator(unary_declarator ast, SymbolTable bindings) {
		ClassType c = (ClassType)bindings.Owner;
		Method m = c.AddMethod(new InputElement(unaryOpName(ast.op), ast.begin), msg);
		ast.sym = m.AddFormal(ast.id1, msg);
		ast.method = m;
	}
	override public void unchecked_statement(unchecked_statement ast, SymbolTable bindings) {
		statement(ast.stmt, bindings);
	}
	public virtual void using_directive(using_directive ast, SymbolTable bindings, SymbolList usingdirectives) {
		if (ast is alias_directive)
			return;
		namespace_directive n = (namespace_directive)ast;
		NameSpace t = (NameSpace)bindings.Owner;
		n.sym = (NameSpace)dotted_name(n.name, bindings);
		if (n.sym == null)
			msg.Error(n.name.begin, "'{0}' is not a namespace", n.name.ToString());
		else if (usingdirectives.Contains(n.sym))
			msg.Warning(n.name.right, "namespace{0} already contains a using directive for '{1}'",
				t.declSpace == null ? "" : (" '" + t.FullName) + "'", n.name.ToString());
		else
			usingdirectives.Add(n.sym);
	}
	override public void unsafe_statement(unsafe_statement ast, SymbolTable bindings) {
		msg.Warning(ast.begin, "unsafe statement not yet supported");
		statement(ast.block, bindings);
	}
	override public void using_statement(using_statement ast, SymbolTable bindings) {
		Debug.Assert(bindings.Owner is Block);
		Block b = resource(ast.r, bindings);
		statement(ast.body, b.locals);
		ast.sym = b;
	}
	override public void while_statement(while_statement ast, SymbolTable bindings) {
		statement(ast.body, bindings);
	}
}

public class Pass2: bind {
	public Pass2(MessageWriter msg) : base(msg) {}

	override public void arglist_parameter(arglist_parameter ast, SymbolTable bindings) {
		Formal f= (Formal)bindings[ast.arglist.str];
		f.Type = Type.RuntimeArgumentHandle;
	}
	override public void binary_declarator(binary_declarator ast, SymbolTable bindings) {
		ClassType c = ((Method)bindings.Owner).GetType();
		type(ast.ty, bindings);
		ast.sym1.Type = type(ast.t1, bindings);
		ast.sym2.Type = type(ast.t2, bindings);
		if (ast.sym1.Type != c && ast.sym2.Type != c)
			msg.Error(ast.op, "one parameter of binary operator '{0}' must be a '{1}'",
				ast.op.str, c.FullName);
		if ((ast.op.str == "<<" || ast.op.str == ">>") && ast.sym2.Type != Type.Int)
			msg.Error(ast.op, "second parameter of binary operator '{0}' must be a '{1}'",
				ast.op.str, Type.Int.FullName);
		string[] pairs = new string[] { "<", ">", "==", "!=", "<=", ">=" };
		int i = Array.IndexOf(pairs, ast.op.str);
		if (i >= 0 && c.members[binaryOpName(pairs[(i&~1)+(i+1)%2])] == null)
			msg.Error(ast.op, "'{0}.operator {1}({2},{3}) requires that matching operator '{4}' be defined",
				c.FullName, ast.op.str, ast.sym1.Type.FullName, ast.sym2.Type.FullName, pairs[(i&~1)+(i+1)%2]);
	}
	override public void class_declaration(class_declaration ast, SymbolTable bindings) {
		ClassType t = ast.sym;
		int i = 0;
		if (ast.bases.Count > 0) {
			Type b = type(ast.bases[0], bindings);
			if (b.IsClass) {
				t.baseClass = (ClassType)b;
				i = 1;
			}
		}
		for ( ; i < ast.bases.Count; i++) {
			Type b = type(ast.bases[i], bindings);
			if (b is InterfaceType)
				if (t.interfaces.Contains((InterfaceType)b))
					msg.Error(ast.bases[i].begin, "duplicate interface '{0}'", b.Name);
				else
					t.interfaces.Add((InterfaceType)b);
			else
				msg.Error(ast.bases[i].begin, "'{0}' is not an interface type", b.Name);
		}
		if (t.baseClass == null)
			t.baseClass = Type.Object;
		if (t == t.baseClass)
			t.baseClass = null;
		foreach (declaration x in ast.body)
			declaration(x, t.members);
	}
	public virtual void compilation(compilation ast, SymbolTable bindings) {
		base.compilation(ast);
		foreach (compilation_unit x in ast.inputs)
			compilation_unit(x, bindings);
	}
	public virtual void compilation_unit(compilation_unit ast, SymbolTable bindings) {
		using_directives(ast.using_directives, bindings);
		foreach (declaration x in ast.declarations)
				declaration(x, bindings);
		NameSpace t = (NameSpace)bindings.Owner;
		foreach (string id in t.aliases)
			t.members.Remove(id);
		t.usingdirectives = null;
	}
	override public void constant_declaration(constant_declaration ast, SymbolTable bindings) {
		Type t = type(ast.ty, bindings);
		foreach (const_declarator x in ast.decls)
			x.sym.Type = t;
	}
	override public void constructor_declaration(constructor_declaration ast, SymbolTable bindings) {
		formals(ast.decl.f, ast.sym.locals);
		ast.sym.Type = Type.Void;
	}
	override public void delegate_declaration(delegate_declaration ast, SymbolTable bindings) {
		ast.sym.Type = type(ast.ty, bindings);
		ast.sym.invoke.Type = ast.sym.Type;
		formals(ast.f, ast.sym.invoke.locals);
	}
	override public void destructor_declaration(destructor_declaration ast, SymbolTable bindings) {
		ast.sym.Type = Type.Void;
	}
	override public Symbol dotted_name(dotted_name ast, SymbolTable bindings) {
		Type context = bindings.Owner as Type;	// may be NameSpace
		if (bindings.Owner is Block)
			context = ((Block)bindings.Owner).GetType();
		Symbol t;
		if (ast.left == null) {
			t = bindings.Owner.LookupType(ast.right, msg);
			if (t == null)
				msg.Error(ast.right, "undefined namespace or type '{0}'", ast.right.str);
			else if (!t.IsAccessible(context))
				msg.Error(ast.right, "'{0}' is inaccessible", ast.right.str);
			ast.sym = t;
			return t;
		}
		t = dotted_name(ast.left, bindings);
		if (t is INamespaceOrType)
			t = ((INamespaceOrType)t)[ast.right.str];
		ast.sym = t;
		if (t == null)
			msg.Error(ast.right, "invalid namespace or type '{0}'", ast.ToString());
		else if (!t.IsAccessible(context))
			msg.Error(ast.right, "'{0}' is inaccessible", ast.right.str);
		return t;
	}
	override public void enum_declaration(enum_declaration ast, SymbolTable bindings) {
		if (ast.ty != null)
			ast.sym.baseType = type(ast.ty, bindings);
		else
			ast.sym.baseType = Type.Int;
		foreach (enum_member_declaration x in ast.body)
			x.sym.Type = ast.sym;
	}
	override public void event_declaration1(event_declaration1 ast, SymbolTable bindings) {
		type(ast.ty, bindings);
	}
	override public void event_declaration2(event_declaration2 ast, SymbolTable bindings) {
		type(ast.ty, bindings);
		member_name(ast.name, bindings);
	}
	override public void explicit_declarator(explicit_declarator ast, SymbolTable bindings) {
		ClassType c = ((Method)bindings.Owner).GetType();
		Type ty = type(ast.ty, bindings);
		ast.sym.Type = type(ast.t1, bindings);
		if (ty == ast.sym.Type)
			msg.Error(ast.begin, "'implicit operator {0}({1})' must have different parameter and return types",
				ty.FullName, ast.sym.Type.FullName);
		if (ty != c && ast.sym.Type != c)
			msg.Error(ast.begin, "'implicit operator {0}({1})' must have '{2}' as the parameter or return type",
				ty.FullName, ast.sym.Type.FullName, c.FullName);
		if (ty is InterfaceType || ty == Type.Object || ast.sym.Type is InterfaceType || ast.sym.Type == Type.Object)
			msg.Error(ast.ty.begin, "'implicit operator {0}({1})' cannot have object or interface types as the parameter or return type",
				ty.FullName, ast.sym.Type.FullName);
		if (ty.InheritsFrom(ast.sym.Type) || ast.sym.Type.InheritsFrom(ty))
			msg.Error(ast.ty.begin, "'implicit operator {0}({1})' cannot must have distinct parameter and return types",
				ty.FullName, ast.sym.Type.FullName);
	}
	override public void field_declaration(field_declaration ast, SymbolTable bindings) {
		Type t = type(ast.ty, bindings);
		foreach (field_declarator x in ast.decls)
			x.sym.Type = t;
	}
	override public void fixed_parameter(fixed_parameter ast, SymbolTable bindings) {
		Formal f = (Formal)bindings[ast.id.str];
		f.Type = type(ast.ty, bindings);
	}
	public virtual void formals(formals ast, SymbolTable bindings) {
		foreach (parameter x in ast.fixeds)
			parameter(x, bindings);
		if (ast.param != null)
			parameter(ast.param, bindings);
	}
	override public void implicit_declarator(implicit_declarator ast, SymbolTable bindings) {
		ClassType c = ((Method)bindings.Owner).GetType();
		Type ty = type(ast.ty, bindings);
		ast.sym.Type = type(ast.t1, bindings);
		if (ty == ast.sym.Type)
			msg.Error(ast.begin, "'implicit operator {0}({1})' must have different parameter and return types",
				ty.FullName, ast.sym.Type.FullName);
		if (ty != c && ast.sym.Type != c)
			msg.Error(ast.begin, "'implicit operator {0}({1})' must have '{2}' as the parameter or return type",
				ty.FullName, ast.sym.Type.FullName, c.FullName);
		if (ty is InterfaceType || ty == Type.Object || ast.sym.Type is InterfaceType || ast.sym.Type == Type.Object)
			msg.Error(ast.ty.begin, "'implicit operator {0}({1})' cannot have object or interface types as the parameter or return type",
				ty.FullName, ast.sym.Type.FullName);
		if (ty.InheritsFrom(ast.sym.Type) || ast.sym.Type.InheritsFrom(ty))
			msg.Error(ast.ty.begin, "'implicit operator {0}({1})' cannot must have distinct parameter and return types",
				ty.FullName, ast.sym.Type.FullName);
	}
	override public void indexer_declaration(indexer_declaration ast, SymbolTable bindings) {
		Type t;
		if (ast.i.interfacename != null) {
			t = type(ast.i.interfacename, bindings) as InterfaceType;
			if (!(t is InterfaceType))
				msg.Error("'{0}' is not an interface name",
					ast.i.interfacename.name.ToString());
		}
		t = type(ast.i.ty, bindings);
		foreach (accessor_declaration x in ast.accessors) {
			formals(ast.i.f, x.sym.locals);
			if (x.id.str == "set") {
				((Formal)x.sym.locals["value"]).Type = t;
				x.sym.Type = Type.Void;
			} else
				x.sym.Type = t;
		}
	}
	override public void interface_declaration(interface_declaration ast, SymbolTable bindings) {
		InterfaceType t = ast.sym;
		foreach (type x in ast.interfaces) {
			Type b = type(x, bindings);
			if (!(b is InterfaceType))
				msg.Error(ast.id, "'{0}' is not an interface type", b.Name);
			else if (t.interfaces.Contains((InterfaceType)b))
				msg.Error(ast.id, "duplicate interface base '{0}'", b.Name);
			else
				t.interfaces.Add((InterfaceType)b);
		}
		foreach (declaration x in ast.body)
			declaration(x, t.members);
	}
	override public void interface_event_declaration(interface_event_declaration ast, SymbolTable bindings) {
		ast.sym.Type = type(ast.ty, bindings);
		if (!(ast.ty.sym is DelegateType))
			msg.Error(ast.ty.begin, "delegate type expected; found '{0}'", ast.ty.sym.FullName);
	}
	override public void interface_indexer_declaration(interface_indexer_declaration ast, SymbolTable bindings) {
		Type t = type(ast.ty, bindings);
		foreach (accessor_declaration x in ast.accessors) {
			formals(ast.f, x.sym.locals);
			if (x.id.str == "set"){
				((Formal)x.sym.locals["value"]).Type = t;
				x.sym.Type = Type.Void;
			} else
				x.sym.Type = t;
		}
	}
	override public void interface_method_declaration(interface_method_declaration ast, SymbolTable bindings) {
		ast.sym.Type = type(ast.ty, bindings);
		formals(ast.f, ast.sym.locals);
	}
	override public void interface_property_declaration(interface_property_declaration ast, SymbolTable bindings) {
		ast.sym.Type = type(ast.ty, bindings);
	}
	InterfaceType member_name(member_name ast, SymbolTable bindings) {
		if (ast.ty != null) {
			Type t = type(ast.ty, bindings);
			if (t is InterfaceType) {
				ast.sym = (InterfaceType)t;
				return ast.sym;
			} else
				msg.Error(ast.id, "'{0}' is not an interface name", ast.id.str);
		}
		return null;
	}
	override public void method_declaration(method_declaration ast, SymbolTable bindings) {
		ast.sym.Type = type(ast.ty, bindings);
		member_name(ast.name, bindings);
		formals(ast.parms, ast.sym.locals);
	}
	public virtual void named_argument(named_argument ast, SymbolTable bindings) {
	}
	public virtual void namespace_body(namespace_body ast, SymbolTable bindings) {
		using_directives(ast.ud, bindings);
		foreach (declaration x in ast.declarations)
			declaration(x, bindings);
	}
	override public void namespace_declaration(namespace_declaration ast, SymbolTable bindings) {
		namespace_body(ast.nb, ast.sym.members);
		foreach (string id in ast.sym.aliases)
			ast.sym.members.Remove(id);
		ast.sym.usingdirectives = null;
	}
	override public void operator_declaration(operator_declaration ast, SymbolTable bindings) {
		operator_declarator(ast.op, ast.sym.locals);
		ast.sym.Type = ast.op.ty.sym;
	}
	override public void params_parameter(params_parameter ast, SymbolTable bindings) {
		Type t = type(ast.ty, bindings);
		Formal f = (Formal)bindings[ast.id.str];
		f.Type = type(ast.ty, bindings);;
		if (!(f.Type is ArrayType)) {
			msg.Error(ast.ty.begin, "params parameter must be an array type");
			f.IsParams = false;
		}
	}
	override public void property_declaration(property_declaration ast, SymbolTable bindings) {
		ast.sym.Type = type(ast.ty, bindings);
		member_name(ast.name, bindings);
	}
	public virtual void simple_name(simple_name ast, SymbolTable bindings) {
		ast.sym = bindings.Owner.Lookup(ast.id, msg);
		if (ast.sym == null)
			msg.Error(ast.id, "undefined symbol '{0}'", ast.id.str);
	}
	override public void struct_declaration(struct_declaration ast, SymbolTable bindings) {
		StructType t = ast.sym;
		t.baseClass = Type.ValueType;
		foreach (type x in ast.interfaces) {
			Type b = type(x, bindings);
			if (b is InterfaceType)
				if (t.interfaces.Contains((InterfaceType)b))
					msg.Error(x.begin, "duplicate interface '{0}'", b.Name);
				else
					t.interfaces.Add((InterfaceType)b);
			else
				msg.Error(x.begin, "'{0}' is not an interface type", b.Name);
		}
		foreach (declaration x in ast.body)
			declaration(x, t.members);
	}
	override public Type type(type ast, SymbolTable bindings) {
		ast.sym = base.type(ast, bindings);
		return ast.sym;
	}
	override public void unary_declarator(unary_declarator ast, SymbolTable bindings) {
		ClassType c = ((Method)bindings.Owner).GetType();
		Type ty = type(ast.ty, bindings);
		ast.sym.Type = type(ast.t1, bindings);
		if (ast.sym.Type != c)
			msg.Error(ast.t1.begin, "parameter of unary operator '{0}' must be a '{1}'",
				ast.op.str, c.FullName);
		if ((ast.op.str == "++" || ast.op.str == "--") && ty != c)
			msg.Error(ast.ty.begin, "return type of unary operator '{0}' must be a '{1}'",
				ast.op.str, c.FullName);
		else if ((ast.op.str == "true" || ast.op.str == "false") && ty != Type.Bool)
			msg.Error(ast.t1.begin, "parameter of unary operator '{0}' must be a '{1}'",
				ast.op.str, Type.Bool.FullName);
		if (ast.op.str == "true" && c.members["op_False"] == null)
			msg.Error(ast.ty.begin, "'{0}.operator true({1})' requires that matching operator 'false' be defined",
				c.FullName, ast.sym.Type.FullName);
		if (ast.op.str == "false" && c.members["op_True" ] == null)
			msg.Error(ast.ty.begin, "'{0}.operator false({1})' requires that matching operator 'true' be defined",
				c.FullName, ast.sym.Type.FullName);
	}
	public virtual void using_directives(using_directiveList ud, SymbolTable bindings) {
		NameSpace t = (NameSpace)bindings.Owner;
		t.usingdirectives = new SymbolList();
		foreach (using_directive x in ud)
			if (x is alias_directive) {
				alias_directive d = (alias_directive)x;
				d.sym = dotted_name(d.name, bindings);
			} else if (x is namespace_directive)
				t.usingdirectives.Add(dotted_name(((namespace_directive)x).name, bindings));
			else
				throw new ArgumentException();
		foreach (using_directive x in ud)
			if (x is alias_directive) {
				alias_directive d = (alias_directive)x;
				if (t.aliases.Contains(d.id.str))
					msg.Error(d.id, "'{0}' is already an alias in this namespace", d.id.str);
				else if (d.sym != null) {
					t.aliases.Add(d.id.str);
					d.sym.Add(d.id, t.members, msg);
				}
			}
	}
}

public class Pass3: bind {
	public stringList assemblyRefs = new stringList();
	public Pass3(MessageWriter msg) : base(msg) {}

	public virtual void accessor_declaration(accessor_declaration ast, SymbolTable bindings) {
		foreach (attribute_section x in ast.attrs)
			attribute_section(x, bindings);
		if (ast.body != null)
			statement(ast.body, bindings);
	}
	override public void arglist_parameter(arglist_parameter ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
	}
	public virtual void argument(argument ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void array_creation_expression1(array_creation_expression1 ast, SymbolTable bindings) {
		foreach (expression x in ast.exprs)
			expression(x, bindings);
		if (ast.init != null)
			array_initializer(ast.init, bindings);
		type(ast.ty, bindings);
	}
	public virtual void array_creation_expression2(array_creation_expression2 ast, SymbolTable bindings) {
		array_initializer(ast.init, bindings);
		type(ast.ty, bindings);
	}
	public virtual void array_initializer(array_initializer ast, SymbolTable bindings) {
		foreach (variable_initializer x in ast.a) {
			if (ast.a[0] is array_initializer
			&& (!(x is array_initializer) || ((array_initializer)x).a.Count != ((array_initializer)ast.a[0]).a.Count))
				msg.Error(x.begin, "incorrectly structured array initializer"); 
			variable_initializer(x, bindings);
		}
	}
	public virtual void as_expression(as_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		type(ast.ty, bindings);
	}
	public virtual void assignment_expression(assignment_expression ast, SymbolTable bindings) {
		expression(ast.e1, bindings);
		expression(ast.e2, bindings);
	}
	public virtual void attribute(attribute ast, SymbolTable bindings) {
		if (ast.name is name_type) {
			ast.sym = dotted_name(((name_type)ast.name).name, bindings, "Attribute") as ClassType;
			ast.name.sym = ast.sym;
		}
		type(ast.name, bindings);
		if (ast.arguments != null)
			attribute_arguments(ast.arguments, bindings, ast.sym);
	}
	public virtual void attribute_arguments(attribute_arguments ast, SymbolTable bindings, ClassType c) {
		foreach (argument x in ast.args)
			argument(x, bindings);
		foreach (named_argument x in ast.namedargs)
			named_argument(x, bindings, c);
	}
	public virtual void attribute_section(attribute_section ast, SymbolTable bindings) {
		foreach (attribute x in ast.attributes)
			attribute(x, bindings);
	}
	public virtual void attribute_sections(attribute_sectionList attrs, SymbolTable bindings) {
		foreach (attribute_section x in attrs)
			attribute_section(x, bindings);
	}
	public virtual void base_access(base_access ast, SymbolTable bindings) {
		Block b = (Block)bindings.Owner;
		if (b.GetMethod().IsStatic)
			msg.Error(ast.begin, "'base' can appear only in instance methods");
		ast.sym = b.GetType().baseClass;
	}
	public virtual void base_initializer(base_initializer ast, SymbolTable bindings) {
		foreach (argument x in ast.args)
			argument(x, bindings);
	}
	override public void binary_declarator(binary_declarator ast, SymbolTable bindings) {
		type(ast.t1, bindings);
		type(ast.t2, bindings);
		type(ast.ty, bindings);
	}
	public virtual void binary_expression(binary_expression ast, SymbolTable bindings) {
		expression(ast.e1, bindings);
		expression(ast.e2, bindings);
	}
	override public void block_statement(block_statement ast, SymbolTable bindings) {
		foreach (statement x in ast.stmts)
			statement(x, ast.sym.locals);
	}
	public virtual void cast_expression(cast_expression ast, SymbolTable bindings) {
		ast.sym = type(ast.ty, bindings);
		expression(ast.expr, bindings);
	}
	public virtual void catch_clause(catch_clause ast, SymbolTable bindings) {
		Type t = type(ast.ty, bindings);
		if (ast.id != null)
			ast.sym.Type = t;
		statement(ast.block, bindings);
	}
	public virtual void catch_clauses(catch_clauses ast, SymbolTable bindings) {
		foreach (catch_clause x in ast.specifics)
			catch_clause(x, bindings);
		if (ast.general != null)
			statement(ast.general, bindings);
	}
	public virtual void checked_expression(checked_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	override public void checked_statement(checked_statement ast, SymbolTable bindings) {
		statement(ast.stmt, bindings);
	}
	override public void class_declaration(class_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (type b in ast.bases)
			type(b, bindings);
		type(ast.sym.baseClass);
		foreach (declaration x in ast.body)
			declaration(x, ast.sym.members);
		if (!ast.sym.Is("abstract"))
			foreach (Symbol s in ast.sym.Flatten())
				if (s.Is("abstract") && s.declSpace.Owner != ast.sym)
					msg.Error(s.id, "'{0}' does not implement inherited abstract member '{1}'",
						ast.sym.FullName, s.FullName);
		interface_mapping(ast.sym, ast);
	}
	public virtual void compilation(compilation ast, SymbolTable bindings) {
		base.compilation(ast);
		ast.assemblyRefs = assemblyRefs;
		foreach (compilation_unit x in ast.inputs)
			compilation_unit(x, bindings);
	}
	public virtual void compilation_unit(compilation_unit ast, SymbolTable bindings) {
		attribute_sections(ast.attributes, bindings);
		using_directives(ast.using_directives, bindings);
		foreach (declaration x in ast.declarations)
			declaration(x, bindings);
		((NameSpace)bindings.Owner).usingdirectives = null;
	}
	public virtual void compound_assignment_expression(compound_assignment_expression ast, SymbolTable bindings) {
		expression(ast.e1, bindings);
		expression(ast.e2, bindings);
	}
	public virtual void cond_expression(cond_expression ast, SymbolTable bindings) {
		expression(ast.cond, bindings);
		expression(ast.success, bindings);
		expression(ast.failure, bindings);
	}
	public virtual void const_declarator(const_declarator ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	override public void const_statement(const_statement ast, SymbolTable bindings) {
		Type t = type(ast.ty, bindings);
		foreach (const_declarator x in ast.consts) {
			expression(x.expr, bindings);
			x.sym.Type = t;
		}
	}
	override public void constant_declaration(constant_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (const_declarator x in ast.decls)
			expression(x.expr, bindings);
	}
	override public void constructor_declaration(constructor_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		constructor_declarator(ast.decl, ast.sym.locals);
		if (ast.block != null)
			statement(ast.block, ast.sym.locals);
	}
	public virtual void constructor_declarator(constructor_declarator ast, SymbolTable bindings) {
		if (ast.init != null)
			constructor_initializer(ast.init, bindings);
	}
	public virtual void constructor_initializer(constructor_initializer ast, SymbolTable bindings) {
		     if (ast is base_initializer) base_initializer((base_initializer)ast, bindings);
		else if (ast is this_initializer) this_initializer((this_initializer)ast, bindings);
		else throw new ArgumentException();
	}
	override public void delegate_declaration(delegate_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		formals(ast.f, ast.sym.invoke.locals);
		type(ast.sym.baseClass);
	}
	override public void destructor_declaration(destructor_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		if (ast.block != null)
			statement(ast.block, ast.sym.locals);
	}
	override public void do_statement(do_statement ast, SymbolTable bindings) {
		statement(ast.body, bindings);
		expression(ast.expr, bindings);
	}
	override public Symbol dotted_name(dotted_name ast, SymbolTable bindings) {
		return dotted_name(ast, bindings, null);
	}
	public Symbol dotted_name(dotted_name ast, SymbolTable bindings, string suffix) {
		Type context = bindings.Owner as Type;	// may be NameSpace
		if (bindings.Owner is Block)
			context = ((Block)bindings.Owner).GetType();
		Symbol t;
		if (ast.left == null) {
			t = bindings.Owner.LookupType(ast.right, msg);
			if (suffix != null && !ast.right.str.EndsWith(suffix)) {
				Symbol t1 = bindings.Owner.LookupType(new InputElement(ast.right.str + suffix), msg);
				if (t == null)
					t = t1;
				else if (t1 != null)
					msg.Error(ast.right, "'{0}' is ambiguous; use '{0}{1}'",
						ast.right.str, suffix);
			}
			if (t == null)
				msg.Error(ast.right, "undefined namespace or type '{0}'", ast.right.str);
			else if (!t.IsAccessible(context))
				msg.Error(ast.right, "'{0}' is inaccessible", ast.right.str);
			ast.sym = t;
			return t;
		}
		t = dotted_name(ast.left, bindings);
		if (t is INamespaceOrType)
			t = ((INamespaceOrType)t)[ast.right.str];
		ast.sym = t;
		if (t == null)
			msg.Error(ast.right, "invalid namespace or type '{0}'", ast.ToString());
		else if (!t.IsAccessible(context))
			msg.Error(ast.right, "'{0}' is inaccessible", ast.right.str);
		return t;
	}
	public virtual void element_access(element_access ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		foreach (argument x in ast.exprs)
			argument(x, bindings);
	}
	override public void enum_declaration(enum_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (enum_member_declaration x in ast.body)
			enum_member_declaration(x, ast.sym.members);
		if (ast.ty != null)
			type(ast.ty, bindings);
	}
	public virtual void enum_member_declaration(enum_member_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		if (ast.expr != null)
			expression(ast.expr, bindings);
	}
	public virtual void event_accessor(event_accessor ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		statement(ast.block, ast.sym.locals);
	}
	override public void event_declaration1(event_declaration1 ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		Type t = type(ast.ty, bindings);
		if (!(t is DelegateType))
			msg.Error(ast.ty.begin, "delegate type expected; found '{0}'", t.FullName);
		foreach (event_declarator x in ast.decls) {
			x.sym.Type = t;
			if (x.init != null)
				variable_initializer(x.init, bindings);
		}
	}
	override public void event_declaration2(event_declaration2 ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		Type t = type(ast.ty, bindings);
		if (!(t is DelegateType))
			msg.Error(ast.ty.begin, "delegate type expected; found '{0}'", t.FullName);
		ast.sym.Type = t;
		foreach (event_accessor x in ast.accessors)
			event_accessor(x, bindings);
	}
	override public void explicit_declarator(explicit_declarator ast, SymbolTable bindings) {
		type(ast.t1, bindings);
		type(ast.ty, bindings);
	}
	public virtual void expr_access(expr_access ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void expr_initializer(expr_initializer ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void expression(expression ast, SymbolTable bindings) {
		     if (ast is simple_name) simple_name((simple_name)ast, bindings);
		else if (ast is literal) return;
		else if (ast is member_access) member_access((member_access)ast, bindings);
		else if (ast is invocation_expression) invocation_expression((invocation_expression)ast, bindings);
		else if (ast is element_access) element_access((element_access)ast, bindings);
		else if (ast is this_access) this_access((this_access)ast, bindings);
		else if (ast is base_access) base_access((base_access)ast, bindings);
		else if (ast is post_expression) post_expression((post_expression)ast, bindings);
		else if (ast is new_expression) new_expression((new_expression)ast, bindings);
		else if (ast is array_creation_expression1) array_creation_expression1((array_creation_expression1)ast, bindings);
		else if (ast is array_creation_expression2) array_creation_expression2((array_creation_expression2)ast, bindings);
		else if (ast is typeof_expression) typeof_expression((typeof_expression)ast, bindings);
		else if (ast is checked_expression) checked_expression((checked_expression)ast, bindings);
		else if (ast is unchecked_expression) unchecked_expression((unchecked_expression)ast, bindings);
		else if (ast is unary_expression) unary_expression((unary_expression)ast, bindings);
		else if (ast is pre_expression) pre_expression((pre_expression)ast, bindings);
		else if (ast is cast_expression) cast_expression((cast_expression)ast, bindings);
		else if (ast is binary_expression) binary_expression((binary_expression)ast, bindings);
		else if (ast is is_expression) is_expression((is_expression)ast, bindings);
		else if (ast is as_expression) as_expression((as_expression)ast, bindings);
		else if (ast is cond_expression) cond_expression((cond_expression)ast, bindings);
		else if (ast is assignment_expression) assignment_expression((assignment_expression)ast, bindings);
		else if (ast is compound_assignment_expression) compound_assignment_expression((compound_assignment_expression)ast, bindings);
		else if (ast is sizeof_expression) sizeof_expression((sizeof_expression)ast, bindings);
		else throw new ArgumentException();
	}
	override public void expression_statement(expression_statement ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	override public void field_declaration(field_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (field_declarator x in ast.decls)
			if (x.init != null)
				variable_initializer(x.init, bindings);
		type(ast.ty, bindings);
	}
	public static finally_clause find_finally(statement ast) {
		for (AST s = ast; s != null; s = s.parent)
			if (s is finally_clause)
				return (finally_clause)s;
		return null;		
	}
	public statement find_switch(statement ast, string kind) {
		for (AST s = ast; s != null; s = s.parent)
			if (s is finally_clause) {
				msg.Error(ast.begin, "invalid '{0}' statement: '{0}' cannot exit a finally block", kind);
				return null;
			} else if (s is switch_statement)
				return (statement)s;
		msg.Error(ast.begin, "invalid '{0}' statement", kind);
		return null;
	}
	override public void fixed_parameter(fixed_parameter ast, SymbolTable bindings) {
		type(ast.ty, bindings);
		attribute_sections(ast.attrs, bindings);
	}
	override public void fixed_statement(fixed_statement ast, SymbolTable bindings) {
		foreach (fixed_declarator x in ast.declarators)
			expression(x.expr, bindings);
		statement(ast.body, bindings);
	}
	public virtual void for_init(for_init ast, SymbolTable bindings) {
		if (ast is for_decl)
			local_statement(((for_decl)ast).decl, bindings);
		else if (ast is for_list)
			foreach (expression x in ((for_list)ast).exprs)
				expression(x, bindings);
		else
			throw new ArgumentException();
	}
	override public void for_statement(for_statement ast, SymbolTable bindings) {
		if (ast.init != null)
			for_init(ast.init, ast.sym.locals);
		if (ast.cond != null)
			expression(ast.cond, ast.sym.locals);
		foreach (expression x in ast.iterators)
			expression(x, ast.sym.locals);
		statement(ast.body, ast.sym.locals);
	}
	public virtual void formals(formals ast, SymbolTable bindings) {
		foreach (parameter x in ast.fixeds)
			parameter(x, bindings);
		if (ast.param != null)
			parameter(ast.param, bindings);
	}
	override public void foreach_statement(foreach_statement ast, SymbolTable bindings) {
		Local t = ast.sym;
		ast.sym.Type =  type(ast.ty, t.declSpace);
		expression(ast.expr, t.declSpace);
		statement(ast.body, t.declSpace);
	}
	override public void goto_case_statement(goto_case_statement ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		ast.stmt = find_switch(ast, "goto case");
	}
	override public void goto_default_statement(goto_default_statement ast, SymbolTable bindings) {
		ast.stmt = find_switch(ast, "goto default");
	}
	override public void goto_statement(goto_statement ast, SymbolTable bindings) {
		ast.sym = ((Block)bindings.Owner).LookupLabel(ast.id);
		if (ast.sym == null)
			msg.Error(ast.id, "undefined label '{0}'", ast.id.str);
		else {
			ast.target = ast.sym.definition;
			if (find_finally(ast) != find_finally(ast.target))
				msg.Error(ast.begin, "invalid 'goto' statement: 'goto' cannot exit a finally block");
		}
	}
	override public void if_statement(if_statement ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		statement(ast.thenpart, bindings);
		if (ast.elsepart != null)
			statement(ast.elsepart, bindings);
	}
	override public void implicit_declarator(implicit_declarator ast, SymbolTable bindings) {
		type(ast.t1, bindings);
		type(ast.ty, bindings);
	}
	override public void indexer_declaration(indexer_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		if (ast.i.interfacename != null)
			type(ast.i.interfacename, bindings);
		type(ast.i.ty, bindings);
		foreach (accessor_declaration x in ast.accessors) {
			attribute_sections(x.attrs, bindings);
			formals(ast.i.f, x.sym.locals);
			if (x.body != null)
				statement(x.body, x.sym.locals);
		}
	}
	override public void interface_declaration(interface_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (declaration x in ast.body)
			declaration(x, ast.sym.members);
		foreach (type x in ast.interfaces)
			type(x, bindings);
	}
	override public void interface_event_declaration(interface_event_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		type(ast.ty, bindings);
	}
	override public void interface_indexer_declaration(interface_indexer_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (accessor_declaration x in ast.accessors)
			attribute_sections(x.attrs, bindings);
		formals(ast.f, bindings);
		type(ast.ty, bindings);
	}
	override public void interface_method_declaration(interface_method_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		formals(ast.f, bindings);
		type(ast.ty, bindings);
	}
	public virtual void interface_mapping(ClassType c, declaration ast) {
		foreach (InterfaceType x in c.interfaces)
			foreach (Symbol s in x) {
				Symbol t = null;
				for (ClassType b = c; b != null; b = b.baseClass) {
					t = b.members[s.FullName];
					if (t == null)
						t = b.members[s.Name];
					if (t is MethodSuite && s is Method) {
						t = ((MethodSuite)t).Contains(((Method)s).signature);
						if (t is Method && t.Type.Equals(((Method)s).Type))
							break;
					} else if (t is Property && s is Property || t is Event && s is Event)
						break;
				}
				if (t == null || (!s.Equals(t) || !t.IsPublic) && t.Name != s.FullName)
					msg.Error(ast.end, "'{0}' does not implement interface member '{1}'",
						c.FullName, s.FullName);
				else if (t is Method) {
					if (!t.Modifiers.Contains("virtual")) {
						t.Modifiers.Add("virtual");
						t.Modifiers.Add("sealed");
					}
					((Method)t).interfaceMethod = (Method)s;
				}
		}
	}
	override public void interface_property_declaration(interface_property_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (accessor_declaration x in ast.accessors)
			accessor_declaration(x, bindings);
		type(ast.ty, bindings);
	}
	public virtual void invocation_expression(invocation_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		foreach (argument x in ast.args)
			argument(x, bindings);
	}
	public virtual void is_expression(is_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		type(ast.ty, bindings);
	}
	override public void labeled_statement(labeled_statement ast, SymbolTable bindings) {
		statement(ast.stmt, bindings);
	}
	override public void local_statement(local_statement ast, SymbolTable bindings) {
		Block b = (Block)bindings.Owner;
		Type t = type(ast.ty, bindings);
		foreach (var_declarator x in ast.vars) {
			x.sym = b.AddLocal(x.id, msg);
			x.sym.Type = t;
			if (x.init != null)
				variable_initializer(x.init, bindings);
		}
	}
	override public void lock_statement(lock_statement ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		statement(ast.body, bindings);
	}
	public virtual void member_access(member_access ast, SymbolTable bindings) {
		     if (ast is expr_access) expr_access((expr_access)ast, bindings);
		else if (ast is pointer_access) pointer_access((pointer_access)ast, bindings);
		else if (ast is predefined_access) predefined_access((predefined_access)ast, bindings);
		else throw new ArgumentException();
	}
	override public void method_declaration(method_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		type(ast.ty, bindings);
		Method m = ast.sym;
		formals(ast.parms, m.locals);
		ClassType c = m.GetType();
		MethodSuite t = c.members[m.id.str] as MethodSuite;
		if (t != null && t.Contains(m.signature) != m)
			msg.Error(ast.name.begin, "{0} '{1}' already contains a definition for '{2}'",
				bindings.Owner.Kind, bindings.Owner.FullName, m.Name);
		if (m.Is("override") && m.GetBaseDefinition() == m)
			msg.Error(ast.name.begin, "invalid use of 'override'; '{0}' is not virtual",
				m.FullName);
		else if (!m.Is("new") && !m.Is("override")) {
			while ((c = c.baseClass) != null) {
				t = c.members[m.id.str] as MethodSuite;
				if (t != null && t.Contains(m.signature) != null)
					msg.Warning(ast.name.begin, "'{0}' hides '{1}'; use 'new'",
						m.FullName, t.Contains(m.signature).FullName);
			}
		}
		if (ast.body != null)
			statement(ast.body, m.locals);
	}
	public virtual void named_argument(named_argument ast, SymbolTable bindings, ClassType c) {
		ast.sym = c.Lookup(ast.id, msg);
		if (!(ast.sym is Field || ast.sym is Property))
			msg.Error(ast.id, "Type '{0}' does not contain a member named '{1}'",
				c.FullName, ast.id.str);
		expression(ast.expr, bindings);
	}
	public virtual void namespace_body(namespace_body ast, SymbolTable bindings) {
		using_directives(ast.ud, bindings);
		foreach (declaration x in ast.declarations)
			declaration(x, bindings);
	}
	override public void namespace_declaration(namespace_declaration ast, SymbolTable bindings) {
		namespace_body(ast.nb, ast.sym.members);
		foreach (string id in ast.sym.aliases)
			ast.sym.members.Remove(id);
		ast.sym.usingdirectives = null;
	}
	public virtual void new_expression(new_expression ast, SymbolTable bindings) {
		foreach (argument x in ast.args)
			argument(x, bindings);
		type(ast.ty, bindings);
	}
	override public void operator_declaration(operator_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		if (ast.block != null)
			statement(ast.block, ast.sym.locals);
		operator_declarator(ast.op, bindings);
	}
	override public void params_parameter(params_parameter ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		type(ast.ty, bindings);
	}
	public virtual void pointer_access(pointer_access ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void post_expression(post_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void pre_expression(pre_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void predefined_access(predefined_access ast, SymbolTable bindings) {
		switch (ast.predefined.str) {
		case "bool":   ast.type = Type.Bool;   break;
		case "byte":   ast.type = Type.Byte;   break;
		case "char":   ast.type = Type.Char;   break;
		case "decimal":ast.type = Type.Decimal;break;
		case "double": ast.type = Type.Double; break;
		case "float":  ast.type = Type.Float;  break;
		case "int":    ast.type = Type.Int;    break;
		case "long":   ast.type = Type.Long;   break;
		case "object": ast.type = Type.Object; break;
		case "sbyte":  ast.type = Type.SByte;  break;
		case "short":  ast.type = Type.Short;  break;
		case "string": ast.type = Type.String; break;
		case "uint":   ast.type = Type.UInt;   break;
		case "ulong":  ast.type = Type.ULong;  break;
		case "ushort": ast.type = Type.UShort; break;
		default: throw new ArgumentException();
		}
	}
	override public void property_declaration(property_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (accessor_declaration x in ast.decls) {
			attribute_sections(x.attrs, bindings);
			if (x.body != null)
				statement(x.body, x.sym.locals);
		}
	}
	public virtual void resource(resource ast, SymbolTable bindings) {
		     if (ast is resource_expr) expression(((resource_expr)ast).expr, bindings);
		else if (ast is resource_decl) local_statement(((resource_decl)ast).local, bindings);
		else throw new ArgumentException();
	}
	override public void return_statement(return_statement ast, SymbolTable bindings) {
		if (ast.method.Type == Type.Void && ast.expr != null)
			msg.Error(ast.expr.begin, "extraneous return expression");
		if (ast.expr != null)
			expression(ast.expr, bindings);
	}
	public virtual void simple_name(simple_name ast, SymbolTable bindings) {
		ast.sym = bindings.Owner.Lookup(ast.id, msg);
		if (ast.sym == null)
			msg.Error(ast.id, "undefined symbol '{0}'", ast.id.str);
	}
	public virtual void sizeof_expression(sizeof_expression ast, SymbolTable bindings) {
		type(ast.ty, bindings);
	}
	public virtual void stackalloc_initializer(stackalloc_initializer ast, SymbolTable bindings) {
		type(ast.ty, bindings);
		expression(ast.expr, bindings);
	}
	override public void struct_declaration(struct_declaration ast, SymbolTable bindings) {
		attribute_sections(ast.attrs, bindings);
		foreach (type x in ast.interfaces)
			type(x, bindings);
		type(ast.sym.baseClass);
		foreach (declaration x in ast.body)
			declaration(x, ast.sym.members);
		interface_mapping(ast.sym, ast);
	}
	public virtual void switch_expression(switch_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void switch_label(switch_label ast, SymbolTable bindings, ref bool hasdefault) {
		     if (ast is switch_expression) switch_expression((switch_expression)ast, bindings);
		else if (ast is switch_default) {
			if (hasdefault)
				msg.Error(ast.begin, "duplicate default label");
			hasdefault = true;
		} else throw new ArgumentException();
	}
	public virtual void switch_section(switch_section ast, SymbolTable bindings, ref bool hasdefault) {
		foreach (switch_label x in ast.labels)
			switch_label(x, bindings, ref hasdefault);
		statement s = null;
		foreach (statement x in ast.stmts)
			statement(s = x, bindings);
		if (!(s is return_statement || s is break_statement
		|| s is continue_statement  || s is goto_statement
		|| s is goto_case_statement || s is goto_default_statement
		|| s is throw_statement))
			msg.Error(s.begin, "missing break or other control flow statement in switch case");
	}
	override public void switch_statement(switch_statement ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		bool hasdefault = false;
		foreach (switch_section x in ast.sections)
			switch_section(x, bindings, ref hasdefault);
	}
	public virtual void this_access(this_access ast, SymbolTable bindings) {
		Block b = (Block)bindings.Owner;
		if (b.GetMethod().IsStatic)
			msg.Error(ast.begin, "'this' can appear only in instance methods");
		ast.sym = b.GetType();
	}
	public virtual void this_initializer(this_initializer ast, SymbolTable bindings) {
		foreach (argument x in ast.args)
			argument(x, bindings);
	}
	override public void throw_statement(throw_statement ast, SymbolTable bindings) {
		if (ast.expr != null)
			expression(ast.expr, bindings);
	}
	override public void try_statement(try_statement ast, SymbolTable bindings) {
		statement(ast.block, bindings);
		if (ast.catches != null)
			catch_clauses(ast.catches, bindings);
		if (ast.finally_block != null)
			statement(ast.finally_block.block, bindings);
	}
	public Type type(Type ty) {
		if (ty != null && ty.module != null && !assemblyRefs.Contains(ty.module))
			assemblyRefs.Add(ty.module);
		return ty;
	}
	override public Type type(type ast, SymbolTable bindings) {
		if (ast.sym == null)
			ast.sym = base.type(ast, bindings);
		return type(ast.sym);
	}
	public virtual void typeof_expression(typeof_expression ast, SymbolTable bindings) {
		type(ast.ty, bindings);
	}
	override public void unary_declarator(unary_declarator ast, SymbolTable bindings) {
		type(ast.t1, bindings);
		type(ast.ty, bindings);
	}
	public virtual void unary_expression(unary_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	public virtual void unchecked_expression(unchecked_expression ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
	}
	override public void unchecked_statement(unchecked_statement ast, SymbolTable bindings) {
		statement(ast.stmt, bindings);
	}
	public virtual void using_directives(using_directiveList ud, SymbolTable bindings) {
		NameSpace t = (NameSpace)bindings.Owner;
		t.usingdirectives = new SymbolList();
		foreach (using_directive x in ud)
			if (x is alias_directive) {
				alias_directive d = (alias_directive)x;
				d.sym = dotted_name(d.name, bindings);
			} else if (x is namespace_directive)
				t.usingdirectives.Add(dotted_name(((namespace_directive)x).name, bindings));
			else
				throw new ArgumentException();
		foreach (using_directive x in ud)
			if (x is alias_directive) {
				alias_directive d = (alias_directive)x;
				if (d.sym != null)
					d.sym.Add(d.id, t.members, msg);
			}
	}
	override public void unsafe_statement(unsafe_statement ast, SymbolTable bindings) {
		statement(ast.block, bindings);
	}
	override public void using_statement(using_statement ast, SymbolTable bindings) {
		resource(ast.r, ast.sym.locals);
		statement(ast.body, ast.sym.locals);
	}
	public virtual void var_declarator(var_declarator ast, SymbolTable bindings) {
		if (ast.init != null)
			variable_initializer(ast.init, bindings);
	}
	public virtual void variable_initializer(variable_initializer ast, SymbolTable bindings) {
		     if (ast is stackalloc_initializer) stackalloc_initializer((stackalloc_initializer)ast, bindings);
		else if (ast is expr_initializer) expr_initializer((expr_initializer)ast, bindings);
		else if (ast is array_initializer) array_initializer((array_initializer)ast, bindings);
		else throw new ArgumentException();
	}
	override public void while_statement(while_statement ast, SymbolTable bindings) {
		expression(ast.expr, bindings);
		statement(ast.body, bindings);
	}
}
