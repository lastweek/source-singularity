using System;
using System.IO;
using System.Collections;
using System.Reflection;
using System.Reflection.Emit;

public class emit {
	public MessageWriter msg;
	protected TextWriter w;
	public BuiltinTypes T;
	protected Hashtable map;
	public ModuleBuilder module;
	public emit(TextWriter w, MessageWriter msg, Hashtable map, ModuleBuilder module) {
		this.w = w;
		this.msg = msg;
		this.map = map;
		this.module = module;
	}
	static void init(BuiltinTypes T, Hashtable map) {
		map.Add(T.Bool, System.Type.GetType("System.Boolean"));
		map.Add(T.Byte, System.Type.GetType("System.Byte"));
		map.Add(T.Char, System.Type.GetType("System.Char"));
		map.Add(T.Decimal, System.Type.GetType("System.Decimal"));
		map.Add(T.Double, System.Type.GetType("System.Double"));
		map.Add(T.Float, System.Type.GetType("System.Single"));
		map.Add(T.Int, System.Type.GetType("System.Int32"));
		map.Add(T.Long, System.Type.GetType("System.Int64"));
		map.Add(T.Object, System.Type.GetType("System.Object"));
		map.Add(T.SByte, System.Type.GetType("System.SByte"));
		map.Add(T.Short, System.Type.GetType("System.Int16"));
		map.Add(T.String, System.Type.GetType("System.String"));
		map.Add(T.UInt, System.Type.GetType("System.UInt32"));
		map.Add(T.ULong, System.Type.GetType("System.UInt64"));
		map.Add(T.UShort, System.Type.GetType("System.UInt16"));
		map.Add(T.Void, System.Type.GetType("System.Void"));
	}
	public static object visit(object ast, TextWriter w, string[] args, MessageWriter msg) {
		if (msg.Count == 0) {
			Hashtable map = new Hashtable();
			init(((compilation)ast).global.Types, map);
			emit1 pass1 = new emit1(w, msg, map);
			AssemblyBuilder asm = pass1.compilation((compilation)ast);
			(new emit2(w, msg, map, pass1.module)).compilation((compilation)ast);
			(new emit3(w, msg, map, pass1.module)).compilation((compilation)ast);
			return asm;
		}
		return ast;
	}

	public FieldAttributes GetFieldAttributes(stringList modifiers) {
		FieldAttributes attr = 0;
		foreach (string mod in modifiers)
			switch (mod) {
			case "private": attr |= FieldAttributes.Private; break;
			case "public": attr |= FieldAttributes.Public; break;
			case "protected":
				if (modifiers.Contains("internal"))
					attr |= FieldAttributes.FamORAssem;
				else
					attr |= FieldAttributes.Family;
				break;
			case "internal":
				if (modifiers.Contains("protected"))
					attr |= FieldAttributes.FamORAssem;
				else
					attr |= FieldAttributes.Assembly;
				break;
			case "static": attr |= FieldAttributes.Static; break;
			}
		return attr;
	}
	public MethodAttributes GetMethodAttributes(stringList modifiers) {
		MethodAttributes attr = 0;
		foreach (string mod in modifiers)
			switch (mod) {
			case "private": attr |= MethodAttributes.Private; break;
			case "public": attr |= MethodAttributes.Public; break;
			case "protected":
				if (modifiers.Contains("internal"))
					attr |= MethodAttributes.FamORAssem;
				else
					attr |= MethodAttributes.Family;
				break;
			case "internal":
				if (modifiers.Contains("protected"))
					attr |= MethodAttributes.FamORAssem;
				else
					attr |= MethodAttributes.Assembly;
				break;
			case "static": attr |= MethodAttributes.Static; break;
			case "override":
			case "virtual": attr |= MethodAttributes.Virtual; break;
			case "new": attr |= MethodAttributes.NewSlot; break;
			case "abstract": attr |= MethodAttributes.Abstract; break;
			case "sealed": attr |= MethodAttributes.Final; break;
				
			}
		return attr;
	}
	public TypeAttributes GetTypeAttributes(Type t) {
		TypeAttributes attr = 0;
		foreach (string mod in t.Modifiers)
			switch (mod) {
			case "private":
				attr |= t.IsNested ? TypeAttributes.NestedPrivate : TypeAttributes.NotPublic; break;
			case "public":
				attr |= t.IsNested ? TypeAttributes.NestedPublic : TypeAttributes.Public; break;
			case "protected":
				if (t.IsNested)
					attr |= t.Modifiers.Contains("internal") ? TypeAttributes.NestedFamORAssem : TypeAttributes.NestedFamily;
				break;
			case "internal":
				if (t.IsNested)
					attr |= t.Modifiers.Contains("protected") ? TypeAttributes.NestedFamORAssem : TypeAttributes.NestedAssembly;
				break;
			case "sealed": attr |= TypeAttributes.Sealed; break;
			case "abstract": attr |= TypeAttributes.Abstract; break;
			}
		return attr;
	}
	static System.Type GetTypeFromAssembly(Type ty, string assembly) {
		Assembly asm = Assembly.LoadFrom(assembly);	// may throw
		System.Type type = asm.GetType(ty.RealName);
		Debug.Assert(type != null);
		return type;
	}
	public FieldInfo this[Field f] {
		get {
			FieldInfo info = (FieldInfo)map[f];
			if (info == null) {
				Type ty = f.GetType();
				System.Type type = this[ty];
				BindingFlags flags = 0;
				flags |= f.IsStatic ? BindingFlags.Static : BindingFlags.Instance;
				flags |= f.IsPublic ? BindingFlags.Public : BindingFlags.NonPublic;
				info = type.GetField(f.Name, flags);
				if (info != null)
					map.Add(f, info);
			}
			Debug.Assert(info != null);
			return info;
		}
	}
	public ConstructorInfo this[Constructor m] {
		get {
			ConstructorInfo info = (ConstructorInfo)map[m];
			if (info == null) {
				Type ty = m.GetType();
				System.Type type = this[ty];
				BindingFlags flags = m.IsPublic ? BindingFlags.Public : BindingFlags.NonPublic;
				System.Type[] args = new System.Type[m.ArgCount];
				for (int i = 0; i < m.ArgCount; i++)
					args[i] = this[m[i].Type];
				info = type.GetConstructor(flags|BindingFlags.Instance, null, args, null);
				if (info != null)
					map.Add(m, info);
			}
			Debug.Assert(info != null);
			return info;
		}
	}
	public MethodInfo this[Method m] {
		get {
			MethodInfo info = (MethodInfo)map[m];
			if (info == null) {
				Type ty = m.GetType();
				System.Type type = this[ty];
				BindingFlags flags = 0;
				flags |= m.IsStatic ? BindingFlags.Static : BindingFlags.Instance;
				flags |= m.IsPublic ? BindingFlags.Public : BindingFlags.NonPublic;
				System.Type[] args = new System.Type[m.ArgCount];
				for (int i = 0; i < m.ArgCount; i++)
					args[i] = this[m[i].Type];
				info = type.GetMethod(m.Name, flags, null, args, null);
				if (info != null)
					map.Add(m, info);
			}
			Debug.Assert(info != null);
			return info;
		}
	}
	public System.Type this[PointerType ty] {
		get {
			System.Type type, etype = this[ty.elementType];
			if (ty.elementType.module != null)
				type = GetTypeFromAssembly(ty, ty.elementType.module);
			else
				type = module.GetType(etype.FullName + "&");
			Debug.Assert(type != null);
			return type;
		}
	}
	public System.Type this[ArrayType ty] {
		get {
			System.Type type, etype = this[ty.elementType];
			if (ty.elementType.module != null)
				type = GetTypeFromAssembly(ty, ty.elementType.module);
			else
				type = module.GetType(string.Format("{0}[{1}]", etype.FullName, "".PadRight(ty.rank - 1, ',')));
			Debug.Assert(type != null);
			return type;
		}
	}
	public System.Type this[Type ty] {
		get {
			if (ty is ArrayType)
				return this[(ArrayType)ty];
			else if (ty is PointerType)
				return this[(PointerType)ty];
			System.Type type = (System.Type)map[ty];
			if (type != null)
				return type;
			if (ty.module != null)
				return GetTypeFromAssembly(ty, ty.module);
			type = System.Type.GetType(ty.RealName);
			if (type == null)
				type = module.GetType(ty.RealName);
			if (type != null)
				map.Add(ty, type);
			if (type == null)
				System.Console.WriteLine(ty.RealName);
			Debug.Assert(type != null);
			return type;
		}
	}
	public virtual System.Type type(type ast) {
		return this[ast.sym];
	}
}

public class emit1: emit {
	public emit1(TextWriter w, MessageWriter msg, Hashtable map) : base(w, msg, map, null) {}

	public virtual void class_declaration(class_declaration ast, ModuleBuilder m) {
		if (ast.parent is type_declaration) {
			TypeBuilder t = ((type_declaration)ast.parent).builder;
			ast.type = t.DefineNestedType(ast.sym.FullName, GetTypeAttributes(ast.sym)|TypeAttributes.Class);
		} else
			ast.type = m.DefineType(ast.sym.FullName, GetTypeAttributes(ast.sym)|TypeAttributes.Class);
		map.Add(ast.sym, ast.type);
		foreach (declaration x in ast.body)
			declaration(x, m);
	}
	public virtual AssemblyBuilder compilation(compilation ast) {
		T = ast.global.Types;
		AssemblyName name = new AssemblyName();
		if (ast.inputs.Count > 0 && ast.inputs[0].begin.file != null
		&& ast.inputs[0].begin.file != "<stream>")
			name.Name = Path.GetFileNameWithoutExtension(ast.inputs[0].begin.file);
		else
			name.Name = Guid.NewGuid().ToString();
		AssemblyBuilder asm = AppDomain.CurrentDomain.DefineDynamicAssembly(name, AssemblyBuilderAccess.RunAndSave);
		string oname = name.Name;
		foreach (string s in ast.args)
			if (s[0] == '/' || s[0] == '-') {
				string arg = s.Substring(1); 
				if (arg.StartsWith("out:"))
					oname = arg.Substring(4);
			}
		foreach (compilation_unit x in ast.inputs)
			compilation_unit(x, asm, oname);
		return asm;
	}
	public virtual void compilation_unit(compilation_unit ast, AssemblyBuilder asm, string name) {
		module = asm.DefineDynamicModule(asm.GetName().Name, name, true);
		foreach (declaration x in ast.declarations)
			declaration(x, module);
	}
	public virtual void declaration(declaration ast, ModuleBuilder m) {
		     if (ast is class_declaration) class_declaration((class_declaration)ast, m);
		else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast, m);
		else if (ast is enum_declaration) enum_declaration((enum_declaration)ast, m);
		else if (ast is interface_declaration) interface_declaration((interface_declaration)ast, m);
		else if (ast is namespace_declaration) namespace_declaration((namespace_declaration)ast, m);
		else if (ast is struct_declaration) struct_declaration((struct_declaration)ast, m);
	}
	public virtual void delegate_declaration(delegate_declaration ast, ModuleBuilder m) {
		if (ast.parent is type_declaration) {
			TypeBuilder t = ((type_declaration)ast.parent).builder;
			ast.type = t.DefineNestedType(ast.sym.FullName, GetTypeAttributes(ast.sym));
		} else
			ast.type = m.DefineType(ast.sym.FullName, GetTypeAttributes(ast.sym));
		map.Add(ast.sym, ast.type);
	}
	public virtual void enum_declaration(enum_declaration ast, ModuleBuilder m) {
		ast.type = m.DefineEnum(ast.sym.FullName, GetTypeAttributes(ast.sym), System.Type.GetType("System.Int32"));
		map.Add(ast.sym, ast.type);
	}
	public virtual void interface_declaration(interface_declaration ast, ModuleBuilder m) {
		if (ast.parent is type_declaration) {
			TypeBuilder t = ((type_declaration)ast.parent).builder;
			ast.type = t.DefineNestedType(ast.sym.FullName,
				GetTypeAttributes(ast.sym)|TypeAttributes.Interface|TypeAttributes.Abstract);
		} else
			ast.type = m.DefineType(ast.sym.FullName,
				GetTypeAttributes(ast.sym)|TypeAttributes.Interface|TypeAttributes.Abstract);
		map.Add(ast.sym, ast.type);
		foreach (declaration x in ast.body)
			declaration(x, m);
	}
	public virtual void namespace_body(namespace_body ast, ModuleBuilder m) {
		foreach (declaration x in ast.declarations)
			declaration(x, m);
	}
	public virtual void namespace_declaration(namespace_declaration ast, ModuleBuilder m) {
		namespace_body(ast.nb, m);
	}
	public virtual void struct_declaration(struct_declaration ast, ModuleBuilder m) {
		if (ast.parent is type_declaration) {
			TypeBuilder t = ((type_declaration)ast.parent).builder;
			ast.type = t.DefineNestedType(ast.sym.FullName, GetTypeAttributes(ast.sym));
		} else
			ast.type = m.DefineType(ast.sym.FullName, GetTypeAttributes(ast.sym));
		map.Add(ast.sym, ast.type);
		foreach (declaration x in ast.body)
			declaration(x, m);
	}
}

public class emit2: emit {
	public emit2(TextWriter w, MessageWriter msg, Hashtable map, ModuleBuilder mod) : base(w, msg, map, mod) {}

	public virtual void binary_declarator(binary_declarator ast, TypeBuilder t) {
	}
	public virtual void class_declaration(class_declaration ast) {
		TypeBuilder t = ast.builder;
		t.SetParent(this[ast.sym.baseClass]);
		foreach (Type x in ast.sym.interfaces)
			t.AddInterfaceImplementation(this[x]);
		foreach (declaration x in ast.body)
			declaration(x, t);
	}
	public virtual void compilation(compilation ast) {
		T = ast.global.Types;
		foreach (compilation_unit x in ast.inputs)
			compilation_unit(x);
	}
	public virtual void compilation_unit(compilation_unit ast) {
		foreach (declaration x in ast.declarations)
			declaration(x);
	}
	public virtual void constant_declaration(constant_declaration ast, TypeBuilder t) {
		foreach (const_declarator x in ast.decls) {
			FieldBuilder f = t.DefineField(x.sym.Name, type(ast.ty), GetFieldAttributes(x.sym.Modifiers));
			f.SetConstant(x.sym.value);
			map.Add(x.sym, f);
			x.builder = f;
		}
	}
	public virtual void constructor_declaration(constructor_declaration ast, TypeBuilder t) {
		System.Type[] args = new System.Type[ast.sym.ArgCount];
		for (int i = 0; i < ast.sym.ArgCount; i++)
			args[i]= this[ast.sym[i].Type];
		ConstructorBuilder m = t.DefineConstructor(GetMethodAttributes(ast.sym.Modifiers), CallingConventions.Standard, args);
		for (int i = 0; i < ast.sym.ArgCount; i++) {
			Formal f = ast.sym[i];
			m.DefineParameter(i + 1, f.modifier != null && f.modifier.str == "out" ? ParameterAttributes.Out : 0, f.Name);
			f.ordinal = ast.sym.IsInstance ? i + 1 : i;
		}
		map.Add(ast.sym, m);
		ast.builder = m;
	}
	public virtual void declaration(declaration ast, TypeBuilder t) {
		     if (ast is class_declaration) class_declaration((class_declaration)ast);
		else if (ast is constant_declaration) constant_declaration((constant_declaration)ast, t);
		else if (ast is constructor_declaration) constructor_declaration((constructor_declaration)ast, t);
		else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast);
		else if (ast is destructor_declaration) destructor_declaration((destructor_declaration)ast, t);
		else if (ast is enum_declaration) enum_declaration((enum_declaration)ast);
		else if (ast is event_declaration1) event_declaration1((event_declaration1)ast, t);
		else if (ast is event_declaration2) event_declaration2((event_declaration2)ast, t);
		else if (ast is field_declaration) field_declaration((field_declaration)ast, t);
		else if (ast is indexer_declaration) indexer_declaration((indexer_declaration)ast, t);
		else if (ast is interface_declaration) interface_declaration((interface_declaration)ast);
		else if (ast is interface_event_declaration) interface_event_declaration((interface_event_declaration)ast, t);
		else if (ast is interface_indexer_declaration) interface_indexer_declaration((interface_indexer_declaration)ast, t);
		else if (ast is interface_method_declaration) interface_method_declaration((interface_method_declaration)ast, t);
		else if (ast is interface_property_declaration) interface_property_declaration((interface_property_declaration)ast, t);
		else if (ast is method_declaration) method_declaration((method_declaration)ast, t);
		else if (ast is operator_declaration) operator_declaration((operator_declaration)ast, t);
		else if (ast is property_declaration) property_declaration((property_declaration)ast, t);
		else if (ast is struct_declaration) struct_declaration((struct_declaration)ast);
		else throw new ArgumentException();
	}
	public virtual void declaration(declaration ast) {
		     if (ast is class_declaration) class_declaration((class_declaration)ast);
		else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast);
		else if (ast is enum_declaration) enum_declaration((enum_declaration)ast);
		else if (ast is interface_declaration) interface_declaration((interface_declaration)ast);
		else if (ast is namespace_declaration) namespace_declaration((namespace_declaration)ast);
		else if (ast is struct_declaration) struct_declaration((struct_declaration)ast);
		else throw new ArgumentException();
	}
	public virtual MethodBuilder DefineMethod(TypeBuilder t, Method m) {
		return DefineMethod(t, m, GetMethodAttributes(m.Modifiers));
	}
	public virtual MethodBuilder DefineMethod(TypeBuilder t, Method m, MethodAttributes attr) {
		System.Type[] args;
		if (m.Name == "set_Item") {
			args = new System.Type[m.ArgCount + 1];
			args[m.ArgCount] = this[((Formal)m.locals["value"]).Type];
		} else
			args = new System.Type[m.ArgCount];
		int i;
		for (i = 0; i < m.ArgCount; i++) {
			Formal f = m[i];
			if (f.modifier != null)
				args[i] = this[new ManagedPointerType(f.Type)];
			else
				args[i] = this[f.Type];
		}
		MethodBuilder mb = t.DefineMethod(m.Name, attr, this[m.Type], args);
		for (i = 0; i < m.ArgCount; i++) {
			Formal f = m[i];
			mb.DefineParameter(i + 1, f.modifier != null && f.modifier.str == "out" ? ParameterAttributes.Out : 0, f.Name);
			f.ordinal = m.IsInstance ? i + 1 : i;
		}
		if (m.Name == "set_Item") {
			Formal f = (Formal)m.locals["value"];
			f.ordinal = m.IsInstance ? i + 1 : i;	
			mb.DefineParameter(f.ordinal, 0, f.Name);
		}
		if (m.interfaceMethod != null)
			t.DefineMethodOverride(mb, this[m.interfaceMethod]);
		return mb;
	}
	public virtual void delegate_declaration(delegate_declaration ast) {
		TypeBuilder t = ast.builder;
		t.SetParent(this[ast.sym.baseClass]);
		foreach (Symbol s in ast.sym)
			if (s is Constructor) {
				Constructor m = (Constructor)s;
				System.Type[] args = new System.Type[m.ArgCount];
				for (int i = 0; i < m.ArgCount; i++)
					args[i]= this[m[i].Type];
				ConstructorBuilder mb = t.DefineConstructor(GetMethodAttributes(m.Modifiers), CallingConventions.Standard, args);
				for (int i = 0; i < m.ArgCount; i++) {
					Formal f = m[i];
					mb.DefineParameter(i + 1, 0, f.Name);
					f.ordinal = m.IsInstance ? i + 1 : i;
				}
				map.Add(m, mb);
			} else if (s is Method) {
				MethodBuilder mb = DefineMethod(t, (Method)s, GetMethodAttributes(s.Modifiers));
				map.Add(s, mb);
			}
	}
	public virtual void destructor_declaration(destructor_declaration ast, TypeBuilder t) {
		ast.builder = t.DefineMethod(ast.sym.Name,
			MethodAttributes.Private|MethodAttributes.Final|MethodAttributes.SpecialName,
			this[T.Void], new System.Type[0]);
	}
	public virtual void enum_declaration(enum_declaration ast) {
		EnumBuilder t = (EnumBuilder)ast.type;
		foreach (enum_member_declaration x in ast.body)
			x.builder = t.DefineLiteral(x.sym.Name, x.sym.value);
		if (ast.sym.enclosingType == null)
			map[ast.sym] = t.CreateType();
	}
	public virtual void event_declaration1(event_declaration1 ast, TypeBuilder t) {
		foreach (event_declarator x in ast.decls) {
			x.builder = t.DefineField(x.sym.Name, type(ast.ty), GetFieldAttributes(x.sym.Modifiers));
			map.Add(x.sym, x.builder);
			x.event_builder = t.DefineEvent(x.sym.Name, EventAttributes.None, type(ast.ty));
			x.add_builder = DefineMethod(t, x.sym.Add);
			map.Add(x.sym.Add, x.add_builder);
			x.remove_builder = DefineMethod(t, x.sym.Remove);
			map.Add(x.sym.Remove, x.remove_builder);
		}
	}
	public virtual void event_declaration2(event_declaration2 ast, TypeBuilder t) {
		EventBuilder e = t.DefineEvent(ast.sym.Name, EventAttributes.None, type(ast.ty));
		foreach (event_accessor x in ast.accessors) {
			x.builder = DefineMethod(t, x.sym);
			map.Add(x.sym, x.builder);
		}
		ast.builder = e;
	}
	public virtual void explicit_declarator(explicit_declarator ast, TypeBuilder t) {
	}
	public virtual void field_declaration(field_declaration ast, TypeBuilder t) {
		foreach (field_declarator x in ast.decls) {
			FieldBuilder f = t.DefineField(x.sym.Name, type(ast.ty), GetFieldAttributes(x.sym.Modifiers));
			map.Add(x.sym, f);
			x.builder = f;
		}
	}
	public virtual System.Type[] formals(formals ast) {
		System.Type[] args = new System.Type[ast.fixeds.Count + (ast.param != null ? 1 : 0)];
		int i = 0;
		foreach (fixed_parameter p in ast.fixeds)
			args[i++] = type(p.ty);
		if (ast.param != null)
			args[i] = type(((params_parameter)ast.param).ty);	// fix
		return args;
	}
	public virtual void implicit_declarator(implicit_declarator ast, TypeBuilder t) {
	}
	public virtual void indexer_declaration(indexer_declaration ast, TypeBuilder t) {
		PropertyBuilder p = t.DefineProperty("Item", PropertyAttributes.None, type(ast.i.ty), formals(ast.i.f));
		foreach (accessor_declaration x in ast.accessors) {
			x.builder = DefineMethod(t, x.sym);
			map.Add(x.sym, x.builder);
		}
		ast.builder = p;
	}
	public virtual void interface_declaration(interface_declaration ast) {
		TypeBuilder t = ast.builder;
		if (ast.sym.baseClass != null)
			t.SetParent(this[ast.sym.baseClass]);
		foreach (Type x in ast.sym.interfaces)
			t.AddInterfaceImplementation(this[x]);
		foreach (declaration x in ast.body)
			declaration(x, t);
	}
	public virtual void interface_event_declaration(interface_event_declaration ast, TypeBuilder t) {
		ast.builder = t.DefineEvent(ast.sym.Name, EventAttributes.None, type(ast.ty));
		map[ast.sym.Add] = DefineMethod(t, ast.sym.Add);
		map[ast.sym.Remove] = DefineMethod(t, ast.sym.Remove);
	}
	public virtual void interface_indexer_declaration(interface_indexer_declaration ast, TypeBuilder t) {
		PropertyBuilder p = t.DefineProperty("Item", PropertyAttributes.None, type(ast.ty), formals(ast.f));
		foreach (accessor_declaration x in ast.accessors) {
			x.builder = DefineMethod(t, x.sym);
			map.Add(x.sym, x.builder);
		}
		ast.builder = p;
	}
	public virtual void interface_method_declaration(interface_method_declaration ast, TypeBuilder t) {
		ast.builder = DefineMethod(t, ast.sym);
		map.Add(ast.sym, ast.builder);
	}
	public virtual void interface_property_declaration(interface_property_declaration ast, TypeBuilder t) {
		PropertyBuilder p = t.DefineProperty(ast.sym.Name, PropertyAttributes.None, type(ast.ty), new System.Type[0]);
		foreach (accessor_declaration x in ast.accessors) {
			x.builder = DefineMethod(t, x.sym);
			map.Add(x.sym, x.builder);
		}
	}
	public virtual void method_declaration(method_declaration ast, TypeBuilder t) {
		ast.builder = DefineMethod(t, ast.sym);
		map.Add(ast.sym, ast.builder);
	}
	public virtual void namespace_declaration(namespace_declaration ast) {
		foreach (declaration x in ast.nb.declarations)
			declaration(x);
	}
	public virtual void operator_declaration(operator_declaration ast, TypeBuilder t) {
	}
	public virtual void operator_declarator(operator_declarator ast, TypeBuilder t) {
		     if (ast is binary_declarator) binary_declarator((binary_declarator)ast, t);
		else if (ast is explicit_declarator) explicit_declarator((explicit_declarator)ast, t);
		else if (ast is implicit_declarator) implicit_declarator((implicit_declarator)ast, t);
		else if (ast is unary_declarator) unary_declarator((unary_declarator)ast, t);
		else throw new ArgumentException();
	}
	public virtual void property_declaration(property_declaration ast, TypeBuilder t) {
		PropertyBuilder p = t.DefineProperty(ast.sym.Name, PropertyAttributes.None, type(ast.ty), new System.Type[0]);
		foreach (accessor_declaration x in ast.decls) {
			x.builder = DefineMethod(t, x.sym);
			map.Add(x.sym, x.builder);
		}
		ast.builder = p;
	}
	public virtual void struct_declaration(struct_declaration ast) {
		TypeBuilder t = ast.builder;
		t.SetParent(this[ast.sym.baseClass]);
		foreach (Type x in ast.sym.interfaces)
			t.AddInterfaceImplementation(this[x]);
		foreach (declaration x in ast.body)
			declaration(x, t);
	}
	public virtual void unary_declarator(unary_declarator ast, TypeBuilder t) {
	}
}

public class emit3: emit {
	public emit3(TextWriter w, MessageWriter msg, Hashtable map, ModuleBuilder mod) : base(w, msg, map, mod) {}

	public class ILState: gen {
		ILGenerator ILgen;
		emit map;
		ArrayList labels = new ArrayList();
		ArrayList locals = new ArrayList();
		public ILState(ILGenerator ILgen, emit map) : base(map.T, map.msg) {
			this.ILgen = ILgen;
			this.map = map;
			labels.Add(null);
			locals.Add(null);
		}
		System.Type[] arrayMethodArgs(int rank, params System.Type[] prefix) {
			System.Type[] args = new System.Type[rank+prefix.Length];
			Array.Copy(prefix, args, prefix.Length);
			for (int i = 0; i < rank; i++)
				args[i+prefix.Length] = typeof (int);
			return args;
		}
		override public object BeginTry() {
			return ILgen.BeginExceptionBlock();
		}
		override public object BeginFinally(object handle) {
			ILgen.BeginFinallyBlock();
			return handle;
		}
		override public void block_statement(block_statement ast) {
			ILgen.BeginScope();
			foreach (statement x in ast.stmts)
				statement(x);
			ILgen.EndScope();
		}
		override public void catch_clause(Type ty, Local sym, statement block, object handle) {
			ILgen.BeginCatchBlock(map[ty]);
			base.catch_clause(ty, sym, block, handle);
		}
		override public void defLabel(int lab) {
			ILgen.MarkLabel(getLabel(lab));
		}
		void Emit(OpCode op, ConstructorInfo x) { ILgen.Emit(op, x); }
		void Emit(OpCode op, LocalBuilder x) { ILgen.Emit(op, x); }
		void Emit(OpCode op, MethodInfo x) { ILgen.Emit(op, x); }
		void Emit(OpCode op, System.Reflection.Emit.Label x) { ILgen.Emit(op, x); }
		void Emit(OpCode op, System.Type x) { ILgen.Emit(op, x); }
		override public void Emit(OpCode op) { ILgen.Emit(op); }
		override public void Emit(OpCode op, double x) { ILgen.Emit(op, x); }
		override public void Emit(OpCode op, float x) { ILgen.Emit(op, x); }
		override public void Emit(OpCode op, Constructor x) { Emit(op, map[x]); }
		override public void Emit(OpCode op, Field x) { ILgen.Emit(op, map[x]); }
		override public void Emit(OpCode op, int x) { ILgen.Emit(op, x); }
		override public void Emit(OpCode op, Formal x) { ILgen.Emit(op, (short)x.ordinal); }				
		override public void Emit(OpCode op, Local x) { ILgen.Emit(op, getLocal(x.ordinal)); }
		override public void Emit(OpCode op, Method x) { Emit(op, map[x]); }
		override public void Emit(OpCode op, string x) { ILgen.Emit(op, x); }
		override public void Emit(OpCode op, Type x) { Emit(op, map[x]); }
		override public void EmitCreateArray(ArrayType ty, Type ety, int rank) {
			ILgen.Emit(OpCodes.Newobj, GetArrayMethodToken(ty, ".ctor", null));
		}
		override public void EmitLoad(int index) {
			Emit(OpCodes.Ldloc, getLocal(index));
		}
		override public void EmitLoadAddress(int index) {
			Emit(OpCodes.Ldloca, getLocal(index));
		}
		override public void EmitLoadElement(ArrayType ty, Type ety, int rank) {
			Emit(OpCodes.Call, GetArrayMethodToken(ty, "Get", map[ety]));
		}
		override public void EmitLoadElementAddress(ArrayType ty, Type ety, int rank) {
			System.Type rettype = map[new ManagedPointerType(ety)];
			ILgen.Emit(OpCodes.Call, GetArrayMethodToken(ty, "Address", rettype));
		}
		override public void EmitStore(int index) {
			Emit(OpCodes.Stloc, getLocal(index));
		}
		override public void EmitStoreElement(ArrayType ty, Type ety, int rank) {
			ILgen.Emit(OpCodes.Call, GetArrayMethodToken(ty, "Set", null, arrayMethodArgs(rank, map[ety])));
		}
		override public void EmitSwitch(int[] caselabels) {
			System.Reflection.Emit.Label[] labels = new System.Reflection.Emit.Label[caselabels.Length];
			for (int i = 0; i < labels.Length; i++)
				labels[i] = getLabel(caselabels[i]);
			ILgen.Emit(OpCodes.Switch, labels);
		}
		override public void EndTry(object handle) {
			ILgen.EndExceptionBlock();
		}
		override public int genLabel(int n) {
			for (int i = 0; i < n; i++)
				labels.Add(ILgen.DefineLabel());
			return base.genLabel(n);
		}
		int GetArrayMethodToken(ArrayType ty, string name, System.Type rettype) {
			return GetArrayMethodToken(ty, name, rettype, arrayMethodArgs(ty.rank));
		}
		int GetArrayMethodToken(ArrayType ty, string name, System.Type rettype, System.Type[] args) {
			System.Type t = map[ty];
			MethodToken m = map.module.GetArrayMethodToken(t, name,
				CallingConventions.Standard|CallingConventions.HasThis, rettype, args);
			return m.Token;
		}
		System.Reflection.Emit.Label getLabel(int lab) {
			Debug.Assert(labels[lab] != null);
			return (System.Reflection.Emit.Label)labels[lab];
		}
		LocalBuilder getLocal(int var) {
			return (LocalBuilder)locals[var];
		}
		override public void gotoLabel(OpCode inst, int lab) {
			Emit(inst, getLabel(lab));
		}
		override public int newLocal(Type ty) {
			locals.Add(ILgen.DeclareLocal(map[ty]));
			return locals.Count - 1;
		}
		override public int newLocal(Local v) {
			int var = base.newLocal(v);
			getLocal(var).SetLocalSymInfo(v.Name);
			return var;
		}
	}

	public virtual void attribute(attribute ast) {
		if (ast.arguments != null)
			attribute_arguments(ast.arguments);
		type(ast.name);
	}
	public virtual void attribute_arguments(attribute_arguments ast) {
		foreach (named_argument x in ast.namedargs)
			named_argument(x);
	}
	public virtual void attribute_section(attribute_section ast) {
		foreach (attribute x in ast.attributes)
			attribute(x);
	}
	public virtual void attribute_sections(attribute_sectionList attributes) {
		foreach (attribute_section x in attributes)
			attribute_section(x);
	}
	public virtual void binary_declarator(binary_declarator ast, TypeBuilder t) {
	}
	public virtual void class_declaration(class_declaration ast) {
		attribute_sections(ast.attrs);
		declarations(ast.sym, ast.body, ast.builder);
	}
	public virtual void compilation(compilation ast) {
		T = ast.global.Types;
		foreach (compilation_unit x in ast.inputs)
			compilation_unit(x);
	}
	public virtual void compilation_unit(compilation_unit ast) {
		attribute_sections(ast.attributes);
		foreach (declaration x in ast.declarations)
			declaration(x);
	}
	public virtual void constant_declaration(constant_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
	}
	public virtual void constructor_declaration(constructor_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		ConstructorBuilder m = ast.builder;
		if (ast.block != null || ast.decl.init != null) {
			declarationList body;
			if (ast.parent is class_declaration)
				body = ((class_declaration)ast.parent).body;
			else
				body = ((struct_declaration)ast.parent).body;			
			ILState g = new ILState(m.GetILGenerator(), this);
			if (ast.decl.init != null)
				constructor_initializer(ast.decl.init, g, body);
			if (ast.sym.IsStatic)
				foreach (declaration d in body)
					if (d is field_declaration)
						field_declaration((field_declaration)d, g, true);
			if (ast.block != null)
				g.statement(ast.block, ast.sym);
			else
				g.Emit(OpCodes.Ret);
		}
	}
	public virtual void constructor_initializer(constructor_initializer ast, ILState g, declarationList body) {
		if (ast is base_initializer) {
			foreach (declaration d in body)
				if (d is field_declaration)
					field_declaration((field_declaration)d, g, false);
			g.base_initializer((base_initializer)ast);
		} else if (ast is this_initializer) g.this_initializer((this_initializer)ast);
		else throw new ArgumentException();
	}
	public virtual void declaration(declaration ast, TypeBuilder t) {
		     if (ast is class_declaration) class_declaration((class_declaration)ast);
		else if (ast is constant_declaration) constant_declaration((constant_declaration)ast, t);
		else if (ast is constructor_declaration) constructor_declaration((constructor_declaration)ast, t);
		else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast);
		else if (ast is destructor_declaration) destructor_declaration((destructor_declaration)ast, t);
		else if (ast is enum_declaration) enum_declaration((enum_declaration)ast);
		else if (ast is event_declaration1) event_declaration1((event_declaration1)ast, t);
		else if (ast is event_declaration2) event_declaration2((event_declaration2)ast, t);
		else if (ast is field_declaration) return;
		else if (ast is indexer_declaration) indexer_declaration((indexer_declaration)ast, t);
		else if (ast is interface_declaration) interface_declaration((interface_declaration)ast);
		else if (ast is interface_event_declaration) interface_event_declaration((interface_event_declaration)ast, t);
		else if (ast is interface_indexer_declaration) interface_indexer_declaration((interface_indexer_declaration)ast, t);
		else if (ast is interface_method_declaration) interface_method_declaration((interface_method_declaration)ast, t);
		else if (ast is interface_property_declaration) interface_property_declaration((interface_property_declaration)ast, t);
		else if (ast is method_declaration) method_declaration((method_declaration)ast, t);
		else if (ast is operator_declaration) operator_declaration((operator_declaration)ast, t);
		else if (ast is property_declaration) property_declaration((property_declaration)ast, t);
		else if (ast is struct_declaration) struct_declaration((struct_declaration)ast);
		else throw new ArgumentException();
	}
	public virtual void declaration(declaration ast) {
		     if (ast is class_declaration) class_declaration((class_declaration)ast);
		else if (ast is delegate_declaration) delegate_declaration((delegate_declaration)ast);
		else if (ast is enum_declaration) enum_declaration((enum_declaration)ast);
		else if (ast is interface_declaration) interface_declaration((interface_declaration)ast);
		else if (ast is namespace_declaration) namespace_declaration((namespace_declaration)ast);
		else if (ast is struct_declaration) struct_declaration((struct_declaration)ast);
		else throw new ArgumentException();
	}
	public virtual void declarations(Type ty, declarationList decls, TypeBuilder t) {
		foreach (declaration x in decls)
			declaration(x, t);
		if (ty.enclosingType == null)
			map[ty] = t.CreateType();
		foreach (declaration x in decls)
			if (x is type_declaration) {
				type_declaration d = (type_declaration)x;
				map[d.typ] = d.builder.CreateType();
			}			
	}
	public virtual void delegate_declaration(delegate_declaration ast) {
		attribute_sections(ast.attrs);
		TypeBuilder t = ast.builder;
		foreach (Symbol s in ast.sym)
			if (s is Constructor) {
				ConstructorBuilder m = (ConstructorBuilder)this[(Constructor)s];
				m.SetImplementationFlags(MethodImplAttributes.Runtime);
			} else if (s is Method) {
				MethodBuilder m = (MethodBuilder)this[(Method)s];
				m.SetImplementationFlags(MethodImplAttributes.Runtime);
				m.CreateMethodBody(new Byte[]{}, 0);
			}
		if (ast.sym.enclosingType == null)
			map[ast.sym] = t.CreateType();
	}
	public virtual void destructor_declaration(destructor_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		if (ast.block != null)
			EmitMethodBody(ast.sym, ast.block, ast.builder);
	}
	public virtual void EmitMethodBody(Method m, statement body, MethodBuilder mb) {
		EmitMethodBody(m, body, new ILState(mb.GetILGenerator(), this));
	}
	public virtual void EmitMethodBody(Method m, statement body, ILState g) {
		g.statement(body, m);
	}
	public virtual void enum_declaration(enum_declaration ast) {
		attribute_sections(ast.attrs);
	}
	public virtual void event_declaration1(event_declaration1 ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		foreach (event_declarator x in ast.decls) {
			ILState g = new ILState(x.add_builder.GetILGenerator(), this);
			g.EmitDefaultAccessor(x.sym, x.sym.Add);
			g = new ILState(x.remove_builder.GetILGenerator(), this);
			g.EmitDefaultAccessor(x.sym, x.sym.Remove);
			x.event_builder.SetAddOnMethod(x.add_builder);
			x.event_builder.SetRemoveOnMethod(x.remove_builder);
		}
	}
	public virtual void event_declaration2(event_declaration2 ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		EventBuilder e = ast.builder;
		foreach (event_accessor x in ast.accessors) {
			attribute_sections(x.attrs);
			MethodBuilder m = x.builder;
			EmitMethodBody(x.sym, x.block, m);
			if (x.id.str == "add")
				e.SetAddOnMethod(m);
			else
				e.SetRemoveOnMethod(m);
		}
	}
	public virtual void explicit_declarator(explicit_declarator ast, TypeBuilder t) {
	}
	public virtual void field_declaration(field_declaration ast, ILState g, bool doStatic) {
		attribute_sections(ast.attrs);
		foreach (field_declarator x in ast.decls)
			if (x.init != null)
				if (doStatic && x.sym.IsStatic) {
					g.variable_initializer(x.init);
					g.Emit(OpCodes.Stsfld, x.sym);
				} else if (!doStatic && !x.sym.IsStatic) {
					g.this_access();
					g.variable_initializer(x.init);
					g.Emit(OpCodes.Stfld, x.sym);
				}
	}
	public virtual void implicit_declarator(implicit_declarator ast, TypeBuilder t) {
	}
	public virtual void indexer_declaration(indexer_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		PropertyBuilder p = ast.builder;
		foreach (accessor_declaration x in ast.accessors) {
			MethodBuilder m = x.builder;
			if (x.body != null)
				EmitMethodBody(x.sym, x.body, m);
			if (x.id.str == "get")
				p.SetGetMethod(m);
			else
				p.SetSetMethod(m);
		}
	}
	public virtual void interface_declaration(interface_declaration ast) {
		attribute_sections(ast.attrs);
		declarations(ast.sym, ast.body, ast.builder);
	}
	public virtual void interface_event_declaration(interface_event_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
	}
	public virtual void interface_indexer_declaration(interface_indexer_declaration ast, TypeBuilder t) {
		msg.Error("Interface indexers not yet implemented");
	}
	public virtual void interface_method_declaration(interface_method_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
	}
	public virtual void interface_property_declaration(interface_property_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		foreach (accessor_declaration x in ast.accessors)
			attribute_sections(x.attrs);
	}
	public virtual void method_declaration(method_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		if (ast.body != null)
			EmitMethodBody(ast.sym, ast.body, ast.builder);
		if (ast.sym.Name == "Main" && ast.sym.IsStatic && ast.sym.IsPublic)
			((AssemblyBuilder)t.Assembly).SetEntryPoint(ast.builder, PEFileKinds.ConsoleApplication);
	}
	public virtual void named_argument(named_argument ast) {
		//expression(ast.expr, null);
		// InputElement ast.id
	}
	public virtual void namespace_declaration(namespace_declaration ast) {
		foreach (declaration x in ast.nb.declarations)
			declaration(x);
	}
	public virtual void operator_declaration(operator_declaration ast, TypeBuilder t) {
		msg.Error("Operator declarations not yet implemented");
	}
	public virtual void operator_declarator(operator_declarator ast, TypeBuilder t) {
		     if (ast is binary_declarator) binary_declarator((binary_declarator)ast, t);
		else if (ast is explicit_declarator) explicit_declarator((explicit_declarator)ast, t);
		else if (ast is implicit_declarator) implicit_declarator((implicit_declarator)ast, t);
		else if (ast is unary_declarator) unary_declarator((unary_declarator)ast, t);
		else throw new ArgumentException();
	}
	public virtual void property_declaration(property_declaration ast, TypeBuilder t) {
		attribute_sections(ast.attrs);
		PropertyBuilder p = ast.builder;
		foreach (accessor_declaration x in ast.decls) {
			attribute_sections(x.attrs);
			MethodBuilder m = x.builder;
			if (x.body != null)
				EmitMethodBody(x.sym, x.body, m);
			if (x.id.str == "get")
				p.SetGetMethod(m);
			else
				p.SetSetMethod(m);
		}
	}
	public virtual void struct_declaration(struct_declaration ast) {
		attribute_sections(ast.attrs);
		declarations(ast.sym, ast.body, ast.builder);
	}
	public virtual void unary_declarator(unary_declarator ast, TypeBuilder t) {
	}
}
